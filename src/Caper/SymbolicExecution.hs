{-# LANGUAGE MultiParamTypeClasses, FlexibleInstances, ScopedTypeVariables #-}
module Caper.SymbolicExecution where

import Control.Monad.Trans
import Control.Monad.Reader
import Control.Monad.State
import Data.Maybe
import qualified Data.Map as Map
import Control.Lens hiding (pre)
import qualified Data.Set as Set

import Caper.Utils.Alternating
import Caper.Utils.NondetClasses
import qualified Caper.Utils.AliasingMap as AM

import Caper.Constants
import Caper.ProverDatatypes
import Caper.Exceptions
import Caper.Logger
import Caper.Parser.AST hiding (Region)
import Caper.Procedures
import Caper.Predicates
import Caper.RegionTypes
import Caper.Regions
import Caper.SymbolicState
import Caper.Prover
import Caper.ProverStates
import Caper.Assertions.Produce
import Caper.Assertions.Consume

{-
    Symbolic execution.
-}

class (MonadRaise m, MonadIO m, MonadLogger m,
        MonadReader r m, Provers r, RTCGetter r, SpecificationContext r,
        MonadPlus m, MonadState s m, SymbStateLenses s, AssumptionLenses s, DebugState s,
        RegionLenses s, MonadDemonic m) => SymExMonad r s m

instance (MonadRaise m, MonadIO m, MonadLogger m,
        MonadReader r m, Provers r, RTCGetter r, SpecificationContext r,
        MonadPlus m, MonadState s m, SymbStateLenses s, AssumptionLenses s, DebugState s,
        RegionLenses s, MonadDemonic m) => SymExMonad r s m


writtenLocals :: Stmt -> Set.Set String
writtenLocals = flip wl Set.empty
    where
        wl (SeqStmt _ stmts) s = foldr wl s stmts
        wl (IfElseStmt _ _ st1 st2) s = (wl st1 >> wl st2) s
        wl (WhileStmt _ _ _ st) s = wl st s
        wl (DoWhileStmt _ _ st _) s = wl st s
        wl (LocalAssignStmt _ t _) s = Set.insert t s
        wl (DerefStmt _ t _) s = Set.insert t s
        wl (CallStmt _ (Just t) _ _) s = Set.insert t s
        wl _ s = s 

localiseLogicalVars :: (MonadState s m, SymbStateLenses s) =>
        m a -> m a
localiseLogicalVars mop = do
            -- 'push' the logical variables
            savedLVars <- use logicalVars
            logicalVars .= emptyLVars
            a <- mop -- Do what we have to do
            -- 'pop' the logical variables
            logicalVars .= savedLVars
            return a
        
-- |Check if the state is consistent; if not then do not execute the continuation.
whenConsistent :: SymExMonad r s m => m () -> m ()
whenConsistent xx = do
            c <- isConsistent
            unless (c == Just False) xx

-- | Symbolically execute some code with the specified region open.
-- Afterwards, the region should be closed and the state updated.
-- The specified region should be in the domain of the map and have a region type.
-- The region should also have been stabilised (BEFORE ANY REGIONS HAVE BEEN OPENED!)
atomicOpenRegion ::
        SymExMonad r s m =>
        -- |Region identifier 
        VariableID ->
        -- |Operation for performing symbolic execution (parametrised by continuation) 
        (m () -> m ()) ->
        -- |Continuation
        m () ->
          m ()
atomicOpenRegion rid ase cont = do
        -- Resolve the region
        regs <- use regions
        (rs, rg, rt, ps :: [Expr VariableID]) <- case AM.lookup rid regs of
            Nothing -> error $ "atomicOpenRegion: Unable to resolve region identifier '" ++ show rid ++ "'"
            Just (Region {regDirty = True}) -> error $ "atomicOpenRegion: Cannot open dirty region '" ++ show rid ++ "'"
            Just (Region {regTypeInstance = Nothing}) -> error $ "atomicOpenRegion: Region '" ++ show rid ++ "' is of unknown type"
            Just (Region {regTypeInstance = Just (RegionInstance rti ps), regState = rs0, regGuards = rg}) -> do
                    rt <- lookupRType rti
                    rs <- case rs0 of
                        Nothing -> liftM var $ newAvar (show rid ++ "state")
                        Just rs -> return rs
                    return (rs, rg, rt, var rid : ps)
        -- Create a logical state holding the region parameters
        -- It might be worth checking that the expressions have the
        -- appropriate types, but for now I won't.  Hopefully this
        -- should've been checked already.
        plstate <- foldM (\m (pe, (RTDVar parnam, t)) -> do
                         ev <- letAvar parnam pe
                         return (Map.insert parnam ev m)) emptyLVars (zip ps (rtParameters rt)) 
        -- For each region interpretation...
        dAll $ flip map (rtInterpretation rt) $ \interp -> 
            do
                liftIO $ putStrLn $ "*** Trying interp " ++ show interp  
                savedLVars <- use logicalVars
                logicalVars .= plstate
                -- ...assume we are in that state
                st0 <- produceValueExpr (siState interp)
                assumeTrueE $ VAEq st0 rs
                --use theAssumptions >>= (liftIO . print)
                --use logicalVars >>= (liftIO . print)
                forM_ (siConditions interp) producePure
                -- and produce the resources
                produceAssrt False (siInterp interp)
                -- If it's inconsistent then we've nothing to prove here
                whenConsistent $ do
                    oldRegions <- use openRegions
                    openRegions %= (rid:)
                    logicalVars .= savedLVars
                    -- Execute the atomic thing
                    ase $ do
                        savedLVars' <- use logicalVars
                        logicalVars .= plstate -- The parameters don't change
                        -- Non-deterministically choose the next interpretation
                        interp' <- msum $ map return (rtInterpretation rt)
                        liftIO $ putStrLn $ "*** Closing with interp " ++ show interp'
                        debugState
                        check $ do
                            -- Assert that we are in this interpretation
                            st1 <- consumeValueExpr (siState interp')
                            forM_ (siConditions interp') consumePure
                            consumeAssrt (siInterp interp')
                            justCheck -- This isn't needed, but may result in failing faster
                            -- and that the state is guarantee related
                            guardCond <- generateGuaranteeCondition rt ps rg st0 st1
                            assertTrue guardCond
                            regions . ix rid %= (\r -> r {regState = Just st1, regDirty = True})
                        liftIO $ putStrLn $ "*** Closed with interp " ++ show interp'
                        logicalVars .= savedLVars'
                        openRegions .= oldRegions
                        cont

availableRegions :: (SymExMonad r s m) => m [VariableID]
availableRegions = do
            oregs <- use openRegions
            regs <- use regions
            let r0 = AM.distinctKeys regs
            let r1 = [r | r <- r0, isJust $ AM.lookup r regs >>= regTypeInstance]
            filterM (liftM and . forM oregs . cannotAliasStrong) r1
            

-- |Symbolically execute an atomic operation, trying opening
-- regions.        
atomicSymEx :: (SymExMonad r s m) =>
-- |Atomic operation (parametrised by continuation
    (m () -> m ()) ->
-- |Continuation
    m ()
     -> m ()
atomicSymEx ase cont = (ase cont) `mplus` do
            ars <- availableRegions
            msum [ atomicOpenRegion r (atomicSymEx ase) cont | r <- ars] 


data ExitMode = EMReturn (Maybe (ValueExpression VariableID)) | EMContinuation

updateContinuation :: (Monad m) => (ExitMode -> m a) -> m a -> (ExitMode -> m a)
updateContinuation cont newc EMContinuation = newc
updateContinuation cont newc r = cont r


symbolicExecute :: forall r s m.
    SymExMonad r s m =>
            Stmt -> (ExitMode -> m ()) -> m ()
symbolicExecute stmt cont = do
            -- If we reach an inconsistent state then we can stop
            consistent <- isConsistent
            unless (consistent == Just False) $ do
                stabiliseRegions
                debugState
                liftIO $ putStrLn $ ">>> " ++ take 30 (show stmt)
                se stmt
    where
        ses [] = cont EMContinuation
        ses (s:ss) = symbolicExecute s (updateContinuation cont (ses ss))
        se :: Stmt -> m ()
        -- se symbolically executes a statement; in the end, we should always call cont.
        se (SeqStmt _ ss) = ses ss
        se (IfElseStmt sp cond sthen selse) = do
                bc <- bexprToValueCondition cond
                (do -- then branch
                        assumeTrueE bc
                        se sthen) <#>
                    (do -- else branch
                        assumeFalseE bc
                        se selse)
        se (WhileStmt sp minv cond body) = symExLoop sp minv cond body
        se (DoWhileStmt sp minv body cond) = symbolicExecute body (updateContinuation cont (symExLoop sp minv cond body)) 
        se (LocalAssignStmt _ trgt src) = symExLocalAssign trgt src >> cont EMContinuation
        se (DerefStmt _ trgt src) = atomicSymEx (symExRead trgt src >>) (cont EMContinuation)
        se (AssignStmt _ trgt src) = atomicSymEx (symExWrite trgt src >>) (cont EMContinuation)
        se smt@(CallStmt sp rvar "CAS" args) = contextualise (DescriptiveContext sp "In a CAS") $
                case args of
                    [target, oldv, newv] -> atomicSymEx (\c -> symExCAS rvar target oldv newv >> whenConsistent c)
                                                (cont EMContinuation)
                    _ -> raise $ ArgumentCountMismatch 3 (length args)
        se smt@(CallStmt sp rvar "alloc" args) = contextualise (DescriptiveContext sp "In an alloc") $ do
                case args of
                    [l] -> symExAllocate rvar l >> cont EMContinuation
                    _ -> raise $ ArgumentCountMismatch 1 (length args)
        se smt@(CallStmt sp rvar pname args) = do
                        spec <- view (specifications . at pname)
                        contextualise (DescriptiveContext sp ("In a call to function '" ++ pname ++ "'")) $ case spec of
                            Nothing -> raise $ UndeclaredFunctionCall pname
                            Just (Specification params sprec spost) -> do
                                -- Check that there are the right number of arguments
                                unless (length params == length args) $
                                        raise $ ArgumentCountMismatch (length params) (length args)
                                -- 'push' the logical variables
                                savedLVars <- use logicalVars
                                logicalVars .= emptyLVars
                                -- Initialise logical variables for the arguments
                                forM_ (zip params args) $ \(param, arg) -> do
                                        paramVar <- newAvar param
                                        argVExpr <- aexprToVExpr arg
                                        -- XXX: Possibly shift this to a more delicate variableForVExpr (or such)
                                        --liftIO $ putStrLn $ (show paramVar) ++ " ==== " ++ show argVExpr 
                                        assumeTrue $ VAEq (var paramVar) argVExpr
                                        logicalVars . at param ?= paramVar
                                -- Consume the precondition
                                -- TODO: Eventually it might be good to be lazier about stabilising regions
                                when stabiliseBeforeConsumePrecondition $
                                    stabiliseRegions
                                liftIO $ putStrLn $ "Consuming precondition: " ++ show sprec
                                debugState
                                contextualise "Consuming precondition" $
                                        check $ consumeAssrt sprec
                                -- Need to stabilise the frame!!!!!!!!
                                stabiliseRegions 
                                -- Set up variable for the return result
                                retVar <- case rvar of
                                    Nothing -> newAvar returnVariableName
                                    Just retv -> do
                                        retVar <- newAvar retv
                                        progVars . at retv ?= var retVar
                                        return retVar                                        
                                logicalVars . at returnVariableName ?= retVar
                                contextualise "Producing postcondition" $
                                        produceAssrt stabiliseAfterProducePostcondition spost
                                liftIO $ putStrLn $ "Produced postcondition: " ++ show spost
                                debugState
                                -- 'pop' the logical variables
                                logicalVars .= savedLVars
                                -- continue
                                cont EMContinuation
        se (ReturnStmt _ (Just rexp)) = do
                        rtn <- aexprToVExpr rexp
                        cont $ EMReturn (Just rtn)
        se (ReturnStmt _ Nothing) = cont $ EMReturn Nothing
        se (SkipStmt _) = cont EMContinuation
        se (ForkStmt _ pname args) = undefined
        se (AssertStmt _ assrt) = undefined
        symExLoop sp minv cond body = do
                -- use True as a default invariant
                let inv = fromMaybe (AssrtPure sp $ ConstBAssrt sp True)
                let wrlvs = writtenLocals body
                undefined

checkProcedure ::
    (MonadRaise m, MonadIO m, MonadLogger m,
        MonadReader r m, Provers r, RTCGetter r, SpecificationContext r) =>
        FunctionDeclr -> m Bool
checkProcedure fd@(FunctionDeclr sp n opre opost args s) =
        contextualise fd $ contextualise ("Checking procedure '" ++ n ++ "'") $ do
            verRes <- runAlternatingT $ flip evalStateT (emptySymbStateWithVars args) $ do
                -- Produce the precondition
                logEvent $ InfoEvent $ "Producing precondition: " ++ show pre
                contextualise "Producing precondition" $ produceAssrt
                    stabiliseAfterProducePrecondition
                    pre
                debugState
                symbolicExecute s postcheck
            case verRes of
                Nothing -> return False 
                Just _ -> return True
                
    where
        pre = fromMaybe (defaultPrecondition sp) opre
        post = fromMaybe (defaultPostcondition sp) opost
        postcheck' res = contextualise ("Consuming postcondition: " ++ show post) $ whenConsistent $ do
                        logEvent $ InfoEvent $ "Consuming postcondition: " ++ show post
                        retVar <- newAvar returnVariableName
                        case res of
                            Just rv -> assumeTrue (VAEq (var retVar) rv)
                            _ -> return ()
                        logicalVars %= Map.insert returnVariableName retVar
                        when stabiliseBeforeConsumePostcondition stabiliseRegions
                        debugState
                        check $ consumeAssrt post
                        logEvent $ InfoEvent $ "Postcondition consumed."
        postcheck EMContinuation = postcheck' Nothing
        postcheck (EMReturn ret) = postcheck' ret 
            
verifyProcedure ::
    (MonadRaise m, MonadIO m, MonadLogger m,
        MonadReader r m, Provers r, RTCGetter r, SpecificationContext r) =>
        FunctionDeclr -> m ()        
verifyProcedure fd = do
        res <- checkProcedure fd
        unless res $ contextualise fd $ contextualise ("Verifying procedure") $
            raise $ VerificationFailed (show fd) 

verifyProcedures ::
    (MonadRaise m, MonadIO m, MonadLogger m,
        MonadReader r m, Provers r, RTCGetter r, SpecificationContext r) =>
        [FunctionDeclr] -> m ()
verifyProcedures = mapM_ verifyProcedure
