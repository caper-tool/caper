{-# LANGUAGE MultiParamTypeClasses, FlexibleInstances, FlexibleContexts, ScopedTypeVariables #-}
module Caper.SymbolicExecution where

import Control.Monad.Trans
import Control.Monad.Reader hiding (forM_)
import Control.Monad.State hiding (forM_)
import Data.Maybe
import qualified Data.Map as Map
import Control.Lens hiding (pre)
import qualified Data.Set as Set
import Data.Foldable (forM_, toList, Foldable)

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
import Caper.DeductionFailure

{-
    Symbolic execution.
-}

class (MonadRaise m, MonadIO m, MonadLogger m,
        MonadReader r m, Provers r, RTCGetter r, SpecificationContext r,
        MonadPlus m, MonadOrElse m, Failure DeductionFailure m, OnFailure DeductionFailure m,
        MonadState s m, SymbStateLenses s, AssumptionLenses s, DebugState s r,
        RegionLenses s, MonadDemonic m, DebugState (WithAssertions s) r) => SymExMonad r s m

instance (MonadRaise m, MonadIO m, MonadLogger m,
        MonadReader r m, Provers r, RTCGetter r, SpecificationContext r,
        MonadPlus m, MonadOrElse m, Failure DeductionFailure m, OnFailure DeductionFailure m,
        MonadState SymbState m, MonadDemonic m) => SymExMonad r SymbState m


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

-- | Symbolically execute some code with the specified region open.
-- Afterwards, the region should be closed and the state updated.
-- The specified region should be in the domain of the map and have a region type.
-- The region should also have been stabilised (BEFORE ANY REGIONS HAVE BEEN OPENED!)
atomicOpenRegion ::
        SymExMonad r s m =>
        VariableID          -- ^Region identifier
        -> (m () -> m ())   -- ^Operation for performing symbolic execution (parametrised by continuation)
        -> m ()             -- ^Continuation
            -> m ()
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
                            regions . ix rid %= (\r -> r {regState = Just st1, regDirty = True})
                            consumeAssrt (siInterp interp')
                            justCheck -- This isn't needed, but may result in failing faster
                            -- and that the state is guarantee related
                            guardCond <- generateGuaranteeCondition rt ps rg st0 st1
                            assertTrue guardCond
                        liftIO $ putStrLn $ "*** Closed with interp " ++ show interp'
                        logicalVars .= savedLVars'
                        openRegions .= oldRegions
                        debugState
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
    (m () -> m ())  -- ^Atomic operation (parametrised by continuation 
    -> m ()         -- ^Continuation
     -> m ()
atomicSymEx ase cont = ase cont `mplus` do
            ars <- availableRegions
            msum [ atomicOpenRegion r (atomicSymEx ase) cont | r <- ars] 

createRegionWithParams :: (SymExMonad r s m) =>
    RTId
    -- ^ Type of the region to create
    -> [Expr VariableID]
    -- ^ Parameters of the region excluding the region identifier
    -- -- variables not in the current context with be existentially quantified
    -> ValueExpression VariableID
    -- ^ State of the region -- variables not in the current context with be existentially quantified
    -> m ()
createRegionWithParams rtid params st = do
        rt <- lookupRType rtid
        oldRegions <- use openRegions
        savedLVars <- use logicalVars
        interp' <- check $ do
            let vars = Set.unions (toSet st : map toSet params)
            bvars <- use boundVars
            forM_ (vars `Set.difference` bvars) $ \v ->
                declareEvar v
            rid <- newEvar "region"
            -- Create a logical state holding the region parameters
            let (RTDVar ridparam, VTRegionID) = head (rtParameters rt)
            bindVarAs rid VTRegionID
            let plstate0 = Map.insert ridparam rid emptyLVars
            plstate <- foldM (\m (pe, (RTDVar parnam, t)) -> do
                             ev <- letEvar parnam pe
                             bindVarAs ev t
                             return (Map.insert parnam ev m))
                        plstate0 (zip params (tail $ rtParameters rt))
            openRegions %= (rid:)
            logicalVars .= plstate
            -- Non-deterministically choose the next interpretation
            interp' <- msum $ map return (rtInterpretation rt)
            liftIO $ putStrLn $ "*** Constructing with interp " ++ show interp'
            -- Assert that we are in this interpretation
            st1 <- consumeValueExpr (siState interp')
            forM_ (siConditions interp') consumePure
            regions %= AM.insert rid Region {
                regDirty = True,
                regTypeInstance = (Just (RegionInstance rtid params)),
                regState = (Just st1),
                regGuards = rtFullGuard rt}
            consumeAssrt (siInterp interp')
            return interp'
        liftIO $ putStrLn $ "*** Constructed with interp " ++ show interp'
        logicalVars .= savedLVars
        openRegions .= oldRegions
    where
        toSet :: (Foldable f, Ord v) => f v -> Set.Set v
        toSet = Set.fromList . toList

missingRegionHandler :: (SymExMonad r s m) => m ()
missingRegionHandler = --retry (liftIO $ putStrLn "registered missing region handler") handler >> retry (return ()) handler
        (liftIO $ putStrLn "registered missing region handler") >> multiRetry regionConstructionLimit handler
    where
        handler (MissingRegionByType rtid params st s) = Just $ do
                liftIO $ putStrLn "invoked missing region handler"
                debugState
                createRegionWithParams rtid params st
                liftIO $ putStrLn "created region"
                debugState
        handler _ = Nothing

data ExitMode = EMReturn (Maybe (ValueExpression VariableID)) | EMContinuation

updateContinuation :: (Monad m) => (ExitMode -> m a) -> m a -> (ExitMode -> m a)
updateContinuation cont newc EMContinuation = newc
updateContinuation cont newc r = cont r

variableForVExpr :: (MonadState s m, AssumptionLenses s) => String -> ValueExpression VariableID -> m VariableID
-- ^Convert a value expression to a variable.  This takes a string to use as the basis
-- of the variable name.  If the expression is already a variable, it won't introduce
-- an additional variable.  Otherwise, it creates a new assumption variable and assumes
-- that it is equal to the supplied 'ValueExpression'.  Note that all variables in the
-- expression must be assumption variables.
variableForVExpr _ (VEVar v) = return v
variableForVExpr vn ve = do
                vr <- newAvar vn
                assumeTrue $ VAEq (var vr) ve
                return vr
                

programVarsToLogicalVars :: SymExMonad r s m => m LVarBindings
-- ^Modify the logical variables to include the current values of program variables.
-- Returns the old bindings (so these can be restored following produce/consume).
programVarsToLogicalVars = do
            oldLVars <- use logicalVars
            pvars <- use progVars
            iforM_ pvars $ \pv pvval -> case oldLVars ^. at pv of
                    Nothing -> variableForVExpr pv pvval >>= (logicalVars . at pv ?=) 
                    Just lv -> if var lv == pvval then return () else do
                            logEvent $ WarnAmbiguousVariable programVariableSupersedesLogicalVariable pv
                            when programVariableSupersedesLogicalVariable
                                (variableForVExpr pv pvval >>= (logicalVars . at pv ?=))
            return oldLVars                    

symbolicExecute :: forall r s m.
    SymExMonad r s m =>
            Stmt -> (ExitMode -> m ()) -> m ()
symbolicExecute stmt cont = do
            -- If we reach an inconsistent state then we can stop
            whenConsistent $ do
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
                                        paramVar <- aexprToVExpr arg >>= variableForVExpr param
                                        logicalVars . at param ?= paramVar
                                missingRegionHandler
                                -- Consume the precondition
                                -- TODO: Eventually it might be good to be lazier about stabilising regions
                                when stabiliseBeforeConsumePrecondition
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
        se (ForkStmt sp pname args) = do
                        spec <- view (specifications . at pname)
                        contextualise (DescriptiveContext sp ("In a fork of function '" ++ pname ++ "'")) $ case spec of
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
                                        paramVar <- aexprToVExpr arg >>= variableForVExpr param
                                        logicalVars . at param ?= paramVar
                                missingRegionHandler
                                -- Consume the precondition
                                -- TODO: Eventually it might be good to be lazier about stabilising regions
                                when stabiliseBeforeConsumePrecondition
                                    stabiliseRegions
                                liftIO $ putStrLn $ "Consuming precondition: " ++ show sprec
                                debugState
                                contextualise "Consuming precondition" $
                                        check $ consumeAssrt sprec
                                -- Stabilise what remains
                                stabiliseRegions 
                                -- 'pop' the logical variables
                                logicalVars .= savedLVars
                                -- continue
                                cont EMContinuation
        se (AssertStmt sp assrt) = contextualise (DescriptiveContext sp ("In assertion: " ++ show assrt)) $ do
                liftIO $ putStrLn $ "assert " ++ show assrt
                debugState
                savedLVars <- programVarsToLogicalVars
                when stabiliseBeforeConsumeInvariant stabiliseRegions
                missingRegionHandler
                contextualise "Consuming assertion" $
                    check $ consumeAssrt assrt
                logicalVars .= savedLVars
                savedLVars' <- programVarsToLogicalVars
                contextualise "Producing assertion" $
                    produceAssrt stabiliseAfterProduceInvariant assrt
                logicalVars .= savedLVars'
                debugState
                cont EMContinuation
        symExLoop sp minv cond body = do
                -- use True as a default invariant
                let inv = fromMaybe (AssrtPure sp $ ConstBAssrt sp True) minv
                let wrlvs = writtenLocals body
                let produceInv = do
                        savedLVars <- programVarsToLogicalVars
                        contextualise "Producing invariant" $
                            produceAssrt stabiliseAfterProduceInvariant inv
                        liftIO $ putStrLn $ "Produced invariant: " ++ show inv
                        debugState
                        logicalVars .= savedLVars
                let consumeInv = do
                        savedLVars <- programVarsToLogicalVars
                        when stabiliseBeforeConsumeInvariant stabiliseRegions
                        liftIO $ putStrLn $ "Consuming invariant: " ++ show inv
                        missingRegionHandler
                        debugState
                        contextualise "Consuming invariant" $
                            check $ consumeAssrt inv
                        logicalVars .= savedLVars
                -- consume invariant (using program variables as logical variables)
                consumeInv
                -- stabilise
                stabiliseRegions
                -- havoc the local variables in wrlvs
                forM_ wrlvs $ \lv -> do
                    lvv <- newAvar lv
                    progVars . at lv ?= var lvv
                (do
                        liftIO $ putStrLn $ "*** exiting loop"
                        -- produce the invariant (program variables)
                        produceInv
                        -- assume negative loop test
                        bc <- bexprToValueCondition cond
                        assumeFalseE bc
                        -- continue
                        cont EMContinuation) <#>
                    (do
                        liftIO $ putStrLn $ "*** executing loop body"
                        -- store the heap and regions for future use, abandoning them
                        restoreFrame <- frame
                        -- produce the invariant (program variables)
                        produceInv
                        -- assume positive loop test
                        bc <- bexprToValueCondition cond
                        assumeTrueE bc
                        let
                            cont' (EMReturn r) = do
                                    -- restore frame
                                    restoreFrame
                                    -- pass to return continuation
                                    cont (EMReturn r)
                            cont' (EMContinuation) =
                                    -- consume the invariant
                                    consumeInv
                        symbolicExecute body cont')


checkProcedure ::
    (MonadRaise m, MonadIO m, MonadLogger m,
        MonadReader r m, Provers r, RTCGetter r, SpecificationContext r) =>
        FunctionDeclr -> m Bool
checkProcedure fd@(FunctionDeclr sp n opre opost args s) =
        contextualise fd $ contextualise ("Checking procedure '" ++ n ++ "'") $ do
            verRes <- runAlternatingTD $ flip evalStateT (emptySymbStateWithVars args) $ do
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
                        missingRegionHandler
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
