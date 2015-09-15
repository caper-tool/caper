module Caper.SymbolicExecution where

import Control.Monad.Trans
import Control.Monad.Reader
import Control.Monad.State
import Data.Maybe
import qualified Data.Map as Map
import Control.Lens hiding (pre)

import Caper.Utils.Choice
import Caper.Utils.NondetClasses

import Caper.ProverDatatypes
import Caper.Exceptions
import Caper.Logger
import Caper.Parser.AST
import Caper.Procedures
import Caper.RegionTypes
import Caper.Regions
import Caper.SymbolicState
import Caper.Prover
import Caper.Assertions.Produce
import Caper.Assertions.Consume

{-
    Symbolic execution.
-}

-- TODO: this should handle regions
atomicSymEx :: m () -> m ()
atomicSymEx ase = ase


data ExitMode = EMReturn (Maybe (ValueExpression VariableID)) | EMContinuation

updateContinuation :: (Monad m) => (ExitMode -> m ()) -> m () -> (ExitMode -> m ())
updateContinuation cont newc EMContinuation = newc
updateContinuation cont newc r = cont r

symbolicExecute ::
    (MonadRaise m, MonadIO m, MonadLogger m,
        MonadReader r m, Provers r, RTCGetter r,
        MonadPlus m, MonadState s m, SymbStateLenses s,
        RegionLenses s, MonadCut m) =>
            Stmt -> (ExitMode -> m ()) -> m ()
symbolicExecute stmt cont = do
            -- If we reach an inconsistent state then we can stop
            consistent <- isConsistent
            unless (consistent == Just False) $ do
                stabiliseRegions
                se stmt
    where
        ses [] = cont EMContinuation
        ses (s:ss) = symbolicExecute s (updateContinuation cont (ses ss))
        se (SeqStmt _ ss) = ses ss
        se (IfElseStmt sp cond sthen selse) = do
                bc <- bexprToValueCondition cond
                branch_   
                    (do -- then branch
                        assumeTrueE bc
                        se sthen)
                    (do -- else branch
                        assumeFalseE bc
                        se selse)
        se (WhileStmt _ _ _ _) = undefined
        se (DoWhileStmt _ _ _ _) = undefined
        se (LocalAssignStmt _ trgt src) = symExLocalAssign trgt src 
        se (DerefStmt _ trgt src) = atomicSymEx $ symExRead trgt src
        se (AssignStmt _ trgt src) = atomicSymEx $ symExWrite trgt src
        se (CallStmt _ rvar pname args) = undefined
        se (ReturnStmt _ (Just rexp)) = do
                        re <- aexprToVExpr rexp
                        cont $ EMReturn (Just re)
        se (ReturnStmt _ Nothing) = cont $ EMReturn Nothing
        se (SkipStmt _) = cont EMContinuation
        se (ForkStmt _ pname args) = undefined
        se (AssertStmt _ assrt) = undefined

checkProcedure ::
    (MonadRaise m, MonadIO m, MonadLogger m,
        MonadReader r m, Provers r, RTCGetter r) =>
        FunctionDeclr -> m Bool
checkProcedure fd@(FunctionDeclr sp n opre opost args s) =
        contextualise fd $ contextualise ("Checking procedure '" ++ n ++ "'") $ do
            verRes <- firstChoice $ flip evalStateT (emptySymbStateWithVars args) $ do
                -- Produce the precondition
                -- For now, we won't assume that it is necessarily stable
                -- TODO: make this configurable
                contextualise "Producing precondition" $ produceAssrt
                    True -- Treat regions as dirty
                    pre
                undefined
            case verRes of
                Nothing -> return False 
                Just _ -> return True
                
    where
        pre = fromMaybe (defaultPrecondition sp) opre
        post = fromMaybe (defaultPostcondition sp) opost
            
verifyProcedure ::
    (MonadRaise m, MonadIO m, MonadLogger m,
        MonadReader r m, Provers r, RTCGetter r) =>
        FunctionDeclr -> m ()        
verifyProcedure fd = do
        res <- checkProcedure fd
        unless res $ contextualise fd $ contextualise ("Verifying procedure") $
            raise $ VerificationFailed (show fd) 

checkProcedures ::
    (MonadRaise m, MonadIO m, MonadLogger m,
        MonadReader r m, Provers r, RTCGetter r) =>
        [FunctionDeclr] -> m ()
checkProcedures = mapM_ checkProcedure
