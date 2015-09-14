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

{- |Record the current state; execute the first computation; revert to the saved state;
    execute the second computation.  
-} 
branch :: (MonadState s m, MonadCut m) => m a -> m b -> m (a, b)
branch b1 b2 = do
                s <- get
                r1 <- b1
                put s
                cut_
                r2 <- b2
                put $ error "State is invalid after a branch"
                return (r1, r2)

{- |Like 'branch', but throws away the results of the computations.
-}
branch_ :: (MonadState s m, MonadCut m) => m a -> m b -> m ()
branch_ b1 b2 = branch b1 b2 >> return ()



data ExitMode = EMReturn (Maybe ValExpr) | EMContinuation

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
