module Caper.SymbolicExecution where

import Control.Monad.Trans
import Control.Monad.Reader
import Control.Monad.State
import Data.Maybe
import qualified Data.Map as Map
import Control.Lens hiding (pre)

import Caper.Utils.Choice

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

symbolicExecute ::
    (MonadRaise m, MonadIO m, MonadLogger m,
        MonadReader r m, Provers r, RTCGetter r,
        MonadPlus m, MonadState s m, SymbStateLenses s) =>
            Stmt -> m ()
symbolicExecute stmt = do
            consistent <- isConsistent
            when consistent $ do
                stabiliseRegions

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
                preConsistent <- isConsistent
                
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
