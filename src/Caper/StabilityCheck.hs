module Caper.StabilityCheck where

import Control.Monad.IO.Class
import Control.Monad.Reader
import Control.Monad.State
import Control.Lens

import Caper.Regions
import Caper.Assertions
import Caper.Parser.AST.Annotation
import Caper.ProverDatatypes
import Caper.Prover
import Caper.Logger
import Caper.Exceptions
import Caper.RegionTypes
import Caper.Utils.Choice
import Caper.SymbolicState

checkStability :: (MonadIO m, MonadLogger m,
        MonadReader r m, Provers r, RTCGetter r,
        MonadRaise m) => 
        Assrt -> m Bool
checkStability a = do
        r <- firstChoice $ flip evalStateT emptySymbState $ do
                produceAssrt True a
                liftIO $ putStrLn "=== pre stab ==="
                printSymbState
                liftIO $ putStrLn "================"
                stabiliseRegions
                liftIO $ putStrLn "=== post stab ==="
                printSymbState
                liftIO $ putStrLn "================"
                logicalVars .= emptyLVars
                wrapStateT (fmap emptyAssertions) (fmap admitAssertions) $ do
                        consumeAssrt a
                        printSymbState
                        justCheck
                return True
        case r of
                Just True -> return True
                _ -> return False

