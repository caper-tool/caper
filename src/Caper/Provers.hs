{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE CPP #-}
-- #define z3ffi
module Caper.Provers where
import Data.ConfigFile
import Control.Monad.Error
import Control.Monad.Reader

import Caper.ProverDatatypes
import Caper.PermissionsI
import Caper.PermissionsE
import qualified Caper.ValueProver as VP
#ifdef z3ffi
import qualified Caper.ValueProver2 as VP2
#endif
import Caper.FirstOrder
import Caper.Utils.MemoIO

configDefaults :: MonadError CPError m => m ConfigParser
configDefaults = readstring emptyCP "[Provers]\npermissions = internal\nvalues = z3\n[EProver]\ntimeout=1000\n[InternalProver]\nmode=tree\n[Z3Prover]\ntimeout=1000"

configFile :: (MonadError CPError m, MonadIO m) => m ConfigParser
configFile = do
                def <- configDefaults
                join $ liftIO $ readfile def "config.ini"

proversFromConfig :: (MonadError CPError m, MonadIO m) => m ProverRecord
proversFromConfig = do
                conf <- configFile
                permProver <- get conf "Provers" "permissions"
                (pp0,ppi) <- case permProver of
                        "e" -> do
                                exec <- get conf "EProver" "executable"
                                timeout <- get conf "EProver" "timeout"
                                epp <- liftIO $ makeEPProver exec timeout
                                return (epp . simplify, eproverVersion exec)
                        _ -> do
                                mode <- get conf "InternalProver" "mode"
                                let ipp = if mode == "bigint" then permCheckBigInt else permCheckTree
                                let ipi = if mode == "bigint" then (return "Internal permissions prover, bigint configuration") else (return "Internal permissions prover, tree configuration")
                                return (ipp . simplify . rewriteFOF simplR, ipi)
                pp <- liftIO $ memoIO pp0 -- cache results from the permissions prover
                valProver <- get conf "Provers" "values"
                timeout <- get conf "Z3Prover" "timeout"
                let (vp, vi) = case valProver :: String of
#ifdef z3ffi
                        "z3-ffi" -> (VP2.valueCheck (Just timeout), VP2.valueProverInfo)
#endif
                        _ -> (VP.valueCheck (if timeout <= 0 then Nothing else Just $ (timeout - 1) `div` 1000 + 1), VP.valueProverInfo)
                return $ Provers pp vp ppi vi
                        
initProvers :: IO ProverRecord
initProvers = do
                res <- runErrorT proversFromConfig
                case res of
                        (Left e) -> error $ "Failed parsing configuration file: " ++ show e
                        (Right r) -> return r

runWithProvers :: (MonadIO m) => ReaderT ProverRecord m a -> m a
runWithProvers o = liftIO initProvers >>= runReaderT o

{-
getEZ3Provers :: IO ProverRecord
getEZ3Provers = do
        epp <- makeEPProver
        let z3vp = valueCheck
        return $ Provers (permCheck epp . simplify) z3vp

getInternalZ3Provers :: IO ProverRecord
getInternalZ3Provers =
        return $ Provers (permCheck (TPProver ()) . simplify . (rewriteFOF simplR)) valueCheck
-}
