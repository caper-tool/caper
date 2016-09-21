{-# LANGUAGE FlexibleContexts, MultiParamTypeClasses #-}
{-# LANGUAGE CPP #-}
{-| This module provides functions for generating prover instances based on the configuration file.
-}
-- #define z3ffi
module Caper.Provers where
import Data.ConfigFile
#if MIN_VERSION_mtl(2,2,1)
import Control.Monad.Except
#else
import Control.Monad.Error
#endif
import Control.Monad.Reader

import Caper.ProverDatatypes
import Caper.Provers.Permissions.Internal
import Caper.Provers.Permissions.E
import qualified Caper.Provers.Values.SBV as VP
#ifdef z3ffi
import qualified Caper.Provers.Values.Z3 as VP2
import qualified Caper.Provers.Values.Z3plus as VP3
import Caper.Provers.Permissions.SMT
#endif
import Caper.FirstOrder
import Caper.Utils.MemoIO

-- |The default configuration options.
configDefaults :: MonadError CPError m => m ConfigParser
configDefaults = readstring emptyCP "[Provers]\npermissions = internal\nvalues = z3\n[EProver]\ntimeout=1000\n[InternalProver]\nmode=tree\n[Z3Prover]\ntimeout=1000"

-- |Configuration options read from the file "config.ini", backed by defaults
configFile :: (MonadError CPError m, MonadIO m) => m ConfigParser
configFile = do
                def <- configDefaults
                join $ liftIO $ readfile def "config.ini"

-- |Initialise the provers using the configuration file
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
#ifdef z3ffi
                        "smt" -> do
                                timeout <- get conf "Z3Prover" "timeout" -- TODO: Possibly make this separately configurable
                                return (permCheckZ3 (Just timeout), permCheckZ3Info)
#endif
                        _ -> do
                                mode <- get conf "InternalProver" "mode"
                                let ipp = if mode == "bigint" then permCheckBigInt else permCheckTree
                                let ipi = return $ if mode == "bigint" then
                                        "Internal permissions prover, bigint configuration" else
                                        "Internal permissions prover, tree configuration"
                                return (ipp . simplify . rewriteFOF simplR, ipi)
                pp <- liftIO $ memoIO pp0 -- cache results from the permissions prover
                valProver <- get conf "Provers" "values"
                timeout <- get conf "Z3Prover" "timeout"
                (vp, vi) <- case valProver :: String of
#ifdef z3ffi
                        "z3-ffi" -> return (VPBasic $ VP2.valueCheck (Just timeout), VP2.valueProverInfo)
                        "z3-plus" -> do
                                vp <- liftIO $ VP3.createEntailsChecker (Just timeout)
                                return (VPEnhanced (VP2.valueCheck (Just timeout)) vp, VP3.valueProverInfo)
#endif
                        _ -> return (VPBasic $ VP.valueCheck (if timeout <= 0 then Nothing else Just $ (timeout - 1) `div` 1000 + 1), VP.valueProverInfo)
                return $ Provers pp vp ppi vi
                        
-- |Initialise the provers from the configuration file.  Errors with the configuration
-- file are raised as errors.
initProvers :: IO ProverRecord
initProvers = do
#if MIN_VERSION_mtl(2,2,1)
                res <- runExceptT proversFromConfig
#else
                res <- runErrorT proversFromConfig
#endif
                case res of
                        (Left e) -> error $ "Failed parsing configuration file: " ++ show e
                        (Right r) -> return r


-- | Run something that requires a 'ProverRecord'.  Will probably be removed in future.
runWithProvers :: (MonadIO m) => ReaderT ProverRecord m a -> m a
runWithProvers o = liftIO initProvers >>= runReaderT o

