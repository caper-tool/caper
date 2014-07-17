{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE CPP #-}
-- #define z3ffi
module Provers where
import ProverDatatypes
-- import Permissions
import PermissionsI
import PermissionsE
import qualified ValueProver as VP
#ifdef z3ffi
import qualified ValueProver2 as VP2
#endif
import FirstOrder
import Data.ConfigFile
import Control.Monad.Error
import Control.Monad.Reader
import Utils.MemoIO

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
                pp0 <- case permProver of
                        "e" -> do
                                exec <- get conf "EProver" "executable"
                                timeout <- get conf "EProver" "timeout"
                                epp <- liftIO $ makeEPProver exec timeout
                                return (epp . simplify)
                        _ -> do
                                mode <- get conf "InternalProver" "mode"
                                let ipp = if mode == "bigint" then permCheckBigInt else permCheckTree
                                return (ipp . simplify . (rewriteFOF simplR))
                pp <- liftIO $ memoIO pp0 -- cache results from the permissions prover
                valProver <- get conf "Provers" "values"
                timeout <- get conf "Z3Prover" "timeout"
                let vp = case valProver :: String of
#ifdef z3ffi
                        "z3-ffi" -> VP2.valueCheck (Just timeout)
#endif
                        _ -> VP.valueCheck (if timeout <= 0 then Nothing else Just $ (timeout - 1) `div` 1000 + 1)
                return $ Provers pp vp
                        
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
