{-# LANGUAGE FlexibleContexts #-}
module Provers where
import ProverDatatypes
import PermissionsInterface
import Permissions
import PermissionsE
import ValueProver
import qualified ValueProver2 as VP2
import FirstOrder
import Data.ConfigFile
import Control.Monad.Error
import MemoIO

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
                pp0 <- if permProver == "e" then do
                        exec <- get conf "EProver" "executable"
                        timeout <- get conf "EProver" "timeout"
                        epp <- liftIO $ makeEPProver exec timeout
                        return (permCheck epp . simplify)
                    else do
                        return (permCheck (TPProver ()) . simplify . (rewriteFOF simplR))
                pp <- liftIO $ memoIO pp0 -- cache results from the permissions prover
                valProver <- get conf "Provers" "values"
                timeout <- get conf "Z3Prover" "timeout"
                let vp = if valProver == "z3-ffi" then
                        VP2.valueCheck else 
                        valueCheck (if timeout <= 0 then Nothing else Just $ (timeout - 1) `div` 1000 + 1)
                return $ Provers pp vp
                        
initProvers :: IO ProverRecord
initProvers = do
                res <- runErrorT proversFromConfig
                case res of
                        (Left e) -> error $ "Failed parsing configuration file: " ++ show e
                        (Right r) -> return r


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
