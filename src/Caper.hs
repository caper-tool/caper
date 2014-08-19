module Main where
import Paths_Caper (version)
import Data.Version (showVersion)
import Control.Exception

import Caper.Assertions
import Caper.ProverDatatypes
import Caper.Provers


main::IO()
main = do
        putStrLn $ "Caper " ++ showVersion version
        (do 
        provers <- initProvers
        putStrLn "Prover configuration\n====================\nValue prover:"
        vpinfo <- _valueInfo provers
        putStrLn vpinfo
        (do
                r <- valueProver provers FOFTrue
                case r of
                        Just True -> return ()
                        _ -> putStrLn "*** ERROR: The value prover could not prove True."
                ) `catch` (\e -> putStrLn $ "*** ERROR: Invoking the value prover resulted in the following error:\n" ++ show (e :: SomeException))
        putStrLn "\nPermissions prover:"
        ppinfo <- _permissionsInfo provers
        putStrLn ppinfo
        (do
                r <- permissionsProver provers FOFTrue
                case r of
                        Just True -> return ()
                        _ -> putStrLn "*** ERROR: The permissions prover could not prove True."
                ) `catch` (\e -> putStrLn $ "*** ERROR: Invoking the permissions prover resulted in the following error:\n" ++ show (e :: SomeException))
        ) `catch` (\e -> putStrLn $ "*** ERROR: Falied to initialise provers:\n" ++ show (e :: SomeException))
        putStrLn "Proved."
