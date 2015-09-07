module Main where
import Paths_Caper (version)
import Data.Version (showVersion)
import Control.Exception
import Control.Monad.Reader
import System.Environment
import System.Console.ArgParser
import System.Console.ArgParser.Params
import System.Console.ArgParser.Parser
import System.Console.ArgParser.Format

import Caper.Utils.MonadHoist
-- import Caper.Assertions
import Caper.Contexts
import Caper.ProverDatatypes
import Caper.Provers
import Caper.Parser.Parser
import Caper.Parser.AST
import Caper.Exceptions
import Caper.Logger
import Caper.RegionTypes
import Caper.RegionInterpretations
import Caper.Procedures


data CommandLine =
    CLVersion           -- Get version information; test configuration
    | CLVerify {        -- Verify a file
        verifyFile :: FilePath
        }

commandLineParser :: ParserSpec CommandLine
commandLineParser = CLVerify
    `parsedBy` reqPos "file" `Descr` "source file to verify"

caperSpecialFlags :: [SpecialFlag CommandLine]
caperSpecialFlags = 
    [(flagparser Short "help" "show this help message and exit",
        const . Left . showCmdLineAppUsage defaultFormat),
     (flagparser Long "version" "show version information, test configuration options and exit",
        \_ _ -> Right CLVersion)]
    where
        flagparser fmt key descr = liftParam $ FlagParam fmt key id `Descr` descr

caperInterface :: String -> CmdLnInterface CommandLine
caperInterface progName = CmdLnInterface
    commandLineParser
    caperSpecialFlags
    progName
    (Just $ showVersion version)
    (Just "Caper: a verification tool for concurrent programs.")
    (Just "Copyright (c) 2013-2015 Thomas Dinsdale-Young, Pedro da Rocha Pinto.")

caperApp :: (CommandLine -> IO ()) -> IO ()
caperApp app = do
        pn <- getProgName
        runApp (caperInterface pn) app

caperCommand :: CommandLine -> IO ()
caperCommand CLVersion = do
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
            ) `catch` (\e -> putStrLn $ "*** ERROR: Failed to initialise provers:\n" ++ show (e :: SomeException))
caperCommand (CLVerify file) = do
        declrs <- parseFile file
        print declrs
        provers <- initProvers
        result <- runErrLogger $ flip runReaderT [StringContext $ "File: \"" ++ file ++ "\"."] $ runRaiseT $ do
            procSpecs <- declrsToProcedureSpecs (functionDeclrs declrs)
            rtc <- declrsToRegionTypeContext declrs
            liftIO $ print rtc 
            hoist (withReaderT (ProcedureContext procSpecs rtc provers)) $ do
                checkRegionTypeContextInterpretations rtc
        print result

main::IO()
main = caperApp caperCommand

