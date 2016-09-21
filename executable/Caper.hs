module Main where
import Paths_caper (version)
import Data.Version (showVersion)
import Control.Exception
import Control.Monad.Reader
import System.Environment
import System.Console.ArgParser
import System.Console.ArgParser.Params
import System.Console.ArgParser.Parser
import System.Console.ArgParser.Format

import Caper.Utils.MonadHoist
import Caper.Constants
import Caper.Predicates (createPredicateContext)
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
import Caper.DeclarationTyping
import Caper.SymbolicExecution

data CommandLine =
    CLVersion           -- Get version information; test configuration
    | CLVerify {        -- Verify a file
        verifyFile :: FilePath,
        verbose :: Bool,
        cfgROL :: Int,
        cfgRCL :: Int,
        cfgInteractive :: Bool
        }

commandLineParser :: ParserSpec CommandLine
commandLineParser = CLVerify
    `parsedBy` reqPos "file" `Descr` "source file to verify"
    `andBy` boolFlag "v" `Descr` "verbose output"
    `andBy` optFlag defaultRegionOpenLimit "o" `Descr` "maximum number of regions to open [default: " ++ show defaultRegionOpenLimit ++ "]"
    `andBy` optFlag defaultRegionConstructionLimit "c" `Descr` "maximum number of regions to construct in one step [default: " ++ show defaultRegionConstructionLimit ++ "]"
    `andBy` boolFlag "i" `Descr` "interactive verification"

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
                    let vpp = (case (valueProver provers) of VPBasic vp -> vp; VPEnhanced vp _ -> vp)
                    r <- vpp FOFTrue
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
caperCommand (CLVerify file verb rol rcl inter) = do
        declrs <- parseFile file
        print declrs
        let funDecs = functionDeclrs declrs
        provers <- initProvers
        let filtLog = filterLogger (if verb then const True else logNotProver)
        let configuration = defaultConfiguration { ccRegionOpenLimit = rol, ccRegionConstructionLimit = rcl, ccInteractiveVerification = inter }
        result <- runOutLogger $ filtLog $ flip runReaderT [StringContext $ "File: \"" ++ file ++ "\"."] $ runRaiseT $ do
            (predTypings, regTypeTypings) <- typeDeclarations declrs
            let pc = createPredicateContext predTypings
            procSpecs <- declrsToProcedureSpecs funDecs
            rtc <- hoist (withReaderT (ProverContext provers)) $ declrsToRegionTypeContext declrs regTypeTypings
            liftIO $ print rtc 
            hoist (withReaderT (ProcedureContext configuration procSpecs rtc pc provers)) $ do
                logEvent $ InfoEvent "Validating region declarations."
                checkRegionTypeContextInterpretations
                -- FIXME: Add check that transitions are well-formed (guards are valid)
                localWithDistinctionConditions $ do
                        logEvent $ InfoEvent "Verifying procedures."
                        verifyProcedures funDecs
        case result of
            Right () -> putStrLn "ACCEPTED"
            Left (context, exception) -> do
                    mapM_ print (reverse context)
                    print exception
                    putStrLn "REJECTED"
                     

main :: IO ()
main = caperApp caperCommand

