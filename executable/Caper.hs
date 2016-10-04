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
    -- |Get version information; test configuration
    CLVersion
    -- |Verify a file
    | CLVerify {        
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
    (Just "Copyright (c) 2013-2016 Thomas Dinsdale-Young, Pedro da Rocha Pinto, Kristoffer Just Andersen.")

caperApp :: (CommandLine -> IO ()) -> IO ()
caperApp app = do
        pn <- getProgName
        runApp (caperInterface pn) app

caperCommand :: CommandLine -> IO ()
caperCommand CLVersion = do
    putStrLn $ "Caper " ++ showVersion version
    (do provers <- initProvers
        putStrLn "Prover configuration\n====================\nValue prover:"
        vpinfo <- _valueInfo provers
        putStrLn vpinfo
        (do let vpp =
                    case valueProver provers of
                        VPBasic vp -> vp
                        VPEnhanced vp _ -> vp
            r <- vpp FOFTrue
            case r of
                Just True -> return ()
                _ ->
                    putStrLn "*** ERROR: The value prover could not prove True.") `catch`
            (\e ->
                  putStrLn $
                  "*** ERROR: Invoking the value prover resulted in the following error:\n" ++
                  show (e :: SomeException))
        putStrLn "\nPermissions prover:"
        ppinfo <- _permissionsInfo provers
        putStrLn ppinfo
        (do r <- permissionsProver provers FOFTrue
            case r of
                Just True -> return ()
                _ ->
                    putStrLn
                        "*** ERROR: The permissions prover could not prove True.") `catch`
            (\e ->
                  putStrLn $
                  "*** ERROR: Invoking the permissions prover resulted in the following error:\n" ++
                  show (e :: SomeException))) `catch`
        (\e ->
              putStrLn $
              "*** ERROR: Failed to initialise provers:\n" ++
              show (e :: SomeException))
caperCommand (CLVerify file verb rol rcl inter) = do
    -- Parse the file
    declrs <- parseFile file
    -- Function declarations
    let funDecs = functionDeclrs declrs
    -- Initialise the provers
    provers <- initProvers
    -- Filter the log based on verbosity level
    let filtLog =
            filterLogger
                (if verb
                     then const True
                     else logNotProver)
    -- Set up the configuration
    let configuration =
            defaultConfiguration
            { ccRegionOpenLimit = rol
            , ccRegionConstructionLimit = rcl
            , ccInteractiveVerification = inter
            }
    result <- 
        -- Log to stdout
        runOutLogger $
        -- Filter the log
        filtLog $
        -- Reader monad for exception context
        flip runReaderT [StringContext $ "File: \"" ++ file ++ "\"."] $
        -- Deal with raising exceptions
        runRaiseT $
        do -- Create the context
           -- Type the declarations for predicates and region types
           (predTypings, regTypeTypings) <- typeDeclarations declrs
           -- Context of predicates
           let pc = createPredicateContext predTypings
           -- Procedure specifications
           procSpecs <- declrsToProcedureSpecs funDecs
           -- Region type context
           rtc <- 
               hoist (withReaderT (ProverContext provers)) $
               declrsToRegionTypeContext declrs regTypeTypings
           hoist
               -- Run with the context
               (withReaderT
                    (ProcedureContext configuration procSpecs rtc pc provers)) $
               do -- Start by checking the region types have sensible interpretations
                  logEvent $ InfoEvent "Validating region declarations."
                  checkRegionTypeContextInterpretations
                  -- FIXME: Add check that transitions are well-formed (guards are valid)
                  -- Be smart about identifying when regions must be identical
                  localWithDistinctionConditions $
                      do logEvent $ InfoEvent "Verifying procedures."
                         -- Actually verify the procedures
                         verifyProcedures funDecs
    case result of
        Right () -> putStrLn "ACCEPTED"
        Left (context, exception) -> do
            mapM_ print (reverse context)
            print exception
            putStrLn "REJECTED"
                     

main :: IO ()
main = caperApp caperCommand

