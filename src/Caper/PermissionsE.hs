{-# LANGUAGE DeriveFunctor, QuasiQuotes #-}
module Caper.PermissionsE(makeEPProver,eproverVersion) where
import Control.Concurrent
import Control.Monad
import Data.List
import System.IO
import System.Process
import qualified Control.Concurrent.MSem as MSem
import Control.Concurrent.MSem (MSem)
import Control.Concurrent.MVar
import System.Exit
import Debug.Trace
import System.Directory
import Control.Exception

--import Paths_Caper
import Caper.ProverDatatypes
import Caper.Utils.LiteralFileQQ


-- Note, variables must be alpha-numeric (possibly including _) to work!

data BAExpression v = BAVariable v
                | BAOne
                | BAZero
                | BAMeet (BAExpression v) (BAExpression v)
                | BAJoin (BAExpression v) (BAExpression v)
                | BACompl (BAExpression v)
                deriving (Eq, Ord, Functor)

instance Show v => Show (BAExpression v) where
        show (BAVariable x) = 'V' : show x
        show BAOne = "one"
        show BAZero = "zero"
        show (BAMeet a b) = "meet(" ++ show a ++ "," ++ show b ++ ")"
        show (BAJoin a b) = "join(" ++ show a ++ "," ++ show b ++ ")"
        show (BACompl a) = "compl(" ++ show a ++ ")"

data BAFormula v =
          BAForAll [v] (BAFormula v)
        | BAExists [v] (BAFormula v)
        | BANot (BAFormula v)
        | BAAnd (BAFormula v) (BAFormula v)
        | BAOr (BAFormula v) (BAFormula v)
        | BAImpl (BAFormula v) (BAFormula v)
        | BAIff (BAFormula v) (BAFormula v)
        | BADisj (BAExpression v) (BAExpression v)
        | BAComp (BAExpression v) (BAExpression v) (BAExpression v)
        | BAEq (BAExpression v) (BAExpression v)
        | BATrue
        | BAFalse
        deriving (Eq, Ord, Functor)

instance Show v => Show (BAFormula v) where
        show (BAForAll [] f') = show f'
        show (BAForAll xs f') = "(![" ++ intercalate "," (map (('V':) . show) xs) ++ "]: " ++ show f' ++ ")"
        show (BAExists [] f') = show f'
        show (BAExists xs f') = "(?[" ++ intercalate "," (map (('V':) . show) xs) ++ "]: " ++ show f' ++ ")"
        show (BANot f') = "(~" ++ show f' ++ ")"
        show (BAAnd f1 f2) = "(" ++ show f1 ++ " & " ++ show f2 ++ ")"
        show (BAOr f1 f2) = "(" ++ show f1 ++ " | " ++ show f2 ++ ")"
        show (BAImpl f1 f2) = "(" ++ show f1 ++ " => " ++ show f2 ++ ")"
        show (BAIff f1 f2) = "(" ++ show f1 ++ " <=> " ++ show f2 ++ ")"
        show (BADisj e1 e2) = "disj(" ++ show e1 ++ "," ++ show e2 ++ ")"
        show (BAComp e1 e2 e3) = "compose(" ++ show e1 ++ "," ++ show e2 ++ "," ++ show e3 ++ ")"
        show (BAEq e1 e2) = "(" ++ show e1 ++ " = " ++ show e2 ++ ")"
        show BATrue = "$true"
        show BAFalse = "$false"
        

newtype NewString = NewString String deriving (Eq, Ord)
instance Show NewString where
        show (NewString s) = s


baDisjoints :: PermissionExpression String -> BAFormula NewString
baDisjoints (PESum e1 e2) = BAAnd (BAAnd (baDisjoints e1) (baDisjoints e2))
                                (BAEq (BAMeet (toBAExpression e1) (toBAExpression e2)) BAZero)
baDisjoints (PECompl e) = baDisjoints e
baDisjoints _ = BATrue


toBAExpression :: PermissionExpression String -> BAExpression NewString
toBAExpression PEFull = BAOne
toBAExpression PEZero = BAZero
toBAExpression (PEVar v) = BAVariable (NewString v)
toBAExpression (PESum e1 e2) = BAJoin (toBAExpression e1) (toBAExpression e2)
toBAExpression (PECompl e) = BACompl (toBAExpression e)

toBAFormula :: FOF PermissionAtomic String -> BAFormula NewString
toBAFormula FOFFalse = BAFalse
toBAFormula FOFTrue = BATrue
toBAFormula (FOFAtom (PAEq pe1 pe2)) = BAAnd (BAAnd (baDisjoints pe1) (baDisjoints pe2))
                                        (BAEq (toBAExpression pe1) (toBAExpression pe2))
toBAFormula (FOFAtom (PADis pe1 pe2)) = BAAnd (BAAnd (baDisjoints pe1) (baDisjoints pe2))
                                        (BADisj (toBAExpression pe1) (toBAExpression pe2))
toBAFormula (FOFAnd f1 f2) = BAAnd (toBAFormula f1) (toBAFormula f2)
toBAFormula (FOFOr f1 f2) = BAOr (toBAFormula f1) (toBAFormula f2)
toBAFormula (FOFImpl f1 f2) = BAImpl (toBAFormula f1) (toBAFormula f2)
toBAFormula (FOFNot f1) = BANot (toBAFormula f1)
toBAFormula (FOFForAll v f) = BAForAll [NewString v] (toBAFormula f)
toBAFormula (FOFExists v f) = BAExists [NewString v] (toBAFormula f)


data EPProver = EPProver { tptpPrelude :: String, proverPath :: String, eTimeout :: Int }

{--
var :: String -> BAExpression NewString
var = BAVariable . NewString

bindVars :: [String] -> [NewString]
bindVars = map NewString

crossSplit :: BAFormula NewString
crossSplit = BAForAll [v "f", v "a", v "b", v "c", v "d"] $
        BAImpl (BAAnd (BAComp (var "a") (var "b") (var "f")) (BAComp (var "c") (var "d") (var "f"))) $
        BAExists [v "ac", v "ad", v "bc", v "bd"] $
        BAAnd (BAAnd (BAComp (var "ac") (var "ad") (var "a")) (BAComp (var "bc") (var "bd") (var "b")))
        (BAAnd (BAComp (var "ac") (var "bc") (var "c")) (BAComp (var "ad") (var "bd") (var "d")))
        where v = NewString

test1 = BAExists (bindVars ["x"]) $ BAForAll (bindVars ["y"]) (BADisj (var "x") (var "y"))
--}


eproverVersion :: String -> IO String
eproverVersion proverpath = 
        liftM ("EProver version: " ++) (readProcess proverpath ["--version"] "")
                `catch` (\e -> return $ "Failed to invoke EProver:\n" ++ show (e :: SomeException))

{-
tptpBAPrelude :: IO String
tptpBAPrelude = getDataFileName "ba_prelude.tptp" >>= readFile
-}

tptpBAPrelude :: String
tptpBAPrelude = [literalFile|ba_prelude.tptp|]

query :: Show v => BAFormula v -> String
query f = "fof(query,question," ++ show f ++ ")."

startCheck :: Show v => EPProver -> BAFormula v -> Handle -> Handle -> IO ProcessHandle
startCheck epp formula outHandle errHandle = do
        let p = (proc (proverPath epp)
                ["--auto", "--tptp3-format", "--output-level=0"]) { std_in = CreatePipe, std_out = UseHandle outHandle, std_err = UseHandle errHandle }
        (Just inp, _, _, ph) <- createProcess p
        hPutStrLn inp (tptpPrelude epp ++ query formula)
        hClose inp
        return ph

waitForCheck :: ProcessHandle -> MSem Int -> MVar ExitCode -> IO ()
waitForCheck ph sem res = do
        r <- waitForProcess ph
        putMVar res r
        MSem.signal sem

timeoutSem :: Int -> MSem Int -> IO ()
-- terminate the handles after timeout
timeoutSem n sem = unless (n <= 0) $
  do threadDelay n
     MSem.signal sem

-- TODO: Handle errors removing files more gracefully;
--       Ensure termination of subprocesses on error;
--       Handle errors in terminating subprocesses

checkBothWays :: Show v => EPProver -> BAFormula v -> IO (Maybe Bool)
checkBothWays epp formula = trace ("Calling E on:\n" ++ show formula) $ bracket
        (do
                out1 <- openTempFile "." "eout.log"
                err1 <- openTempFile "." "eerr.log"                
                out2 <- openTempFile "." "eout.log"
                err2 <- openTempFile "." "eerr.log"
                return (out1,err1,out2,err2))
        (\((outFile1,outHandle1),(errFile1,errHandle1),(outFile2,outHandle2),(errFile2,errHandle2)) ->
                do
                        hClose outHandle1
                        hClose outHandle2
                        hClose errHandle1
                        hClose errHandle2
                        removeFile outFile1
                        removeFile outFile2
                        removeFile errFile1
                        removeFile errFile2)
        (\((outFile1,outHandle1),(errFile1,errHandle1),(outFile2,outHandle2),(errFile2,errHandle2)) -> do
                htrue <- startCheck epp formula outHandle1 errHandle1
                mvtrue <- newEmptyMVar
                sem <- MSem.new 0
                tidtrue <- forkIO $ waitForCheck htrue sem mvtrue
                hfalse <- startCheck epp (BANot formula) outHandle2 errHandle2
                mvfalse <- newEmptyMVar
                tidfalse <- forkIO $ waitForCheck hfalse sem mvfalse
                let hs = [htrue,hfalse]
                tidTimeout <- forkIO $ timeoutSem (eTimeout epp) sem
                MSem.wait sem
                mapM_ (try . terminateProcess :: ProcessHandle -> IO (Either SomeException ())) hs
                rtrue <- takeMVar mvtrue
                rfalse <- takeMVar mvfalse
                return $ if rtrue == ExitSuccess then
                        trace "Proved." $ Just True 
                        else if rfalse == ExitSuccess then trace "Disproved." $ Just False else trace "Unknown." Nothing)


makeEPProver ::
        String -- ^Path to the eprover executable
        -> Int -- ^Timeout in milliseconds (0 or negative for no timeout)
        -> IO PermissionsProver
makeEPProver execpath timeout = do
        let prel = tptpBAPrelude
        return $ checkBothWays (EPProver prel execpath (timeout * 1000)) . toBAFormula
        -- "c:\\cygwin64\\home\\Thomas\\E\\PROVER\\eprover.exe"



{--
main :: IO ()
main = do
        prel <- tptpBAPrelude
        r <- checkBothWays prel test1
        putStrLn (show r)
--}

