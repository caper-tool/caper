{-# LANGUAGE DeriveFunctor #-}
module PermissionsE(EPProver, makeEPProver) where
import Control.Concurrent
import Data.List
import System.IO
import System.Process
import qualified Control.Concurrent.MSem as MSem
import Control.Concurrent.MSem (MSem)
import Control.Concurrent.MVar
import System.Exit
import ProverDatatypes
import PermissionsInterface

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


data EPProver = EPProver { tptpPrelude :: String, proverPath :: String }

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

tptpBAPrelude :: IO String
tptpBAPrelude = readFile "ba_prelude.tptp"

query :: Show v => BAFormula v -> String
query f = "fof(query,question," ++ show f ++ ")."

startCheck :: Show v => EPProver -> BAFormula v -> IO ProcessHandle
startCheck epp formula = do
        let p = (proc (proverPath epp)
                ["--auto", "--tptp3-format"]) { std_in = CreatePipe, std_out = CreatePipe, std_err = CreatePipe }
        (Just inp, Just outp, _, ph) <- createProcess p
        hPutStrLn inp ((tptpPrelude epp) ++ query formula)
        hClose inp
        return ph

waitForCheck :: ProcessHandle -> MSem Int -> MVar ExitCode -> IO ()
waitForCheck ph sem res = do
        r <- waitForProcess ph
        putMVar res r
        MSem.signal sem

timeoutSem :: Int -> MSem Int -> IO ()
-- terminate the handles after timeout
timeoutSem n sem = do
        threadDelay n
        MSem.signal sem

checkBothWays :: Show v => EPProver -> BAFormula v -> IO (Maybe Bool)
checkBothWays epp formula = do
        htrue <- startCheck epp formula
        mvtrue <- newEmptyMVar
        sem <- MSem.new 0
        tidtrue <- forkIO $ waitForCheck htrue sem mvtrue
        hfalse <- startCheck epp (BANot formula)
        mvfalse <- newEmptyMVar
        tidfalse <- forkIO $ waitForCheck hfalse sem mvfalse
        let hs = [htrue,hfalse]
        tidTimeout <- forkIO $ timeoutSem 1000000 sem
        MSem.wait sem
        mapM_ terminateProcess hs
        rtrue <- takeMVar mvtrue
        rfalse <- takeMVar mvfalse
        return $ if rtrue == ExitSuccess then
                Just True 
                else if rfalse == ExitSuccess then Just False else Nothing


makeEPProver :: IO EPProver
makeEPProver = do
        prel <- tptpBAPrelude
        return $ EPProver prel "c:\\cygwin\\home\\td202\\E\\bin\\eprover.exe"

instance PermissionsProver EPProver where
        permCheck epp = (checkBothWays epp) . toBAFormula


{--
main :: IO ()
main = do
        prel <- tptpBAPrelude
        r <- checkBothWays prel test1
        putStrLn (show r)
--}

