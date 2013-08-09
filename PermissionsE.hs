{-# LANGUAGE DeriveFunctor #-}

import Control.Concurrent
import Data.List
import System.IO
import System.Process
import qualified Control.Concurrent.MSem as MSem
import Control.Concurrent.MSem (MSem)
import Control.Concurrent.MVar
import System.Exit

-- Note, variables must be alpha-numeric (possibly including _) to work!

data BAExpression v = BAVariable v
                | BAone
                | BAzero
                | BAMeet (BAExpression v) (BAExpression v)
                | BAJoin (BAExpression v) (BAExpression v)
                deriving (Eq, Ord, Functor)

instance Show v => Show (BAExpression v) where
        show (BAVariable x) = 'V' : show x
        show BAone = "one"
        show BAzero = "zero"
        show (BAMeet a b) = "meet(" ++ show a ++ "," ++ show b ++ ")"
        show (BAJoin a b) = "join(" ++ show a ++ "," ++ show b ++ ")"

data BAFormula v =
          BAForall [v] (BAFormula v)
        | BAExists [v] (BAFormula v)
        | BANot (BAFormula v)
        | BAAnd (BAFormula v) (BAFormula v)
        | BAOr (BAFormula v) (BAFormula v)
        | BAImpl (BAFormula v) (BAFormula v)
        | BAIff (BAFormula v) (BAFormula v)
        | BADisj (BAExpression v) (BAExpression v)
        | BAComp (BAExpression v) (BAExpression v) (BAExpression v)
        | BAEq (BAExpression v) (BAExpression v)
        deriving (Eq, Ord, Functor)

instance Show v => Show (BAFormula v) where
        show (BAForall [] f') = show f'
        show (BAForall xs f') = "(![" ++ intercalate "," (map (('V':) . show) xs) ++ "]: " ++ show f' ++ ")"
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
        

newtype NewString = NewString String deriving (Eq, Ord)
instance Show NewString where
        show (NewString s) = s

var :: String -> BAExpression NewString
var = BAVariable . NewString

bindVars :: [String] -> [NewString]
bindVars = map NewString

crossSplit :: BAFormula NewString
crossSplit = BAForall [v "f", v "a", v "b", v "c", v "d"] $
        BAImpl (BAAnd (BAComp (var "a") (var "b") (var "f")) (BAComp (var "c") (var "d") (var "f"))) $
        BAExists [v "ac", v "ad", v "bc", v "bd"] $
        BAAnd (BAAnd (BAComp (var "ac") (var "ad") (var "a")) (BAComp (var "bc") (var "bd") (var "b")))
        (BAAnd (BAComp (var "ac") (var "bc") (var "c")) (BAComp (var "ad") (var "bd") (var "d")))
        where v = NewString

test1 = BAExists (bindVars ["x"]) $ BAForall (bindVars ["y"]) (BADisj (var "x") (var "y"))

tptpBAPrelude :: IO String
tptpBAPrelude = readFile "ba_prelude.tptp"

query :: Show v => BAFormula v -> String
query f = "fof(query,question," ++ show f ++ ")."

startCheck :: Show v => String -> BAFormula v -> IO ProcessHandle
startCheck prelude formula = do
        let p = (proc "C:\\cygwin\\home\\td202\\E\\bin\\eprover.exe"
                ["--auto", "--tptp3-format"]) { std_in = CreatePipe, std_out = CreatePipe, std_err = CreatePipe }
        (Just inp, Just outp, _, ph) <- createProcess p
        hPutStrLn inp (prelude ++ query formula)
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

checkBothWays :: Show v => String -> BAFormula v -> IO (Maybe Bool)
checkBothWays prelude formula = do
        htrue <- startCheck prelude formula
        mvtrue <- newEmptyMVar
        sem <- MSem.new 0
        tidtrue <- forkIO $ waitForCheck htrue sem mvtrue
        hfalse <- startCheck prelude (BANot formula)
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
        
main :: IO ()
main = do
        prel <- tptpBAPrelude
        r <- checkBothWays prel test1
        putStrLn (show r)


