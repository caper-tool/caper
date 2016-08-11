
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE ExtendedDefaultRules #-}
{-# OPTIONS_GHC -fno-warn-type-defaults #-}

-- import Control.Applicative
-- import Data.List(sort)

import Control.Monad (forM_,liftM,foldM)
import Shelly
import Prelude hiding (FilePath, lines, drop, concat, takeWhile)
import qualified Prelude as Prelude
import Data.Text hiding (last, length)
import qualified Data.Text
import System.FilePath hiding (FilePath)
import System.Environment
import System.Console.ANSI
import qualified Data.Map.Strict as Map
import Data.Maybe (fromMaybe)
import System.Console.GetOpt 
import Data.String (fromString)


data TestResult = Passed | Failed | Errored | Skipped
        deriving (Eq,Ord,Show)

echoResult :: FilePath -> Text -> TestResult -> Sh ()
echoResult fname testName res = do
    echo_n $ concat ["[", pack $ takeFileName (unpack $ toTextIgnore fname), "] ",
        testName, ": "]
    case res of
        Passed -> liftIO (setSGR [SetColor Foreground Vivid Green]) >> echo "PASSED"
        Failed -> liftIO (setSGR [SetColor Foreground Vivid Red]) >> echo "FAILED"
        Errored -> liftIO (setSGR [SetColor Foreground Vivid Yellow]) >> echo "ERROR"
        Skipped -> echo "SKIPPED"
    liftIO (setSGR [])

testFile :: Num a => FilePath -> Map.Map TestResult a -> FilePath -> Sh (Map.Map TestResult a)
testFile caperPath rmap name = do
    absCaperPath   <- absPath caperPath
    absName        <- absPath name
    contents       <- readfile absName
    let testName = strip $ takeWhile (not . (`elem` ['\r','\n'])) $ drop (5 + Data.Text.length (fst $ breakOn "NAME:" $ toUpper contents)) contents
    let testRes = strip $ drop 7 $ snd $ breakOn "RESULT:" $ toUpper contents
    let echoR = echoResult name testName
    let runCheck ck = do
            out <- run absCaperPath [toTextIgnore absName]
            exitCode <- lastExitCode
            let res = if exitCode == 0
                        then if ck (strip $ last $ lines out) then Passed else Failed
                        else if ck (strip $ last $ lines out) then Passed else Errored
            echoR res
            return $ Map.alter (Just . (+1) . fromMaybe 0) res rmap
    case unpack testRes of
        ('A':_) -> runCheck (=="ACCEPTED")
        ('R':_) -> runCheck (=="REJECTED")
        ('E':_) -> runCheck (\x -> not (x == "ACCEPTED" || x == "REJECTED"))
        _ -> do
            echoR Skipped
            return $ Map.alter (Just . (+1) . fromMaybe 0) Skipped rmap

runTests :: FilePath -> FilePath -> FilePath -> IO ()
runTests rootPath testsPath caperPath = shelly $ silently $ errExit False $ do
    dir   <- liftIO getExecutablePath
    echo_n (fromString dir)
    cd $ fromText $ pack $ takeDirectory dir
    cd rootPath
    names <- findWhen (return . isSuffixOf ".t" . toTextIgnore) testsPath
    m' <- foldM (testFile caperPath) (Map.empty :: Map.Map TestResult Int) names
    liftIO $ putStrLn $ Map.foldlWithKey (\s k v -> (s ++ show k ++ ": " ++ show v ++ "; ")) "" m'

main :: IO ()
main = do
  args <- getArgs
  conf <- parseConfiguration args
  runTests (rootPath conf) (testsPath conf) (caperPath conf)

data Configuration = Configuration {
  rootPath :: FilePath,
  testsPath :: FilePath,
  caperPath :: FilePath
  }

defaultConfiguration :: Configuration
defaultConfiguration = Configuration {
  rootPath = "../../../",
  testsPath = "runtests/",
  caperPath = "dist/build/Caper/Caper"
  }

options :: [OptDescr (Configuration -> Configuration)]
options = [
  Option ['r'] ["rootpath"] (ReqArg (\path conf -> conf { rootPath = fromString path}) "PATH")
    "Path to the root directory of Caper repo",
  Option ['t'] ["testspath"] (ReqArg (\path conf -> conf { testsPath = fromString path}) "PATH")
  "Folder containing integration tests",
  Option ['c'] ["caperpath"] (ReqArg (\path conf -> conf { caperPath = fromString path}) "PATH")
  "Path to Caper executable under test" ]

parseConfiguration :: [String] -> IO Configuration
parseConfiguration args =
  case getOpt Permute options args of
    (o, _, []) -> return $ Prelude.foldl (flip id) defaultConfiguration o
    (_,_,errs) -> ioError . userError $ Prelude.concat errs ++ usageInfo header options
    where
      header = "Usage: RunTests [OPTION...]"
