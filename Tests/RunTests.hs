{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE ExtendedDefaultRules #-}
{-# OPTIONS_GHC -fno-warn-type-defaults #-}

import Control.Applicative
import Data.List(sort)
import Control.Monad (forM_,liftM,foldM)
import Shelly
import Prelude hiding (FilePath, lines, drop, concat, takeWhile)
import System.Directory
import Data.Text hiding (last, length)
import qualified Data.Text
import System.FilePath hiding (FilePath)
import System.Environment
import System.Console.ANSI
import qualified Data.Map.Strict as Map
import Data.Maybe (fromMaybe)

caperPath = "dist/build/Caper/Caper"
testsPath = "runtests/"
rootPath = "../../../"

data TestResult = Passed | Failed | Errored | Skipped
        deriving (Eq,Ord,Show)

--echoResult :: Text -> FilePath -> TestResult -> Sh ()
echoResult fname testName res = do
    echo_n $ concat $ ["[", pack $ takeFileName (unpack $ toTextIgnore fname), "] ",
        testName, ": "]
    case res of
        Passed -> liftIO (setSGR [SetColor Foreground Vivid Green]) >> echo "PASSED"
        Failed -> liftIO (setSGR [SetColor Foreground Vivid Red]) >> echo "FAILED"
        Errored -> liftIO (setSGR [SetColor Foreground Vivid Yellow]) >> echo "ERROR"
        Skipped -> echo "SKIPPED"
    liftIO (setSGR [])

testFile rmap name = do
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
                        else Errored
            echoR res
            return $ Map.alter (Just . (+1) . fromMaybe 0) res rmap
    case unpack testRes of
        ('A':_) -> runCheck (=="ACCEPTED")
        ('R':_) -> runCheck (=="REJECTED")
        _ -> do
            echoR Skipped
            return $ Map.alter (Just . (+1) . fromMaybe 0) Skipped rmap


main = shelly $ silently $ errExit False $ do
    dir   <- liftIO $ getExecutablePath
    cd $ fromText $ pack $ takeDirectory $ dir
    cd $ rootPath
    value <- pwd
    names <- findWhen (\n -> return $ isSuffixOf ".t" $ toTextIgnore n) testsPath
    m' <- foldM testFile (Map.empty :: Map.Map TestResult Int) names
    liftIO $ putStrLn $ Map.foldlWithKey (\s k v -> (s ++ show k ++ ": " ++ show v ++ "; ")) "" m'
