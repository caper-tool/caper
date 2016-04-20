{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE ExtendedDefaultRules #-}
{-# OPTIONS_GHC -fno-warn-type-defaults #-}

module RunTests (tests) where

import Distribution.TestSuite hiding (run)
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
import qualified Data.Map.Strict as Map
import Data.Maybe (fromMaybe)

{-
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


main = shelly $ silently $ errExit False $ do
    dir   <- liftIO getExecutablePath
    cd $ fromText $ pack $ takeDirectory dir
    cd rootPath
    value <- pwd
    names <- findWhen (return . isSuffixOf ".t" . toTextIgnore) testsPath
    m' <- foldM testFile (Map.empty :: Map.Map TestResult Int) names
    liftIO $ putStrLn $ Map.foldlWithKey (\s k v -> (s ++ show k ++ ": " ++ show v ++ "; ")) "" m'
-}
tests :: IO [Test]
tests = do
    -- dir <- getExecutablePath
    -- putStrLn dir
    return [undefined]