{-# LANGUAGE OverloadedStrings #-}
module Caper.IntegrationTests (tests, getTestCaseList) where

import Paths_caper

import Test.Tasty (TestTree, testGroup)
import Test.Tasty.HUnit (testCaseInfo, testCase, (@=?), (@?), assertFailure)

import System.Directory (doesFileExist, getDirectoryContents)
import System.FilePath ((</>), takeExtensions)
import System.Process (readProcessWithExitCode)
import System.Exit (ExitCode(..))
import qualified Data.Text as Text
import qualified Data.Text.IO as Text
import Text.Read (readMaybe)

testCaseDirectory :: String
testCaseDirectory = "runtests"

testCasePath :: String -> String
testCasePath name = testCaseDirectory </> name

tests :: [FilePath] -> TestTree
tests testCases = testGroup "Caper.Integration" [  
    testCase "Caper binary is available for the test suite" $ do
      exe <- getExecutablePath
      doesFileExist exe @? "Caper executable does not exist in the binary directory",
    integrationTests testCases
  ]

integrationTests :: [FilePath] -> TestTree
integrationTests testCases = 
  testGroup "End-to-end integration tests" $ flip map testCases $ \tc ->
    testCaseInfo tc $ do
      (description, result) <- testFile tc
      case result of
        Nothing ->
          assertFailure "Skipped test case due to error in test case description"
        Just (expected, actual) ->
          expected @=? actual     
      return description

getExecutablePath :: IO FilePath
getExecutablePath = (</> "Caper") <$> getBinDir

getTestCaseList :: IO [FilePath]
getTestCaseList = filter ((== ".t") . takeExtensions) <$> getDirectoryContents testCaseDirectory

data TestResult = ACCEPT | REJECT | ERROR 
        deriving (Eq,Ord,Show, Read)

testFile :: FilePath -> IO (String, Maybe (TestResult, TestResult))
testFile tc = do
    caperPath <- getExecutablePath
    contents <- Text.readFile $ testCasePath tc
    let testName = Text.unpack . Text.strip . head . Text.lines . Text.drop (5 + Text.length (fst . Text.breakOn "NAME:" . Text.toUpper $ contents)) $ contents
    let mexpected = readMaybe . Text.unpack . Text.strip . head . Text.lines . Text.drop 7 . snd . Text.breakOn "RESULT:" $ Text.toUpper contents
    case mexpected of
      Nothing -> return (testName, Nothing)
      Just expected -> do
        (exitCode, out, _) <- readProcessWithExitCode caperPath [testCasePath tc] ""
        let conclude actual = return (testName, Just (expected, actual))
        conclude $ if exitCode == ExitSuccess
                   then case Text.unpack . Text.strip . Text.pack . last . lines $ out of
                          "ACCEPTED" -> ACCEPT
                          "REJECTED" -> REJECT
                          _ -> ERROR
                   else ERROR
