module Main where

import Test.Tasty (defaultMain, testGroup)

import qualified Caper.FirstOrder.Tests
import qualified Caper.IntegrationTests

main :: IO ()
main = do
  intTestCaseList <- Caper.IntegrationTests.getTestCaseList
  defaultMain $ testGroup "Tests" [
    Caper.FirstOrder.Tests.tests,
    Caper.IntegrationTests.tests intTestCaseList
    ]

