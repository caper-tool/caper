module Main where

import Test.Tasty (defaultMain, testGroup)

import qualified Caper.FirstOrder.Tests

main :: IO ()
main = defaultMain $ testGroup "Tests" [
  Caper.FirstOrder.Tests.tests
  ]
