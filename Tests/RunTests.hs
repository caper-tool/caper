{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE ExtendedDefaultRules #-}
{-# OPTIONS_GHC -fno-warn-type-defaults #-}

import Control.Applicative
import Data.List(sort)
import Control.Monad (forM_)
import Shelly
import Prelude hiding (FilePath, lines, drop, concat)
import System.Directory
import Data.Text hiding (last, length)
import System.FilePath
import System.Environment

caperPath = "dist/build/Caper/Caper"
testsPath = "runtests/"
rootPath = "../../../"

testFile name = do
    absCaperPath   <- absPath caperPath
    absName        <- absPath name
    contents       <- readfile absName
    contentsLines  <- return $ lines contents
    testName       <- return (drop 9 $ contentsLines !! 0)
    expectedResult <- return $ concat $ (drop 11 $ contentsLines !! 1):["ED"]
    out            <- run absCaperPath [toTextIgnore absName]
    exitCode       <- lastExitCode
    echo $ concat $ ["[", pack $ takeFileName (unpack $ toTextIgnore name), "] ",
                     testName, ": ",
                     if exitCode == 0
                         then if expectedResult == (last $ lines out)
                                  then "\ESC[32m\STXPASSED\ESC[m\STX"
                                  else "\ESC[31m\STXFAILED\ESC[m\STX"
                         else "\ESC[33m\STXERROR\ESC[m\STX"]

main = shelly $ silently $ errExit False $ do
    dir   <- liftIO $ getExecutablePath
    cd $ fromText $ pack $ takeDirectory $ dir
    cd $ rootPath
    value <- pwd
    names <- findWhen (\n -> return $ isSuffixOf ".t" $ toTextIgnore n) testsPath
    forM_ names $ \n -> do
        testFile n
