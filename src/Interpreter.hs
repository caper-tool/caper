module Main where
import Paths_Caper (version)
import Data.Version (showVersion)
import System.Environment

import Caper.Interpreter.Interpreter

main :: IO ()
main = do
        args <- getArgs
        putStrLn $ "Caper Interpreter " ++ showVersion version
        putStrLn "Type 'quit' to exit."
        runInterpreter args
