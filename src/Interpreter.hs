module Main where
import Paths_Caper (version)
import Data.Version (showVersion)

import Caper.Interpreter.Interpreter
import Caper.Interpreter.Environment

main :: IO ()
main = do
        putStrLn $ "Caper Interpreter " ++ showVersion version
        putStrLn $ "Type 'quit' to exit."
        env <- emptyEnv
        (until_ (== "quit") (readPrompt "> ") . evalAndPrint) env