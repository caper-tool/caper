module Main where
import Paths_Caper (version)
import Data.Version (showVersion)


import Caper.Assertions
import Caper.Provers


main::IO()
main = putStrLn $ "Caper " ++ showVersion version