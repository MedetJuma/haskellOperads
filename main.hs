

module Main where

import GHC.Conc (getNumCapabilities)
import IO
import Parsing
import Generation
import PrettyPrinting

main :: IO ()
main = do
  caps <- getNumCapabilities
  putStrLn $ "Runtime capabilities: " ++ show caps ++ " cores"
  gb "input.txt"

gb :: String -> IO ()
gb input = do
  c <- readIn input
  putStrLn $ show c
  solve c

