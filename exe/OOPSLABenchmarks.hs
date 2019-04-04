module Main where

import LIVS.Config.Config

import LIVS.Target.JavaScript.Interface

import LIVS.Core.Init

import qualified Data.HashMap.Lazy as HM

import System.Console.CmdArgs
import System.Random
import System.Directory

main :: IO ()
main = do

    setStdGen $ mkStdGen 108

    jsEnv <- jsLanguageEnv

    let benchmarkDir = "benchmarks/synthesis/"
    benchmarksFilepaths <- listDirectory benchmarkDir

    config <- cmdArgs livsConfig
    let config = config {
          code_file = fp
        }
    results <- mapM
       (\fp -> do
          putStrLn $ "File = " ++ show fp
          
          timeout $ synth config jsEnv
       )
       (map (\b -> benchmarkDir++b++"/fullGrammar.js") benchmarksFilepaths)

    print results
