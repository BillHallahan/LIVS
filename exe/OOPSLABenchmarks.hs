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

    results <- mapM
       (\fp -> do
          putStrLn $ "File = " ++ show fp
          synth (livsConfig {code_file = fp}) jsEnv)
       (map (\b -> benchmarkDir++b++"/fullGrammar.js") $ take 1 benchmarksFilepaths)

    print results
