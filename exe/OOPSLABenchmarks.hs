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

    setStdGen $ mkStdGen 1

    jsEnv <- jsLanguageEnv

    let benchmarkDir = "benchmarks/synthesis/"
    benchmarksFilepaths <- listDirectory benchmarkDir

    mapM_
       (\fp -> synth (livsConfig {code_file = fp}) jsEnv)
       (map (\b -> benchmarkDir++b++"/fullGrammar.js") benchmarksFilepaths)