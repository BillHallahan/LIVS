module Main where

import LIVS.Config.Config

import LIVS.Target.JavaScript.Interface

import LIVS.Core.Init

import System.Console.CmdArgs
import System.Random

main :: IO ()
main = do
    config <- cmdArgs livsConfig

    case seed config of
        Just s -> setStdGen $ mkStdGen s
        Nothing -> return ()

    jsEnv <- jsLanguageEnv

    synth config jsEnv