module Main where

import LIVS.Config.Config

import LIVS.Target.JavaScript.Interface

import LIVS.Core.Init

import qualified Data.HashMap.Lazy as HM

import System.Console.CmdArgs
import System.Random
import System.Directory

import System.Timeout
import Data.Time.Clock
import Data.Either

import Control.Concurrent
import Control.Exception
import Control.Monad.Loops

main :: IO ()
main = do

    setStdGen $ mkStdGen 108

    jsEnv <- jsLanguageEnv

    let benchmarkDir = "benchmarks/synthesis/"
    benchmarksFilepaths <- listDirectory benchmarkDir

    config <- cmdArgs livsConfig

    let benchmarkTimeout = 1

    results <- mapM
       (\fp -> do
          putStrLn $ "File = " ++ show fp
          let synthCall = (synth (config {code_file = fp}) jsEnv)
 
          result <- newEmptyMVar :: IO (MVar (Either SomeException String))

          -- run synthesis in a new thread (timeout doesn't work with our timeouts of cvc4)
          startTime <- getCurrentTime
          tId <- forkFinally (synthCall) (\r -> putMVar result r) 
          whileM_ 
            (do
               currTime <- getCurrentTime
               print benchmarkTimeout
               print (realToFrac $ diffUTCTime currTime startTime)
               return ((realToFrac $ diffUTCTime currTime startTime) < benchmarkTimeout)
            )
            (do 
               return ()
            )
          killThread tId
          --get result out of MVar
          r <- readMVar result 
          stopTime <- getCurrentTime

          --calc time
          let x = realToFrac $ diffUTCTime stopTime startTime 
          return (x, isRight r)
       )
       (map (\b -> benchmarkDir++b++"/fullGrammar.js") benchmarksFilepaths)

    print results
