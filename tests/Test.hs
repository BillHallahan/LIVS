module Main where

import Test.Tasty

import Typing

main :: IO ()
main = defaultMain
       =<< return tests

tests :: TestTree
tests =  testGroup "Tests" [ typingTests ]