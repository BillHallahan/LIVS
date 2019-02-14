module Main where

import Test.Tasty

import Language.Expr
import Language.Typing

main :: IO ()
main = defaultMain
       =<< return tests

tests :: TestTree
tests =  testGroup "Tests" [ exprTests
                           , typingTests ]