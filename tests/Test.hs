module Main where

import Test.Tasty

import Interpreter.Interpreter
import Language.CallGraph
import Language.Expr
import Language.Naming
import Language.Typing
import Language.Monad.Naming
import LIVS.LIVS

main :: IO ()
main = defaultMain
       =<< return tests

tests :: TestTree
tests =  testGroup "Tests" [ interpreterTests
                           , callGraphTests
                           , exprTests
                           , namingTests
                           , typingTests
                           , monadNamingTests
                           , livsTests ]