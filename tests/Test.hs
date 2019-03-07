module Main where

import Test.Tasty

import Interpreter.Interpreter
import Language.CallGraph
import Language.Expr
import Language.Naming
import Language.Typing
import Language.Monad.Naming
import LIVS.LIVS

import Target.JavaScript

main :: IO ()
main = do
  targets <- targetTests
  defaultMain $ testGroup "all" [
      targets
   -- , tests
    ]

tests :: TestTree
tests =  testGroup "Tests" [ interpreterTests
                           , callGraphTests
                           , exprTests
                           , namingTests
                           , typingTests
                           , monadNamingTests
                           , livsTests ]

targetTests :: IO TestTree
targetTests = do 
   j <- javascriptTests
   return $ testGroup "Targets" [ j ]
