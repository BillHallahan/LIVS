module Main where

import Test.Tasty

import Interpreter.Interpreter
import Language.AST
import Language.CallGraph
import Language.Expr
import Language.Naming
import Language.Typing
import Language.Monad.Naming
import LIVS.LIVS
import UI.Parse
import Sygus.SMTLexer
import Sygus.TypeValueRules

import Target.JavaScript

main :: IO ()
main = do
  targets <- targetTests
  defaultMain $ testGroup "all" [
      targets
    , tests
    ]

tests :: TestTree
tests =  testGroup "Tests" [ interpreterTests
                           , astTests
                           , callGraphTests
                           , exprTests
                           , namingTests
                           , typingTests
                           , monadNamingTests
                           , livsTests
                           , uiParseTests 
                           , typeValueTests
                           , smtLexerTests
                           ]

targetTests :: IO TestTree
targetTests = do 
   j <- javascriptTests
   return $ testGroup "Targets" [ j ]
