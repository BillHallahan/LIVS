module Target.JavaScript (javascriptTests) where

import LIVS.Target.General.LanguageEnv
import LIVS.Target.JavaScript.Interface
import LIVS.Target.JavaScript.JSIdentifier
import LIVS.Language.Syntax
import LIVS.Language.Typing

import qualified Data.HashSet as S
import Data.Char (isSpace)


import Test.Tasty
import Test.Tasty.HUnit

javascriptTests :: IO TestTree
javascriptTests = do
  r <- run
  p <- parseDeparse
  return $ testGroup "js LIVS" [ r
                      , p ]

parseDeparse :: IO TestTree
parseDeparse = do
  let n = Name Ident "f" Nothing
      testFile = "tests/test_files/oneFxn.js"
  orig_def <- extractJavaScriptDefinition testFile n
  fileContents <- readFile testFile
  let deparsed = trim $ toJavaScriptDef S.empty n orig_def
  return $ testCase "Run JS Test 2"
            $ assertBool ("File contents:\n" ++ fileContents ++ "\nDeparsed:\n" ++ deparsed)
                ("f = function (x) { return x}" == deparsed)

trim :: String -> String
trim = f . f
   where f = reverse . dropWhile isSpace

run :: IO TestTree
run = do
    v <- callConstFxn 
    return $ testCase "Run JS Test 1"
              $ assertBool "Correct run1" 
                (v == AppVal (DataVal jsIntDC) (LitVal (LInt 3)))

callConstFxn :: IO Val
callConstFxn = do
  j <- jsLanguageEnv
  (call j S.empty) testFxn

testFxn :: Expr
testFxn = 
  App (
    Lam 
      (Id (Name Ident "x" Nothing) (intType))
      (Lit $ LInt 3)
    )
    (Lit $ LInt 0)
