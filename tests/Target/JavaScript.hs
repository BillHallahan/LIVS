module Target.JavaScript (javascriptTests) where

import LIVS.Target.General.LanguageEnv
import LIVS.Target.JavaScript.Interface
import LIVS.Target.JavaScript.JSIdentifier
import LIVS.Language.Syntax
import LIVS.Language.Typing

import qualified Data.HashSet as S

import Test.Tasty
import Test.Tasty.HUnit

javascriptTests :: IO TestTree
javascriptTests = do
  r <- run
  return $ testGroup "JavaScript" [ r ]

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
      (Id (IdentName "x") (intType))
      (Lit $ LInt 3)
    )
    (Lit $ LInt 0)
