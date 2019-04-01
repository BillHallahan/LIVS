module Core.TypeValueRules where

import LIVS.Language.Syntax
import LIVS.Core.Fuzz
import LIVS.Target.JavaScript.JSIdentifier

import Test.Tasty
import Test.Tasty.HUnit


typeValueTests :: TestTree
typeValueTests = testGroup "Type-Value rules" [
      testSmall
    --, testLarge 
    ]

testSmall :: TestTree
testSmall = testCase "typeVal Test 1"
    $ assertBool (show $ typeValueRules exs)
        (typeValueRules exs == [([jsStringDC, jsStringDC], DataVal jsErrorDC)])

testLarge :: TestTree
testLarge = undefined

f :: Id
f = Id (IdentName "f") (TyFun jsIdentType (TyFun jsIdentType jsIdentType))

jsStringVal :: String -> Val
jsStringVal = AppVal (DataVal jsStringDC) . LitVal . LString

jsIntVal :: Int -> Val
jsIntVal = AppVal (DataVal jsIntDC) . LitVal . LInt

exs :: [Example]
exs = [
      -- these two examples agree
        Example { func = f
                , input = [jsStringVal "x", jsStringVal "x"]
                , output = DataVal jsErrorDC }
      , Example { func = f
                , input = [jsStringVal "x", jsStringVal "y"]
                , output = DataVal jsErrorDC }

      -- these two disagree on output value, so we do not learn anything
      , Example { func = f
                , input = [jsIntVal 3, jsIntVal 4]
                , output = jsIntVal 3}
      , Example { func = f
                , input = [jsIntVal 4, jsIntVal 4]
                , output = jsIntVal 4}
      ]




