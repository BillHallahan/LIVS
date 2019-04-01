module Sygus.TypeValueRules where

import LIVS.Language.Syntax
import LIVS.Sygus.TypeValueRules
import LIVS.Target.JavaScript.JSIdentifier

import Test.Tasty
import Test.Tasty.HUnit


typeValueTests :: TestTree
typeValueTests = testGroup "Type-Value rules" [
      typeValueTest1
    , typeTypeTest
    , inputTypeTest
    , filterNotRuleCovered1 
    ]

typeValueTest1 :: TestTree
typeValueTest1 = testCase "typeValueTest Test 1"
    $ assertBool (show $ typeValueRules exs)
        (typeValueRules (exs) == [([jsStringDC, jsStringDC], DataVal jsErrorDC)])

typeTypeTest :: TestTree
typeTypeTest = testCase "typeTypeTest Test 1"
    $ assertBool (show $ typeTypeRules exs)
        (typeTypeRules (exs) == [([jsStringDC, jsStringDC], jsErrorDC), ([jsIntDC, jsIntDC], jsIntDC)])

inputTypeTest :: TestTree
inputTypeTest = testCase "inputTypeTest Test"
    $ assertBool (show $ typeTypeRules exs)
        (inputTypeRules (exs++exsNoTypeRule) == [([jsStringDC, jsStringDC], Just jsErrorDC), ([jsIntDC, jsIntDC], Nothing)])

filterNotRuleCovered1 :: TestTree
filterNotRuleCovered1 = testCase "filterNotRuleCovered Test 1"
    $ assertBool (show $ typeValueRules exs)
        (filterNotRuleCovered [([jsStringDC, jsStringDC], DataVal jsErrorDC)] exs == exsNoValRule)




f :: Id
f = Id (Name Ident "f" Nothing) (TyFun jsIdentType (TyFun jsIdentType jsIdentType))

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
                , output = DataVal jsErrorDC } ] ++ exsNoValRule

exsNoValRule :: [Example]
exsNoValRule = 
      -- these two disagree on output value, so we do not learn anything
      [ Example { func = f
                , input = [jsIntVal 3, jsIntVal 4]
                , output = jsIntVal 3}
      , Example { func = f
                , input = [jsIntVal 4, jsIntVal 4]
                , output = jsIntVal 4}
      ]

exsNoTypeRule :: [Example]
exsNoTypeRule = 
      -- these two disagree on output type, so we do not learn anything
      [ Example { func = f
                , input = [jsIntVal 3, jsIntVal 6]
                , output = jsIntVal 3}
      , Example { func = f
                , input = [jsIntVal 4, jsIntVal 5]
                , output = jsStringVal "x"}
      ]




