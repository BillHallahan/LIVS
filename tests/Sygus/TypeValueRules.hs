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
    , filterNotTypeValueRuleCovered1
    , simplifyExamplesTest1
    , simplifyExamplesTest2
    , simplifyExamplesTest3
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

filterNotTypeValueRuleCovered1 :: TestTree
filterNotTypeValueRuleCovered1 = testCase "filterNotTypeValueRuleCovered Test 1"
    $ assertBool (show $ typeValueRules exs)
        (filterNotTypeValueRuleCovered [([jsStringDC, jsStringDC], DataVal jsErrorDC)] exs == exsNoValRule)


simplifyExamplesTest1 :: TestTree
simplifyExamplesTest1 = testCase "simplifyExamples Test 1"
    $ assertBool "simplifyExamples"
        (simplifyExamples ([ex1, ex2]) == [(dcmdc, [ex1Simp, ex2Simp])])
      where
        dcmdc = ([jsIntDC, jsIntDC], Just jsIntDC)

simplifyExamplesTest2 :: TestTree
simplifyExamplesTest2 = testCase "simplifyExamples Test 2"
    $ assertBool "simplifyExamples"
        (simplifyExamples ([ex3, ex4]) == [(dcmdc, [ex3SimpIn, ex4SimpIn])])
      where
        dcmdc = ([jsIntDC, jsIntDC], Nothing)

simplifyExamplesTest3 :: TestTree
simplifyExamplesTest3 = testCase "simplifyExamples Test 3"
    $ assertBool "simplifyExamples"
        (simplifyExamples ([ex3, ex4, ex5]) == 
              [ (dcmdc, [ex3SimpIn, ex4SimpIn])
              , (dcmdc2, [ex5Simp]) ])
      where
        dcmdc = ([jsIntDC, jsIntDC], Nothing)
        dcmdc2 = ([jsIntDC, jsStringDC], Just jsIntDC)

f :: Id
f = Id (Name Ident "f" Nothing) (TyFun jsIdentType (TyFun jsIdentType jsIdentType))

jsStringVal :: String -> Val
jsStringVal = AppVal (DataVal jsStringDC) . LitVal . LString

jsIntVal :: Int -> Val
jsIntVal = AppVal (DataVal jsIntDC) . LitVal . LInt

jsIntLitVal :: Int -> Val
jsIntLitVal = LitVal . LInt

jsStringLitVal :: String -> Val
jsStringLitVal = LitVal . LString

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
      [ ex1, ex2 ]

ex1 :: Example
ex1 = Example { func = f
              , input = [jsIntVal 3, jsIntVal 4]
              , output = jsIntVal 3}

ex1SimpIn :: Example
ex1SimpIn = Example { func = f
                    , input = [jsIntLitVal 3, jsIntLitVal 4]
                    , output = jsIntVal 3}

ex1Simp :: Example
ex1Simp = Example { func = f
                  , input = [jsIntLitVal 3, jsIntLitVal 4]
                  , output = jsIntLitVal 3}

ex2 :: Example
ex2 = Example { func = f
              , input = [jsIntVal 4, jsIntVal 4]
              , output = jsIntVal 4}

ex2SimpIn :: Example
ex2SimpIn = Example { func = f
                    , input = [jsIntLitVal 4, jsIntLitVal 4]
                    , output = jsIntVal 4}

ex2Simp :: Example
ex2Simp = Example { func = f
                  , input = [jsIntLitVal 4, jsIntLitVal 4]
                  , output = jsIntLitVal 4}

exsNoTypeRule :: [Example]
exsNoTypeRule = 
      -- these two disagree on output type, so we do not learn anything
      [ ex2, ex4]

ex3 :: Example
ex3 = Example { func = f
              , input = [jsIntVal 3, jsIntVal 6]
              , output = jsIntVal 3}

ex3SimpIn :: Example
ex3SimpIn = Example { func = f
                    , input = [jsIntLitVal 3, jsIntLitVal 6]
                    , output = jsIntVal 3}

ex4 :: Example
ex4 = Example { func = f
              , input = [jsIntVal 4, jsIntVal 5]
              , output = jsStringVal "x"}

ex4SimpIn :: Example
ex4SimpIn = Example { func = f
                    , input = [jsIntLitVal 4, jsIntLitVal 5]
                    , output = jsStringVal "x"}

ex5 :: Example
ex5 = Example { func = f
              , input = [jsIntVal 3, jsStringVal "y"]
              , output = jsIntVal 3}

ex5Simp :: Example
ex5Simp = Example { func = f
                  , input = [jsIntLitVal 3, jsStringLitVal "y"]
                  , output = jsIntLitVal 3}