module UI.Parse (uiParseTests) where

import LIVS.Language.Syntax
import LIVS.Target.JavaScript.Interface
import LIVS.Target.JavaScript.JSIdentifier
import LIVS.UI.Parse

import Test.Tasty
import Test.Tasty.HUnit

uiParseTests :: TestTree
uiParseTests = testGroup "UI Parse" [ parseExample1
                                    , parseExamples1 ]

parseExample1 :: TestTree
parseExample1 = testCase "parseExample Test 1"
    $ assertBool "Correct parseExample" 
            (parseExample jsJSONToVal "@pbe (constraint (= (f 3) 20))" == Just ex)
    where
        ex = Example { func = Id (Name "f" Nothing) (TyFun jsIdentType jsIdentType)
                     , input = [AppVal (DataVal jsIntDC) (LitVal $ LInt 3)]
                     , output = AppVal (DataVal jsIntDC) (LitVal $ LInt 20) }

parseExamples1 :: TestTree
parseExamples1 = testCase "parseExamples Test 1"
    $ assertBool "Correct parseExamples" 
            (parseExamples jsJSONToVal ex_str == [ex1, ex2])
    where
        ex1_str = "@pbe (constraint (= (f 8) 1))"
        ex2_str = "@pbe (constraint (= (f 90) 2))"
        ex_str = ex1_str ++ "\nOTHER STUFF" ++ ex2_str ++ "\nMORE OTHER STUFF"

        ex1 = Example { func = Id (Name "f" Nothing) (TyFun jsIdentType jsIdentType)
                      , input = [AppVal (DataVal jsIntDC) (LitVal $ LInt 8)]
                      , output = AppVal (DataVal jsIntDC) (LitVal $ LInt 1) }

        ex2 = Example { func = Id (Name "f" Nothing) (TyFun jsIdentType jsIdentType)
                      , input = [AppVal (DataVal jsIntDC) (LitVal $ LInt 90)]
                      , output = AppVal (DataVal jsIntDC) (LitVal $ LInt 2) }
