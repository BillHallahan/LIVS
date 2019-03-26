module UI.Parse (uiParseTests) where

import LIVS.Language.Syntax
import LIVS.Target.JavaScript.Interface
import LIVS.Target.JavaScript.JSIdentifier
import LIVS.UI.Parse

import Test.Tasty
import Test.Tasty.HUnit

uiParseTests :: TestTree
uiParseTests = testGroup "UI Parse" [ parseExample1 ]

parseExample1 :: TestTree
parseExample1 = testCase "parseExample Test 1"
    $ assertBool "Correct parseExample" 
            (parseExample jsJSONToVal "@pbe (constraint (= (f 3) 20))" == Just ex)
    where
        ex = Example { func = Id (Name "f" Nothing) (TyFun jsIdentType jsIdentType)
                     , input = [AppVal (DataVal jsIntDC) (LitVal $ LInt 3)]
                     , output = AppVal (DataVal jsIntDC) (LitVal $ LInt 20) }
