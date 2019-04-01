module Language.Expr where

import LIVS.Language.Syntax
import LIVS.Language.Expr
import LIVS.Language.Typing

import Test.Tasty
import Test.Tasty.HUnit

exprTests :: TestTree
exprTests = testGroup "Expr" [ mkLams1
                             , mkApp1 ]

mkLams1 :: TestTree
mkLams1 = testCase "mkLams1 1"
    $ assertBool "Correct Lams"
        (case mkLams [i1, i2] e1 of
            Lam i1' (Lam i2' _) -> i1 == i1' && i2 == i2'
            _ -> False
        )

mkApp1 :: TestTree
mkApp1 = testCase "mkApp1 1"
    $ assertBool "Correct App" (mkApp [e1, e2, e3] == App (App e1 e2) e3)

e1 :: Expr
e1 = Var (Id (Name "+" Nothing) (TyFun intType (TyFun intType intType)))

e2 :: Expr
e2 = Var i1

e3 :: Expr
e3 = Var i2

i1 :: Id
i1 = Id (Name "x" Nothing) intType

i2 :: Id
i2 = Id (Name "y" Nothing) intType