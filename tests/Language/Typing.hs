module Language.Typing (typingTests) where

import LIVS.Language.Syntax
import LIVS.Language.Typing

import Test.Tasty
import Test.Tasty.HUnit

typingTests :: TestTree
typingTests = testGroup "Typing" [ exprType1
                                 , exprType2
                                 , mkFunTyTest ]

exprType1 :: TestTree
exprType1 = testCase "Expr Type 1"
    $ assertBool "Correct type" (typeOf e1 == TyFun intType intType)

e1 :: Expr
e1 = Lam (Id xN intType) (Var (Id xN intType))

exprType2 :: TestTree
exprType2 = testCase "Expr Type 2"
    $ assertBool "Correct type" (typeOf e2 == intType)

e2 :: Expr
e2 = App (Lam (Id xN intType) (Lit (LInt 0))) (Lit (LInt 1))

mkFunTyTest :: TestTree
mkFunTyTest = testCase "mkTyFun"
    $ assertBool "mkTyFun" (mkTyFun [intType, TyCon floatN TYPE] == TyFun intType (TyCon floatN TYPE))

xN :: Name
xN = Name "x" Nothing

floatN :: Name
floatN = Name "Float" Nothing