module Typing (typingTests) where

import Lava.Language.Syntax
import Lava.Language.Typing

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
e1 = Lam (Id "x" intType) (Var (Id "x" intType))

exprType2 :: TestTree
exprType2 = testCase "Expr Type 2"
    $ assertBool "Correct type" (typeOf e2 == intType)

e2 :: Expr
e2 = App (Lam (Id "x" intType) (Lit (LInt 0))) (Lit (LInt 1))

mkFunTyTest :: TestTree
mkFunTyTest = testCase "mkTyFun"
    $ assertBool "mkTyFun" (mkTyFun [intType, TyCon "Float" TYPE] == TyFun intType (TyCon "Float" TYPE))