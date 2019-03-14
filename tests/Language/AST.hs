{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE TemplateHaskell #-}

module Language.AST (astTests) where

import LIVS.Language.AST

import Test.Tasty
import Test.Tasty.HUnit

astTests :: TestTree
astTests = testGroup "AST" [ children1
                           , children2
                           , children3
                           , children4
                           , children5
                           , children6
                           , children7 ]

data E = M (Maybe E)
       | EitherE (Either E E)
       | A E
       | B E E
       | T
       | I Int
       | SymInt WrapInt
       | SymE WrapE
       | L [E]
       deriving Eq

data Wrap a = Wrap a deriving Eq
type WrapInt = Wrap Int
type WrapE = Wrap E

children1 :: TestTree
children1 = testCase "Children Test 1"
    $ assertBool "Children AST" (children (M (Just (A T))) == [A T])

children2 :: TestTree
children2 = testCase "Children Test 2"
    $ assertBool "Children AST" (children (B (A T) T) == [A T, T])

children3 :: TestTree
children3 = testCase "Children Test 3"
    $ assertBool "Children AST" (children T == [])

children4 :: TestTree
children4 = testCase "Children Test 4"
    $ assertBool "Children AST" (children (EitherE (Right (B T T))) == [B T T])

children5 :: TestTree
children5 = testCase "Children Test 5"
    $ assertBool "Children AST" (children (I 8) == [])

children6 :: TestTree
children6 = testCase "Children Test 6"
    $ assertBool "Children AST" (children (SymE (Wrap (A T))) == [A T])

children7 :: TestTree
children7 = testCase "Children Test 7"
    $ assertBool "Children AST" (children (L [A T, B T (I 3)]) == [A T, B T (I 3)])


$(derivingASTWithContainers ''E)