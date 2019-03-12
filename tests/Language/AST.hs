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
                           , children5 ]

data E = M (Maybe E)
       | EitherE (Either E E)
       | A E
       | B E E
       | T
       | I Int
       deriving Eq

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

$(derivingASTWithContainers ''E)