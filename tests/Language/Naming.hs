module Language.Naming (namingTests) where

import LIVS.Language.Syntax
import LIVS.Language.Naming

import Test.Tasty
import Test.Tasty.HUnit

namingTests :: TestTree
namingTests = testGroup "Naming" [ nameToString1
                                 , stringToName1
                                 , stringToName2
                                 , nameGen1
                                 , nameGen2 ]

nameToString1 :: TestTree
nameToString1 = testCase "nameToString Test 1"
    $ assertBool "Correct nameToString" (nameToString (Name Ident "add" (Just 2)) == "add")

stringToName1 :: TestTree
stringToName1 = testCase "stringToName Test 1"
    $ assertBool "Correct stringToName" (stringToName Ident "add2" == Name Ident "add" (Just 2))

stringToName2 :: TestTree
stringToName2 = testCase "stringToName Test 2"
    $ assertBool "Correct stringToName" (stringToName Ident "add" == Name Ident "add" Nothing)

nameGen1 :: TestTree
nameGen1 = testCase "nameGen Test 1"
    $ assertBool "Correct nameGen"
        (fst (freshName (Name Ident "g" (Just 1)) ng) == Name Ident "g" (Just 8))
    where
        ng = mkNameGen [Name Ident "f" (Just 4), Name Ident "g" (Just 7)]

nameGen2 :: TestTree
nameGen2 = testCase "nameGen Test 2"
    $ assertBool "Correct nameGen"
        (fst (freshName (Name Ident "g" (Just 4)) ng') == Name Ident "g" (Just 9))
    where
        ng = mkNameGen [Name Ident "f" (Just 4), Name Ident "g" (Just 7)]
        (_, ng') = freshName (Name Ident "g" (Just 1)) ng
