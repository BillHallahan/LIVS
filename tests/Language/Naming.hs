module Language.Naming (namingTests) where

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
    $ assertBool "Correct nameToString" (nameToString (Name "add" (Just 2)) == "add2")

stringToName1 :: TestTree
stringToName1 = testCase "stringToName Test 1"
    $ assertBool "Correct stringToName" (stringToName "add2" == Name "add" (Just 2))

stringToName2 :: TestTree
stringToName2 = testCase "stringToName Test 2"
    $ assertBool "Correct stringToName" (stringToName "add" == Name "add" Nothing)

nameGen1 :: TestTree
nameGen1 = testCase "nameGen Test 1"
    $ assertBool "Correct nameGen"
        (fst (freshName (Name "g" (Just 1)) ng) == Name "g" (Just 8))
    where
        ng = mkNameGen [Name "f" (Just 4), Name "g" (Just 7)]

nameGen2 :: TestTree
nameGen2 = testCase "nameGen Test 2"
    $ assertBool "Correct nameGen"
        (fst (freshName (Name "g" (Just 4)) ng') == Name "g" (Just 9))
    where
        ng = mkNameGen [Name "f" (Just 4), Name "g" (Just 7)]
        (_, ng') = freshName (Name "g" (Just 1)) ng
