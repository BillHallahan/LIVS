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
    $ assertBool "Correct nameToString" (nameToString (InternalName "add" (Just 2) Nothing) == "add2")

stringToName1 :: TestTree
stringToName1 = testCase "stringToName Test 1"
    $ assertBool "Correct stringToName" (stringToInternalName "add2" == InternalName "add" (Just 2) Nothing)

stringToName2 :: TestTree
stringToName2 = testCase "stringToName Test 2"
    $ assertBool "Correct stringToName" (stringToInternalName "add" == InternalName "add" Nothing Nothing)

nameGen1 :: TestTree
nameGen1 = testCase "nameGen Test 1"
    $ assertBool "Correct nameGen"
        (fst (freshName (InternalName "g" (Just 1) Nothing) ng) == InternalName "g" (Just 8) Nothing)
    where
        ng = mkNameGen [InternalName "f" (Just 4) Nothing, InternalName "g" (Just 7) Nothing]

nameGen2 :: TestTree
nameGen2 = testCase "nameGen Test 2"
    $ assertBool "Correct nameGen"
        (fst (freshName (InternalName "g" (Just 4) Nothing) ng') == InternalName "g" (Just 9) Nothing)
    where
        ng = mkNameGen [InternalName "f" (Just 4) Nothing, InternalName "g" (Just 7) Nothing]
        (_, ng') = freshName (InternalName "g" (Just 1) Nothing) ng
