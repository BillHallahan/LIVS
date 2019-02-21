module LIVS.LIVS where

import Lava.Language.CallGraph
import Lava.Language.Syntax
import Lava.Language.Typing
import Lava.LIVS.LIVS

import Data.List

import Test.Tasty
import Test.Tasty.HUnit

livsTests :: TestTree
livsTests = testGroup "LIVS" [ synthOrder1
                             , synthOrder2 ]

synthOrder1 :: TestTree
synthOrder1 = testCase "synthOrder 1"
    $ assertBool "Correct synthOrder" (synthOrder1' (toId "z") (toId "f") graph1)

synthOrder2 :: TestTree
synthOrder2 = testCase "synthOrder 2"
    $ assertBool "Correct synthOrder" (synthOrder1' (toId "h") (toId "z") graph1)

synthOrder1' :: Id -> Id -> CallGraph -> Bool
synthOrder1' i1 i2 g =
    let
        ord = synthOrder g
    in
    elemIndex i1 ord < elemIndex i2 ord

graph1 :: CallGraph
graph1 = createCallGraph
    [ (toId "f", [toId "g", toId "h"])
    , (toId "g", [toId "x", toId "h"])
    , (toId "x", [toId "y", toId "z"])
    , (toId "z", [toId "h"])]

toId :: Name -> Id
toId n = Id n (TyFun intType intType)