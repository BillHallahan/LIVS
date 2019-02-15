module LIVS.LIVS where

import Lava.Language.CallGraph
import Lava.Language.Syntax
import Lava.LIVS.LIVS

import Data.List

import Test.Tasty
import Test.Tasty.HUnit

livsTests :: TestTree
livsTests = testGroup "LIVS" [ synthOrder1
                             , synthOrder2 ]

synthOrder1 :: TestTree
synthOrder1 = testCase "synthOrder 1"
    $ assertBool "Correct synthOrder" (synthOrder1' "z" "f" graph1)

synthOrder2 :: TestTree
synthOrder2 = testCase "synthOrder 2"
    $ assertBool "Correct synthOrder" (synthOrder1' "h" "z" graph1)

synthOrder1' :: Name -> Name -> CallGraph -> Bool
synthOrder1' n1 n2 g =
    let
        ord = synthOrder g
    in
    elemIndex n1 ord < elemIndex n2 ord

graph1 :: CallGraph
graph1 = createCallGraph
    [("f", ["g", "h"]), ("g", ["x", "h"]), ("x", ["y", "z"]), ("z", ["h"])]
