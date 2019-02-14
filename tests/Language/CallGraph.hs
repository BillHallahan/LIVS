module Language.CallGraph where

import Lava.Language.CallGraph
import Lava.Language.Syntax

import Data.Maybe

import Test.Tasty
import Test.Tasty.HUnit

callGraphTests :: TestTree
callGraphTests = testGroup "Call Graph" [ dfs1
                                        , findVert1
                                        , findVert2 ]

dfs1 :: TestTree
dfs1 = testCase "DFS Test 1"
    $ assertBool "Correct DFS" (length (dfs graph1) == 1)

findVert1 :: TestTree 
findVert1 = testCase "findVert Test 1"
    $ assertBool "Correct findVert" (testFindVert "g" graph1)

findVert2 :: TestTree 
findVert2 = testCase "findVert Test 1"
    $ assertBool "Correct findVert" (testFindVert "h" graph1)

testFindVert :: Name -> CallGraph -> Bool
testFindVert n g
    | (t:_) <- mapMaybe (findVert n) dg = vert t == n
    | otherwise = False
    where
        dg = dfs g

graph1 :: CallGraph
graph1 = createCallGraph
    [("f", ["g", "h"]), ("g", ["x", "h"]), ("x", ["y", "z"]), ("z", ["h"])]