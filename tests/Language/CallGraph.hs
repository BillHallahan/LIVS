module Language.CallGraph where

import Lava.Language.CallGraph
import Lava.Language.Syntax

import qualified Data.Set as S

import Test.Tasty
import Test.Tasty.HUnit

callGraphTests :: TestTree
callGraphTests = testGroup "Call Graph" [ dfs1
                                        , reachable1
                                        , findVert1
                                        , findVert2 ]

dfs1 :: TestTree
dfs1 = testCase "DFS Test 1"
    $ assertBool "Correct DFS" (length (dfs graph1) == 1)

reachable1 :: TestTree
reachable1 = testCase "reachable Test 1"
    $ assertBool "Correct reachable" (reachable "f" graph2 == S.fromList ["f", "h", "p", "q", "k"])


findVert1 :: TestTree 
findVert1 = testCase "findVert Test 1"
    $ assertBool "Correct findVert" (testFindVert "g" graph1)

findVert2 :: TestTree 
findVert2 = testCase "findVert Test 1"
    $ assertBool "Correct findVert" (testFindVert "h" graph1)

testFindVert :: Name -> CallGraph -> Bool
testFindVert n g = fmap vert (findVert n g) == Just n

graph1 :: CallGraph
graph1 = createCallGraph
    [("f", ["g", "h"]), ("g", ["x", "h"]), ("x", ["y", "z"]), ("z", ["h"])]

graph2 :: CallGraph
graph2 = createCallGraph
    [("f", ["h"]), ("g", ["x", "h"]), ("x", ["y", "z"]), ("z", ["h"]), ("h", ["p", "q"]), ("p", ["k"])]