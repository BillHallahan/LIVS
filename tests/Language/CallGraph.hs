module Language.CallGraph where

import Lava.Language.CallGraph

import Test.Tasty
import Test.Tasty.HUnit

callGraphTests :: TestTree
callGraphTests = testGroup "Call Graph" [ dfs1 ]

dfs1 :: TestTree
dfs1 = testCase "DFS Test 1"
    $ assertBool "Correct DFS" (length (dfs graph1) == 1)

findVert1 :: TestTree 
findVert1 = testCase "findVert Test 1"
    $ assertBool "Correct findVert" ( case findVert "h" (head $ dfs graph1) of
                                        Just t -> vert t == "h"
                                        Nothing -> False )

graph1 :: CallGraph
graph1 = createCallGraph
    [("f", ["g", "h"]), ("g", ["x", "h"]), ("x", ["y", "z"]), ("z", ["h"])]