module Language.CallGraph (callGraphTests) where

import LIVS.Language.CallGraph
import LIVS.Language.Syntax
import LIVS.Language.Typing

import qualified Data.HashSet as S

import Test.Tasty
import Test.Tasty.HUnit

callGraphTests :: TestTree
callGraphTests = testGroup "Call Graph" [ dfs1
                                        , reachable1
                                        , reachable2
                                        , findVert1
                                        , findVert2 ]

dfs1 :: TestTree
dfs1 = testCase "DFS Test 1"
    $ assertBool "Correct DFS" (length (dfs graph1) == 1)

reachable1 :: TestTree
reachable1 = testCase "reachable Test 1"
    $ assertBool "Correct reachable" 
        (reachable (toId "f") graph2 == 
            S.fromList [toId "f", toId "h", toId "p", toId "q", toId "k"])

reachable2 :: TestTree
reachable2 = testCase "reachable Test 2"
    $ assertBool "Correct reachable" 
        (reachable (toId "f") graph3 == 
            S.fromList [toId "f", toId "e"])

findVert1 :: TestTree 
findVert1 = testCase "findVert Test 1"
    $ assertBool "Correct findVert" (testFindVert (toId "g") graph1)

findVert2 :: TestTree 
findVert2 = testCase "findVert Test 1"
    $ assertBool "Correct findVert" (testFindVert (toId "h") graph1)

testFindVert :: Id -> CallGraph -> Bool
testFindVert i g = fmap vert (findVert i g) == Just i

graph1 :: CallGraph
graph1 = createCallGraph
    [ (toId "f", [toId "g", toId "h"])
    , (toId "g", [toId "x", toId "h"])
    , (toId "x", [toId "y", toId "z"])
    , (toId "z", [toId "h"])]

graph2 :: CallGraph
graph2 = createCallGraph
    [ (toId "f", [toId "h"])
    , (toId "g", [toId "x", toId "h"])
    , (toId "x", [toId "y", toId "z"])
    , (toId "z", [toId "h"])
    , (toId "h", [toId "p", toId "q"])
    , (toId "p", [toId "k"])]

graph3 :: CallGraph
graph3 = createCallGraph [(toId "f", [toId "e"])]

toId :: Name -> Id
toId n = Id n (TyFun intType intType)