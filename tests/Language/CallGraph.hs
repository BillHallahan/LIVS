module Language.CallGraph (callGraphTests) where

import LIVS.Language.CallGraph
import LIVS.Language.Syntax
import LIVS.Language.Typing

import qualified Data.HashSet as S
import Data.List

import Test.Tasty
import Test.Tasty.HUnit

callGraphTests :: TestTree
callGraphTests = testGroup "Call Graph" [ dfs1
                                        , reachable1
                                        , reachable2
                                        , directlyCalls1
                                        , findVert1
                                        , findVert2
                                        , postOrderList1
                                        , postOrderList2
                                        , postOrderListAfter1
                                        , postOrderListAfter2
                                        , postOrderListAfter3 ]

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

directlyCalls1 :: TestTree
directlyCalls1 = testCase "directlyCalls Test 1"
    $ assertBool ("Correct directlyCalls" ++ show (directlyCalls (toId "g") graph2))
        (directlyCalls (toId "g") graph2 == 
            S.fromList [toId "x", toId "h"])

postOrderList1 :: TestTree
postOrderList1 = testCase "postOrderList 1"
    $ assertBool "Correct synthOrder" (postOrderList' (toId "z") (toId "f") graph1)

postOrderList2 :: TestTree
postOrderList2 = testCase "postOrderList 2"
    $ assertBool "Correct postOrderList" (postOrderList' (toId "h") (toId "z") graph1)

postOrderList' :: Id -> Id -> CallGraph -> Bool
postOrderList' i1 i2 g =
    let
        ord = postOrderList g
    in
    elemIndex i1 ord < elemIndex i2 ord

postOrderListAfter1 :: TestTree
postOrderListAfter1 = testCase "postOrderListAfter 1"
    $ assertBool "Correct postOrderListAfter1"
        (let
            ord = postOrderListAfter [toId "x"] graph1
         in
         toId "f" `elem` ord && toId "g" `elem` ord && toId "x" `elem` ord
        )

postOrderListAfter2 :: TestTree
postOrderListAfter2 = testCase "postOrderListAfter 2"
    $ assertBool "Correct postOrderListAfter1"
        (let
            ord = postOrderListAfter [toId "x"] graph1
         in
         toId "h" `notElem` ord && toId "y" `notElem` ord
                && toId "z" `notElem` ord
        )

postOrderListAfter3 :: TestTree
postOrderListAfter3 = testCase "postOrderListAfter 3"
    $ assertBool "Correct postOrderListAfter3"
        (let
            ord = postOrderListAfter [toId "g"] graph4
         in
         toId "g" `elem` ord && toId "f" `elem` ord && toId "h" `elem` ord
        )

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

graph4 :: CallGraph
graph4 = createCallGraph
    [ (toId "f", [toId "g"])
    , (toId "h", [toId "g"])]


toId :: String -> Id
toId n = Id (Name n Nothing) (TyFun intType intType)