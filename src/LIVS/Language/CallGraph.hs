{-# LANGUAGE TupleSections #-}

module LIVS.Language.CallGraph ( CallGraph
                               , CallForest
                               , CallTree
                               , createCallGraph
                               , dfs
                               , vert
                               , trees
                               , reachable
                               , directlyCalls
                               , postOrderList
                               , postOrderListAfter
                               , path
                               , findVert) where

import LIVS.Language.Syntax

import qualified Data.Graph as G
import Data.List
import Data.Maybe
import qualified Data.HashSet as S

data CallGraph =
    CallGraph G.Graph (G.Vertex -> Id) (Id -> Maybe G.Vertex)

-- | Takes a list, mapping functions to the functions they call
createCallGraph :: [(Id, [Id])] -> CallGraph
createCallGraph iss =
    let
        -- We want to make sure that all names are included as nodes, even if
        -- they are only in the outlist.  Data.Graph does not guarantee this,
        -- so we do it ourselves.
        iss_f = map fst iss 
        iss_s = nub $ concatMap snd iss
        iss_s' = iss_s \\ iss_f
        iss' = iss ++ map (,[]) iss_s'

        (g, ti, tv) = G.graphFromEdges . map (\(i, is) -> (i, idName i, map idName is)) $ iss'
    in
    CallGraph g (fst3 . ti) (tv . idName)
    where
        fst3 (x, _, _) = x

type CallForest = [CallTree]

data CallTree = CallTree (G.Tree G.Vertex) (G.Vertex -> Id) (Id -> Maybe G.Vertex)

dfs :: CallGraph -> CallForest
dfs (CallGraph g ti tv) = map (\x  -> CallTree x ti tv) (G.dff g)

vert :: CallTree -> Id
vert (CallTree (G.Node a _) f _) = f a 

trees :: CallTree -> CallForest
trees (CallTree (G.Node _ ts) ti tv) = map (\x  -> CallTree x ti tv) ts

-- | Returns all Id's (verts) reachable from the given Id in the CallGraph
reachable :: Id -> CallGraph -> S.HashSet Id
reachable n (CallGraph cg ti tv) =
    case tv n of
        Just v -> S.fromList . map ti $ G.reachable cg v
        Nothing -> S.empty

-- | Returns all Id's directly called by the given Id
directlyCalls :: Id -> CallGraph -> S.HashSet Id
directlyCalls i (CallGraph cg ti _) =
    S.fromList . map snd . filter ((==) i . fst) 
          . map (\(v1, v2) -> (ti v1, ti v2)) . G.edges $ cg

-- | Gives a list of Id's in post-order
postOrderList :: CallGraph -> [Id]
postOrderList (CallGraph cg ti _) = reverse . map ti $ G.topSort cg

-- | The same as postOrderListTree, except cuts off the beginning of each branch
-- up to the first occurence of an element in the input list
postOrderListAfter ::  [Id] -> CallGraph -> [Id]
postOrderListAfter is cg = filter (\i1 -> any (path cg i1) is) . postOrderList $ cg

-- | Returns true if the second Id reachable from the first
path :: CallGraph -> Id -> Id -> Bool
path (CallGraph g _ tv) i1 i2 =
    case (tv i1, tv i2) of
        (Just i1', Just i2') -> G.path g i1' i2'
        _ -> False

findVert :: Id -> CallGraph -> Maybe CallTree
findVert i g
    | (t:_) <- mapMaybe (findVertTree i) $ dfs g = Just t
    | otherwise = Nothing

findVertTree :: Id -> CallTree -> Maybe CallTree
findVertTree i ct
    | vert ct == i = Just ct
    | (r:_) <- mapMaybe (findVertTree i) (trees ct) = Just r
    | otherwise = Nothing