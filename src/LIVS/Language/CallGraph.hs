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

-- | Returns all Id's directally called by the given Id
directlyCalls :: Id -> CallGraph -> S.HashSet Id
directlyCalls i (CallGraph cg ti _) =
    S.fromList . map snd . filter ((==) i . fst) 
          . map (\(v1, v2) -> (ti v1, ti v2)) . G.edges $ cg

-- | Gives a list of Id's in post-order
postOrderList :: CallGraph -> [Id]
postOrderList = nub . concatMap (reverse . postOrderList') . dfs
    where
        postOrderList' :: CallTree -> [Id]
        postOrderList' ct = vert ct:concatMap postOrderList' (trees ct)

findVert :: Id -> CallGraph -> Maybe CallTree
findVert i g
    | (t:_) <- mapMaybe (findVertTree i) $ dfs g = Just t
    | otherwise = Nothing

findVertTree :: Id -> CallTree -> Maybe CallTree
findVertTree i ct
    | vert ct == i = Just ct
    | (r:_) <- mapMaybe (findVertTree i) (trees ct) = Just r
    | otherwise = Nothing