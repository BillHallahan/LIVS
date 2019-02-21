{-# LANGUAGE TupleSections #-}

module LIVS.Language.CallGraph ( CallGraph
                               , CallForest
                               , CallTree
                               , createCallGraph
                               , dfs
                               , vert
                               , trees
                               , reachable
                               , findVert) where

import LIVS.Language.Syntax

import qualified Data.Graph as G
import Data.List
import Data.Maybe
import qualified Data.HashSet as S

data CallGraph = CallGraph G.Graph (G.Vertex -> Id)

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

        (g, f, _) = G.graphFromEdges . map (\(i, is) -> (i, idName i, map idName is)) $ iss'
    in
    CallGraph g (fst3 . f)
    where
        fst3 (x, _, _) = x

type CallForest = [CallTree]

dfs :: CallGraph -> CallForest
dfs (CallGraph g f) = map (flip CallTree f) (G.dff g)

data CallTree = CallTree (G.Tree G.Vertex) (G.Vertex -> Id)

vert :: CallTree -> Id
vert (CallTree (G.Node a _) f) = f a 

trees :: CallTree -> CallForest
trees (CallTree (G.Node _ ts) f) = map (flip CallTree f) ts

-- | Returns all Id's (verts) reachable from the given Id in the CallGraph
reachable :: Id -> CallGraph -> S.HashSet Id
reachable n cg = maybe S.empty id (fmap reachableTree $ findVert n cg)

-- | Returns all Id's (verts) reachable from the given CallTree
reachableTree :: CallTree -> S.HashSet Id
reachableTree t =
    foldr S.union (S.singleton $ vert t) $ map reachableTree (trees t)

findVert :: Id -> CallGraph -> Maybe CallTree
findVert n g
    | (t:_) <- mapMaybe (findVertTree n) $ dfs g = Just t
    | otherwise = Nothing

findVertTree :: Id -> CallTree -> Maybe CallTree
findVertTree n ct
    | vert ct == n = Just ct
    | (r:_) <- mapMaybe (findVertTree n) (trees ct) = Just r
    | otherwise = Nothing