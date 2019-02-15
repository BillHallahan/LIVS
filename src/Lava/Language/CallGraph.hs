{-# LANGUAGE TupleSections #-}

module Lava.Language.CallGraph ( CallGraph
                               , CallForest
                               , CallTree
                               , createCallGraph
                               , dfs
                               , vert
                               , trees
                               , reachable
                               , findVert) where

import Lava.Language.Syntax

import qualified Data.Graph as G
import Data.List
import Data.Maybe
import qualified Data.Set as S

data CallGraph = CallGraph G.Graph (G.Vertex -> Name)

-- | Takes a list, mapping functions to the functions they call
createCallGraph :: [(Name, [Name])] -> CallGraph
createCallGraph nss =
    let
        -- We want to make sure that all names are included as nodes, even if
        -- they are only in the outlist.  Data.Graph does not guarantee this,
        -- so we do it ourselves.
        nss_f = map fst nss 
        nss_s = nub $ concatMap snd nss
        nss_s' = nss_s \\ nss_f
        nss' = nss ++ map (,[]) nss_s'

        (g, f, _) = G.graphFromEdges . map (\(n, ns) -> ((), n, ns)) $ nss'
    in
    CallGraph g (mid . f)
    where
        mid (_, x, _) = x

type CallForest = [CallTree]

dfs :: CallGraph -> CallForest
dfs (CallGraph g f) = map (flip CallTree f) (G.dff g)

data CallTree = CallTree (G.Tree G.Vertex) (G.Vertex -> Name)

vert :: CallTree -> Name
vert (CallTree (G.Node a _) f) = f a 

trees :: CallTree -> CallForest
trees (CallTree (G.Node _ ts) f) = map (flip CallTree f) ts

-- | Returns all Name's (verts) reachable from the given Name in the CallGraph
reachable :: Name -> CallGraph -> S.Set Name
reachable n cg = maybe S.empty id (fmap reachableTree $ findVert n cg)

-- | Returns all Name's (verts) reachable from the given CallTree
reachableTree :: CallTree -> S.Set Name
reachableTree t =
    foldr S.union (S.singleton $ vert t) $ map reachableTree (trees t)

findVert :: Name -> CallGraph -> Maybe CallTree
findVert n g
    | (t:_) <- mapMaybe (findVertTree n) $ dfs g = Just t
    | otherwise = Nothing

findVertTree :: Name -> CallTree -> Maybe CallTree
findVertTree n ct
    | vert ct == n = Just ct
    | (r:_) <- mapMaybe (findVertTree n) (trees ct) = Just r
    | otherwise = Nothing