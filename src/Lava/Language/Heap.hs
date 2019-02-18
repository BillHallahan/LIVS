module Lava.Language.Heap ( Heap
                          , empty
                          , fromList
                          , insert
                          , lookup
                          , map
                          , map'
                          , mapWithKey
                          , mapWithKey'
                          , filter
                          , filterWithKey
                          , keys
                          , toHashMap
                          , toList ) where

import Lava.Language.Syntax

import qualified Data.HashMap.Lazy as M
import Prelude hiding (map, filter, lookup)

newtype Heap = Heap { unHeap :: M.HashMap Name Expr }

empty :: Heap
empty = Heap M.empty

fromList :: [(Name, Expr)] -> Heap
fromList = Heap . M.fromList

insert :: Name -> Expr -> Heap -> Heap
insert n e = Heap . M.insert n e . unHeap

lookup :: Name -> Heap -> Maybe Expr
lookup n = M.lookup n . unHeap

map :: (Expr -> Expr) -> Heap -> Heap
map f = Heap . M.map f . unHeap

map' :: (Expr -> v) -> Heap -> M.HashMap Name v
map' f = M.map f . unHeap

mapWithKey :: (Name -> Expr -> Expr) -> Heap -> Heap
mapWithKey f = Heap . M.mapWithKey f . unHeap

mapWithKey' :: (Name -> Expr -> v) -> Heap -> M.HashMap Name v
mapWithKey' f = M.mapWithKey f . unHeap

filter :: (Expr -> Bool) -> Heap -> Heap
filter p = Heap . M.filter p . unHeap 

filterWithKey :: (Name -> Expr -> Bool) -> Heap -> Heap
filterWithKey p = Heap . M.filterWithKey p . unHeap

keys :: Heap -> [Name]
keys = M.keys . unHeap

toHashMap :: Heap -> M.HashMap Name Expr
toHashMap = unHeap

toList :: Heap -> [(Name, Expr)]
toList = M.toList . unHeap