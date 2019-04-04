-- Tracks when/how a single component function has been broken up into multiple
-- internal functions
module LIVS.Language.SubFunctions ( SubFunctions
                                  , empty
                                  , fromHeap
                                  , insert
                                  , lookup
                                  , lookupName
                                  , lookupAllNames
                                  , lookupAllNamesDefSingleton
                                  , lookupNameInputType
                                  , keys ) where

import qualified LIVS.Language.Heap as H
import LIVS.Language.Syntax
import LIVS.Language.Typing

import qualified Data.HashMap.Lazy as M
import qualified Data.List as L
import Data.Maybe
import Data.Tuple

import Prelude hiding (lookup)

newtype SubFunctions = SubFunctions { unSubFunctions :: M.HashMap Name (M.HashMap Type Name)}
                       deriving (Eq, Show, Read)

empty :: SubFunctions
empty = SubFunctions M.empty

fromHeap :: H.Heap -> SubFunctions
fromHeap h =
    let
        ks = H.keys h
        nothing_ks = filter (\(Name _ _ mi) -> isNothing mi) ks

        hs = H.toList h
        sf = map (\n@(Name _ n1 _) -> 
                    ( n
                    , M.fromList
                      . map (\(n2', e) -> (typeOf e, n2'))
                      $ filter (\(Name _ n2 mi, _) -> n1 == n2 && isJust mi) hs
                    )
                 ) nothing_ks
        sf' = filter (not . null . snd ) sf
    in
    SubFunctions $ M.fromList sf'

insert :: Name -> Type -> Name -> SubFunctions -> SubFunctions
insert n t fn (SubFunctions sub)
    | Just ty_m <- M.lookup n sub = SubFunctions $ M.insert n (M.insert t fn ty_m) sub
    | otherwise = SubFunctions $ M.insert n (M.singleton t fn) sub

lookup :: Name -> SubFunctions -> M.HashMap Type Name
lookup n (SubFunctions s)
    | Just tn <- M.lookup n s = tn
    | otherwise = M.empty

lookupMaybe :: Name -> SubFunctions -> Maybe (M.HashMap Type Name)
lookupMaybe n (SubFunctions s) = M.lookup n s

lookupName :: Name -> Type -> SubFunctions -> Maybe Name
lookupName n t (SubFunctions s)
    | Just tn <- M.lookup n s = M.lookup t tn
    | otherwise = Nothing

lookupAllNames :: [Name] -> SubFunctions -> [Name]
lookupAllNames ns sub = concatMap (M.elems . flip lookup sub) ns

lookupAllNamesDefSingleton :: [Name] -> SubFunctions -> [Name]
lookupAllNamesDefSingleton ns sub =
    concatMap (\n -> case lookupMaybe n sub of
                    Just hm -> M.elems hm
                    Nothing -> [n]) ns

lookupNameInputType :: Name -> Type -> SubFunctions -> Maybe (Name, Type)
lookupNameInputType n t (SubFunctions s)
    | Just tn <- M.lookup n s =
        fmap swap . L.find (\(t', _) -> unTyFun t == argTypes (PresType t')) $ M.toList tn
    | otherwise = Nothing

keys :: SubFunctions -> [Name]
keys = M.keys . unSubFunctions