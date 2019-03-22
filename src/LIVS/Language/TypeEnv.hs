module LIVS.Language.TypeEnv ( TypeEnv
                             , ADTSpec (..)
                             , SelectorDC (..)
                             , NamedType (..)
                             , empty
                             , insert
                             , lookup
                             , keys
                             , elems
                             , fromList
                             , toList

                             , selectorDCToDC

                             , mergeConstructors
                             , mergeSelectorsAndTesters
                             , mergeSelectors
                             , mergeTesters ) where

import qualified LIVS.Language.Heap as H
import LIVS.Language.Naming
import LIVS.Language.Syntax
import LIVS.Language.Typing

import qualified Data.HashMap.Lazy as M

import Prelude hiding (lookup)

-- | Associates Algebraic Data Constructor Names to the corresponding constructors.
newtype TypeEnv = TypeEnv { unTypeEnv :: M.HashMap Name ADTSpec }
                  deriving (Show, Read)

newtype ADTSpec = ADTSpec { selectors :: [SelectorDC] } deriving (Show, Read)

-- | A Data Constructor with named selectors for each type argument
-- The NamedType list is the arguments to the constructor
data SelectorDC = SelectorDC Name [NamedType] deriving (Show, Read)

data NamedType = NamedType { namedTypeName :: Name
                           , namedTypeType :: Type}
                           deriving (Show, Read)

-- TypeEnv functions

empty :: TypeEnv
empty = TypeEnv M.empty

insert :: Name -> ADTSpec -> TypeEnv -> TypeEnv
insert n a = TypeEnv . M.insert n a . unTypeEnv

lookup :: Name -> TypeEnv -> Maybe ADTSpec
lookup n = M.lookup n . unTypeEnv

keys :: TypeEnv -> [Name]
keys = M.keys . unTypeEnv

elems :: TypeEnv -> [ADTSpec]
elems = M.elems . unTypeEnv

fromList :: [(Name, ADTSpec)] -> TypeEnv
fromList = TypeEnv . M.fromList

toList :: TypeEnv -> [(Name, ADTSpec)]
toList = M.toList . unTypeEnv

-- SelectorDC Functions

selectorDCToDC :: Name -> SelectorDC -> DC
selectorDCToDC tn (SelectorDC n nt) =
    DC n . mkTyFun $ map namedTypeType nt ++ [TyCon tn TYPE]

-- Various

-- | Merges the constructors from a TypeEnv into a Heap, as Primitives
mergeConstructors :: TypeEnv -> H.Heap -> H.Heap
mergeConstructors tenv h =
    let
        sels = map (\(n, spec) -> (n, selectors spec)) $ toList tenv
    in
    foldr (uncurry mergeConstructor) h sels
    where
        mergeConstructor :: Name -> [SelectorDC] -> H.Heap -> H.Heap
        mergeConstructor n sels h' = foldr (mergeConstructor' n) h' sels

        mergeConstructor' :: Name -> SelectorDC -> H.Heap -> H.Heap
        mergeConstructor' n sel =
            case selectorDCToDC n sel of
                DC n t -> H.insertPrimitive n t

mergeSelectorsAndTesters :: TypeEnv -> H.Heap -> H.Heap
mergeSelectorsAndTesters tenv = mergeSelectors tenv . mergeTesters tenv

-- | Merges the selectors from a TypeEnv into a Heap, as Primitives
mergeSelectors :: TypeEnv -> H.Heap -> H.Heap
mergeSelectors tenv h =
    let
        sels = map (\(n, spec) -> (n, selectors spec)) $ toList tenv
    in
    foldr (uncurry mergeSelector) h sels
    where
        mergeSelector  :: Name -> [SelectorDC] -> H.Heap -> H.Heap
        mergeSelector n sels h' = foldr (mergeSelector' n) h' sels

        mergeSelector' :: Name -> SelectorDC -> H.Heap -> H.Heap
        mergeSelector' n (SelectorDC _ nt) h' =
            let
                t = TyCon n TYPE
                ins_names_tys = map (\(NamedType n' t') -> (n', TyFun t t')) nt
            in
            foldr (uncurry H.insertPrimitive) h' ins_names_tys

mergeTesters :: TypeEnv -> H.Heap -> H.Heap
mergeTesters tenv h =
    let
        sels = map (\(n, spec) -> (n, selectors spec)) $ toList tenv
    in
    foldr (uncurry mergeTester) h sels
    where
        mergeTester  :: Name -> [SelectorDC] -> H.Heap -> H.Heap
        mergeTester n sels h' = foldr (mergeTester' n) h' sels

        mergeTester' :: Name -> SelectorDC -> H.Heap -> H.Heap
        mergeTester' tn (SelectorDC dcn _) h' =
            let
                t = TyCon tn TYPE
                ins_name = Name ("is" ++ nameToString dcn) Nothing
                func_ty = TyFun t boolType
            in
            H.insertPrimitive ins_name func_ty  h'