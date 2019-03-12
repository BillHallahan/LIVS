{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE TemplateHaskell #-}

module LIVS.Language.AST ( AST (..)
                         , ASTContainer (..)
                         , evalChildren
                         , eval
                         , evalContainedASTs

                         , derivingAST
                         , derivingASTContainer ) where

import Language.Haskell.TH as TH
import Language.Haskell.TH.Syntax as TH

import Control.Monad
import Data.Maybe

class AST t where
    children :: t -> [t]

class ASTContainer c t where
    containedASTs :: c -> [t]

instance ASTContainer c t => ASTContainer [c] t where
    containedASTs = concatMap containedASTs

instance AST t => ASTContainer t t where
    containedASTs t = [t]

instance (ASTContainer a t, ASTContainer b t) => ASTContainer (a, b) t where
    containedASTs (a, b) = containedASTs a ++ containedASTs b

-- | Evaluates all children of the given AST node with the given monoid,
-- and `mconcat`s the results
evalChildren :: (AST t, Monoid a) => (t -> a) -> t -> a
evalChildren f = mconcat . map f . children

-- | Recursively runs the given function on each node, top down. Uses mappend
-- to combine the results after evaluation of the entire tree.
eval :: (AST t, Monoid a) => (t -> a) -> t -> a
eval f t = go t
    where
        go t' = f t' `mappend` evalChildren go t'

-- | Runs a function on all the ASTs in the container, and uses mappend to
-- combine the results.
evalContainedASTs :: (ASTContainer t e, Monoid a) => (e -> a) -> t -> a
evalContainedASTs f = mconcat . map f . containedASTs

--------------------------------------------
-- Template Haskell
--------------------------------------------

derivingAST :: TH.Name -- ^ The name of the datatype to walk 
            -> Q [Dec]
derivingAST ty = do
    (TyConI tyCon) <- reify ty
    let (tyConName, tyVars, cs) = tyConData tyCon

    let instanceType = conT ''AST `appT` applyTypes tyConName tyVars

    sequence [instanceD (return []) instanceType [genChildren tyConName cs]]

genChildren :: TH.Name -> [Con] -> Q Dec
genChildren tcn cs = do funD 'children (map (genChildrenClause tcn) cs)

genChildrenClause :: TH.Name -> Con -> Q Clause
genChildrenClause tcn (NormalC name fieldTypes) = do
    fieldNames <- replicateM (length fieldTypes) (newName "x")
    let pats = [conP name (map varP fieldNames)]

        body = return . NormalB . concatLists . catMaybes
                =<< mapM (fieldChildren tcn) (zip fieldNames fieldTypes)

    clause pats body []
genChildrenClause _ _ = error "genChildrenClause: Bad Con"

fieldChildren :: TH.Name -> (TH.Name, StrictType) -> Q (Maybe Exp)
fieldChildren tcn (n, (_, t)) = do
    case t of
        a@(AppT _ _) -> return . Just =<< varE 'containedASTs `appE` (varE n)
        ConT tcn' | tcn == tcn' -> return . Just =<< listE [varE n]
                  | otherwise ->
                        return . Just =<< varE 'containedASTs `appE` (varE n)
        (VarT _) -> return . Just =<< varE 'containedASTs `appE` (varE n)
        _ -> return Nothing

derivingASTContainer :: TH.Name -- ^ The name of the datatype to walk 
                     -> TH.Name -- ^ The name of the AST datatype to extract
                     -> Q [Dec]
derivingASTContainer ty ty_ex = do
    (TyConI tyCon) <- reify ty
    let (tyConName, tyVars, cs) = tyConData tyCon 

    (TyConI tyConEx) <- reify ty_ex
    let (tyConNameEx, tyVarsEx, _) = tyConData tyConEx

    let instanceType = conT ''ASTContainer
                        `appT` applyTypes tyConName tyVars
                        `appT` applyTypes tyConNameEx tyVarsEx
    let consInstanceType =
            if null tyVars
                then instanceType
                else forallT [] 
                        (mapM (\tv -> conT ''ASTContainer `appT` (toType tv) `appT` (conT tyConNameEx) ) tyVars) 
                        instanceType 

    sequence [instanceD (return []) consInstanceType [genContainedASTs tyConNameEx cs]]
    where
        toType (PlainTV name) = varT name
        toType (KindedTV name _) = varT name

genContainedASTs :: TH.Name -> [Con] -> Q Dec
genContainedASTs tcn cs = do funD 'containedASTs (map (genContainedASTsClause tcn) cs)

genContainedASTsClause :: TH.Name -> Con -> Q Clause
genContainedASTsClause tcn (NormalC name fieldTypes) =
    genContainedASTsClause' tcn name fieldTypes
genContainedASTsClause tcn (RecC name fieldTypes) =
    genContainedASTsClause' tcn name $ map varBangTypeToBangType fieldTypes
genContainedASTsClause tcn (InfixC fieldType1 name fieldType2) =
    genContainedASTsClause' tcn name [fieldType1, fieldType2]
genContainedASTsClause _ _ = error "genContainedASTsClause: Invalid Data Constructor"

genContainedASTsClause' :: TH.Name -> TH.Name -> [BangType] -> Q Clause
genContainedASTsClause' tcn name fieldTypes = do
    fieldNames <- replicateM (length fieldTypes) (newName "x")
    let pats = [conP name (map varP fieldNames)]
        body = return . NormalB . concatLists . catMaybes
                =<< mapM (fieldChildren tcn) (zip fieldNames fieldTypes)

    clause pats body []

applyTypes :: TH.Name -> [TyVarBndr] -> TypeQ
applyTypes tyConName tyVars = foldl applyType (conT tyConName) tyVars
    where
        applyType t (PlainTV name)    = appT t (varT name)
        applyType t (KindedTV name _) = appT t (varT name)

varBangTypeToBangType :: VarBangType -> BangType
varBangTypeToBangType (_, n, t) = (n, t)

tyConData :: Dec -> (Name, [TyVarBndr], [Con])
tyConData (DataD _ nm tyVars _ cs _) = (nm, tyVars, cs)
tyConData (NewtypeD _ nm tyVars _ c _) = (nm, tyVars, [c])
tyConData _ = error "derivingAST: tyCon may not be a type synonym."

concatLists :: [Exp] -> Exp
concatLists = foldl (\e1 e2 -> (VarE '(++)) `AppE` e1 `AppE` e2) (ConE '[])
