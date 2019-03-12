{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE TemplateHaskell #-}

module LIVS.Language.AST ( AST (..)
                         , ASTContainer (..)
                         , evalChildren
                         , eval
                         , evalContainedASTs
                         , evalASTs

                         , derivingAST
                         , derivingASTContainer
                         , derivingASTWithContainers ) where

import Language.Haskell.TH as TH
import Language.Haskell.TH.Syntax as TH

import Control.Monad
import Data.List
import Data.Maybe
import qualified Data.Set as S

class AST t where
    children :: t -> [t]

class AST t => ASTContainer c t where
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

-- | Runs `eval` on all the ASTs in the container, and uses mappend to results.
evalASTs :: (ASTContainer t e, Monoid a) => (e -> a) -> t -> a
evalASTs f = evalContainedASTs (eval f)

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
                  | otherwise -> do
                        b <- isLifted tcn'
                        case b of
                            True -> return . Just =<< varE 'containedASTs `appE` (varE n)
                            False -> return Nothing
        (VarT _) -> return . Just =<< varE 'containedASTs `appE` (varE n)
        _ -> return Nothing
    where
        isLifted tn = do
            r <- reify tn
            case r of
                PrimTyConI _ _ b -> return $ not b
                _ -> return True

derivingASTContainer :: TH.Name -- ^ The name of the datatype to walk 
                     -> TH.Name -- ^ The name of the AST datatype to extract
                     -> Q [Dec]
derivingASTContainer ty ty_ex =
    withTyConI ty [] $ \tyCon -> do -- (TyConI tyCon) <- reify ty
        let (tyConName, tyVars, cs) = tyConData tyCon
        tyApp <- applyTypes tyConName tyVars

        (TyConI tyConEx) <- reify ty_ex
        let (tyConNameEx, tyVarsEx, _) = tyConData tyConEx
        tyExApp <- applyTypes tyConNameEx tyVarsEx

        inst_exists <- isInstance ''ASTContainer [tyApp, tyExApp]

        case inst_exists of
            False -> do
                let instanceType = conT ''ASTContainer
                                    `appT` return tyApp
                                    `appT` return tyExApp
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
            True -> return []

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
tyConData _ = error "tyConData: tyCon may not be a type synonym."

tyConDataWithTySyn :: Dec -> Q [(Name, [TyVarBndr], [Con])]
tyConDataWithTySyn (DataD _ nm tyVars _ cs _) = return [(nm, tyVars, cs)]
tyConDataWithTySyn (NewtypeD _ nm tyVars _ c _) = return [(nm, tyVars, [c])]
tyConDataWithTySyn (TySynD _ _ t) = do
    let ns = typeToNames t
    cs <- mapM (\n -> do
            rt <- reify n
            case rt of
                TyConI rt' ->  
                    tyConDataWithTySyn rt'
                _ -> return []) ns
    return $ concat cs
tyConDataWithTySyn _ = error "tyConData: tyCon may not be a type synonym."

concatLists :: [Exp] -> Exp
concatLists = foldl (\e1 e2 -> (VarE '(++)) `AppE` e1 `AppE` e2) (ConE '[])

-- | Derive an instance of AST, along with all ASTContainers required for that instance
derivingASTWithContainers :: TH.Name -- ^ The name of the datatype to walk 
                          -> Q [Dec]
derivingASTWithContainers ty = do
    d_ast  <- derivingAST ty

    -- Determine which types we need to derive ASTContainers for
    (TyConI tyCon) <- reify ty
    let (tn, tn_vars, cs) = tyConData tyCon
    tn' <- applyTypes tn tn_vars
    req <- collectReqTypes cs

    d_ast_c <- return . concat =<< mapM (flip derivingASTContainer ty) req

    return $ d_ast ++ d_ast_c

collectReqTypes :: [Con] -> Q [TH.Name]
collectReqTypes = collectReqTypes' S.empty

collectReqTypes' :: S.Set Type -> [Con] -> Q [TH.Name]
collectReqTypes' collected [] = do
    let coll' = concatMap typeToNames $ S.toList collected
    return . nub . concat =<< mapM splitTySyn coll'
collectReqTypes' collected (c:cs) = do
    case c of
        (NormalC _ fieldTypes) -> do
            let new_ft = filter (`S.notMember` collected) . map snd $ fieldTypes
                collected' = foldr S.insert collected new_ft

                tns = concatMap typeToNames new_ft
            
            css <- mapM (\tn -> do
                            tycon <- reify tn
                            case tycon of
                                TyConI tyCon' -> do
                                    res <- tyConDataWithTySyn tyCon'
                                    let cs' = concat . (\(_, _, x) -> x )$ unzip3 res
                                    return cs'
                                PrimTyConI _ _ _ -> return []
                                _ -> error $ "collectReqTypes': Bad") tns

            collectReqTypes' collected' $ cs ++ concat css

withTyConI :: TH.Name -> a -> (Dec -> Q a) -> Q a
withTyConI ty def f = do
    t <- reify ty
    case t of
        TyConI d -> f d
        PrimTyConI _ _ _ -> return def
        _ -> error "withTyConI: Bad Name"

typeToNames :: Type -> [TH.Name]
typeToNames (AppT t1 t2) = typeToNames t1 ++ typeToNames t2
typeToNames (VarT n) = []
typeToNames (ConT n) = [n]
typeToNames ListT = []
typeToNames t = error $ "typeToNames: Bad type in typeToNames" ++ show t

-- | Decomposes type synonyms into a list of component data and newtypes.
-- Returns data and newtypes unchanged
splitTySyn :: TH.Name -> Q [TH.Name]
splitTySyn ty = do
    tyCon <- reify ty
    case tyCon of
        TyConI tyCon' ->
            case tyCon' of
                DataD _ _ _ _ _ _ -> return [ty]
                NewtypeD _ _ _ _ _ _ -> return [ty]
                TySynD _ _ t -> return . concat =<< mapM splitTySyn (typeToNames t)
        PrimTyConI _ _ _ -> return []
