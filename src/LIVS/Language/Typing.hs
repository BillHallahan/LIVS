module LIVS.Language.Typing ( Typed (..)
                            , PresType (..)
                            , intType
                            , floatType
                            , stringType
                            , boolType
                            , exampleFuncType

                            , mkTyFun
                            , unTyFun
                            , argTypes
                            , returnType

                            , tyConNames ) where

import LIVS.Language.Syntax

import qualified Data.HashSet as S

class Typed t where
    typeOf :: t -> Type

instance Typed Id where
    typeOf (Id _ t) = t

instance Typed Expr where
    typeOf (Var i) = typeOf i
    typeOf (Data dc) = typeOf dc
    typeOf (Lit l) = typeOf l
    typeOf (Lam i e) = TyFun (typeOf i) (typeOf e)
    typeOf a@(App e _) =
        case typeOf e of
            TyFun _ t2 -> t2
            _ -> error $ "Bad type." ++ show a
    typeOf (Let _ e) = typeOf e

instance Typed Val where
    typeOf (DataVal dc) = typeOf dc
    typeOf (LitVal l) = typeOf l
    typeOf a@(AppVal v1 _) =
        case typeOf v1 of
            TyFun _ t2 -> t2
            _ -> error $ "Bad type." ++ show a

instance Typed Lit where
    typeOf (LInt _) = intType
    typeOf (LFloat _) = floatType
    typeOf (LString _) = stringType

instance Typed DC where
    typeOf (DC _ t) = t

instance Typed Type where
    typeOf (TyCon _ t) = t
    typeOf (TyFun _ _) = TYPE
    typeOf TYPE = TYPE

newtype PresType = PresType Type

instance Typed PresType where
    typeOf (PresType t) = t

intType :: Type
intType = TyCon (Name SMT "Int" Nothing) TYPE

floatType :: Type
floatType = TyCon (Name SMT "Real" Nothing) TYPE

stringType :: Type
stringType = TyCon (Name SMT "String" Nothing) TYPE

boolType :: Type
boolType = TyCon (Name SMT "Bool" Nothing) TYPE

exampleFuncType :: Example -> Type
exampleFuncType es = mkTyFun $ map typeOf (input es) ++ [typeOf (output es)]

mkTyFun :: [Type] -> Type
mkTyFun = foldr1 TyFun

unTyFun :: Type -> [Type]
unTyFun (TyFun t t') = t:unTyFun t'
unTyFun t = [t]

argTypes :: Typed t => t -> [Type]
argTypes = argTypes' . typeOf
    where
        argTypes' :: Type -> [Type]
        argTypes' (TyFun t1 t2) = t1:argTypes' t2
        argTypes' _ = []

returnType :: Typed t => t -> Type
returnType = returnType' . typeOf
    where
        returnType' :: Type -> Type
        returnType' (TyFun _ t2) = returnType' t2
        returnType' t = t

tyConNames :: Type -> S.HashSet Name
tyConNames (TyCon n t) = S.union (S.singleton n) (tyConNames t)
tyConNames (TyFun t1 t2) = S.union (tyConNames t1) (tyConNames t2)
tyConNames TYPE = S.empty
