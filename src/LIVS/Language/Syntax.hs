{-# LANGUAGE DeriveGeneric #-}

module LIVS.Language.Syntax ( Name (..)
                            , Id (..)
                            , Expr (..)
                            , Val (..)
                            , Lit (..)
                            , DC (..)
                            , Type (..)

                            , Example (..)

                            , exprToVal
                            , valToExpr
                            , isVal

                            , idName
                            , funcName
                            , examplesForFunc ) where

import GHC.Generics (Generic)
import Data.Hashable
import Data.Maybe

data Name = Name String (Maybe Integer)
            deriving (Eq, Ord, Show, Read, Generic)

instance Hashable Name

data Id = Id Name Type
          deriving (Eq, Show, Read, Generic)

instance Hashable Id

idName :: Id -> Name
idName (Id n _) = n

data Expr = Var Id
          | Data DC
          | Lit Lit
          | Lam Id Expr
          | App Expr Expr
          | Let Binding Expr
          deriving (Eq, Show, Read, Generic)

instance Hashable Expr

data Val = DataVal DC
         | LitVal Lit
         deriving (Eq, Show, Read, Generic)

instance Hashable Val

exprToVal :: Expr -> Maybe Val
exprToVal (Data dc) = Just $ DataVal dc
exprToVal (Lit l) = Just $ LitVal l
exprToVal _ = Nothing

valToExpr :: Val -> Expr
valToExpr (DataVal dc) = Data dc
valToExpr (LitVal l) = Lit l

isVal :: Expr -> Bool
isVal = isJust . exprToVal

type Binding = (Id, Expr)

data Lit = LInt Int
           deriving (Eq, Show, Read, Generic)

instance Hashable Lit

data DC = DC Name Type
          deriving (Eq, Show, Read, Generic)

instance Hashable DC

data Type = TyCon Name Type
          | TyFun Type Type
          | TYPE
          deriving (Eq, Show, Read, Generic)

instance Hashable Type

data Example = Example { func :: Id
                       , input :: [Val]
                       , output :: Val }
                       deriving (Eq, Show, Read, Generic)

instance Hashable Example

funcName :: Example -> Name
funcName = idName . func

-- | Filter a list of examples to only those relevant to the given function
examplesForFunc :: Name -> [Example] -> [Example]
examplesForFunc n = filter (\e -> n == funcName e)