{-# LANGUAGE DeriveGeneric #-}

module Lava.Language.Syntax ( Name
                            , Id (..)
                            , Expr (..)
                            , Lit (..)
                            , Type (..)

                            , Example (..)

                            , idName
                            , examplesForFunc ) where

import GHC.Generics (Generic)
import Data.Hashable

type Name = String

data Id = Id Name Type
          deriving (Eq, Show, Read, Generic)

instance Hashable Id

idName :: Id -> Name
idName (Id n _) = n

data Expr = Var Id
          | Lam Id Expr
          | App Expr Expr
          | Lit Lit
          deriving (Eq, Show, Read, Generic)

data Lit = LInt Int
           deriving (Eq, Show, Read, Generic)

data Type = TyCon Name Type
          | TyFun Type Type
          | TYPE
          deriving (Eq, Show, Read, Generic)

instance Hashable Type

data Example = Example { func_name :: String
                       , input :: [Lit]
                       , output :: Lit }
                       deriving (Eq, Show, Read, Generic)

-- | Filter a list of examples to only those relevant to the given function
examplesForFunc :: Name -> [Example] -> [Example]
examplesForFunc n = filter (\e -> n == func_name e)