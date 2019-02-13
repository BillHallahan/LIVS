module Lava.Language.Syntax ( Name
                            , Id (..)
                            , Expr (..)
                            , Lit (..)
                            , Type (..)

                            , Example (..) ) where

type Name = String

data Id = Id Name Type
          deriving (Eq, Show, Read)

data Expr = Var Id
          | Lam Id Expr
          | App Expr Expr
          | Lit Lit
          deriving (Eq, Show, Read)

data Lit = LInt Int
           deriving (Eq, Show, Read)

data Type = TyCon Name Type
          | TyFun Type Type
          | TYPE
          deriving (Eq, Show, Read)

data Example = Example { func_name :: String
                       , input :: [Lit]
                       , output :: Lit }