module Lava.Language.Expr ( mkLams
                          , mkApp) where

import Lava.Language.Syntax

mkLams :: [Id] -> Expr -> Expr
mkLams is e = foldr Lam e is

mkApp :: [Expr] -> Expr
mkApp = foldl1 App