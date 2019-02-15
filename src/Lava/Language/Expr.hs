module Lava.Language.Expr ( mkLams
                          , leadingLams
                          , mkApp
                          , unApp) where

import Lava.Language.Syntax

mkLams :: [Id] -> Expr -> Expr
mkLams is e = foldr Lam e is

leadingLams :: Expr -> [Id]
leadingLams (Lam i e) = i:leadingLams e
leadingLams _ = []

mkApp :: [Expr] -> Expr
mkApp = foldl1 App

unApp :: Expr -> [Expr]
unApp = reverse . unApp'

unApp' :: Expr -> [Expr]
unApp' (App e e') = e':unApp' e
unApp' e = [e]