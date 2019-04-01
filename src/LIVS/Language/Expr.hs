module LIVS.Language.Expr ( trueDC
                          , falseDC
                          , mkLams
                          , leadingLams
                          , stripLeadingLams
                          , mkApp
                          , unApp
                          , appCenter
                          , appArgs) where

import LIVS.Language.Syntax
import LIVS.Language.Typing

trueDC :: DC
trueDC = DC (Name SMT "true" Nothing) boolType

falseDC :: DC
falseDC = DC (Name SMT "false" Nothing) boolType

mkLams :: [Id] -> Expr -> Expr
mkLams is e = foldr Lam e is

leadingLams :: Expr -> [Id]
leadingLams (Lam i e) = i:leadingLams e
leadingLams _ = []

stripLeadingLams :: Expr -> Expr
stripLeadingLams (Lam _ e) = stripLeadingLams e
stripLeadingLams e = e

mkApp :: [Expr] -> Expr
mkApp = foldl1 App

unApp :: Expr -> [Expr]
unApp = reverse . unApp'

unApp' :: Expr -> [Expr]
unApp' (App e e') = e':unApp' e
unApp' e = [e]

appCenter :: Expr -> Expr
appCenter (App e _) = appCenter e
appCenter e = e

appArgs :: Expr -> [Expr]
appArgs = tail . unApp