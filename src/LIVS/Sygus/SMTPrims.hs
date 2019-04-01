module LIVS.Sygus.SMTPrims where

import LIVS.Language.Expr
import LIVS.Language.Syntax
import LIVS.Language.Typing

smtTrue :: DC
smtTrue = trueDC

smtAnd :: Id
smtAnd = Id (Name SMT "and" Nothing) (TyFun boolType (TyFun boolType boolType))

smtIte :: Type -> Id
smtIte t = Id (Name SMT "ite" Nothing) (TyFun boolType (TyFun t (TyFun t t)))