module LIVS.Sygus.SMTPrims where

import LIVS.Language.Expr
import LIVS.Language.Syntax
import LIVS.Language.Typing

smtTrue :: DC
smtTrue = trueDC

smtAnd :: Id
smtAnd = Id (SMTName "and") (TyFun boolType (TyFun boolType boolType))

smtIte :: Type -> Id
smtIte t = Id (SMTName "ite") (TyFun boolType (TyFun t (TyFun t t)))