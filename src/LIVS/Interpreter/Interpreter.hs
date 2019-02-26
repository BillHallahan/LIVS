module LIVS.Interpreter.Interpreter (run) where

import LIVS.Language.Expr
import qualified LIVS.Language.Heap as H
import LIVS.Language.Syntax

run :: H.Heap -> Expr -> Expr
run = run'

run' :: H.Heap -> Expr -> Expr
run' h v@(Var (Id n _)) =
	case H.lookup n h of
		Just e -> e
		Nothing -> v
run' _ l@(Lit _) = l

-- | By rewriting with Let's, converts an Expr into a form such that all
-- function arguments are variables or literals
constAppNF :: Expr -> Expr
constAppNF v@(Var _) = v
constAppNF l@(Lit _) = l
constAppNF (Lam i e) = Lam i $ constAppNF e
constAppNF e@(App _ _) =
	let
		(a:as) = unApp e
	in
	undefined
constAppNF (Let (i, b) e) = Let (i, constAppNF b) (constAppNF e)