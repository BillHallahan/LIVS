module LIVS.Sygus.ExamplesToIte (examplesToIteResult) where

import LIVS.Language.Expr
import LIVS.Language.Syntax
import LIVS.Language.Typing
import LIVS.Sygus.Result

import qualified Data.HashMap.Lazy as M

examplesToIteResult :: [Example] -> Result
examplesToIteResult es@(Example { func = Id n _}:_) = Sat $ M.singleton n (examplesToIte es)
examplesToIteResult [] = error "examplesToIteResult: empty list"

-- | Given a list of examples, creates a function which trivially satisfies all
-- the examples via if-then-else statements
examplesToIte :: [Example] -> Expr
examplesToIte es@(ex:_) =
    let
        outputT = typeOf (output ex)

        ite = Name SMT "ite" Nothing
        iteI = Id ite $ TyFun boolType (TyFun outputT (TyFun outputT outputT)) 
    
        -- Create argument Ids
        vs = map (\(i, n) -> Id (Name Ident "x" (Just n)) (typeOf i)) $ zip (input ex) [0..]
    in
    mkLams vs
        $ foldr (\e -> App
                        (App 
                            (App 
                                (Var iteI) 
                                (checkEq vs e)
                            )
                            (valToExpr (output e))
                        )
              ) (valToExpr (output ex)) es
examplesToIte [] = error "examplesToIte: empty list"

checkEq :: [Id] -> Example -> Expr
checkEq vs@(_:_) (Example {input = is@(_:_)}) =
    let
        an = Name SMT "and" Nothing
        andI = Id an $ TyFun boolType (TyFun boolType boolType)

        eq = Name SMT "=" Nothing
    in
    foldr1 (\e -> App (App (Var andI) e)) .
        map (\(v, i) ->
                let
                    t = typeOf v
                    t' = typeOf i

                    eqV = Var $ Id eq (TyFun t (TyFun t boolType))
                in
                App (App eqV (Var v)) (valToExpr i)) $ zip vs is
checkEq _ _ = Data trueDC