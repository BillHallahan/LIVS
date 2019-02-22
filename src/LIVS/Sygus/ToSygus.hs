module LIVS.Sygus.ToSygus ( toSygus ) where

import LIVS.Language.Expr
import qualified LIVS.Language.Heap as H
import LIVS.Language.Syntax
import LIVS.Language.Typing

import qualified Data.HashMap.Lazy as HM
import Data.List

-- | Translates examples into a SyGuS problem.
-- Functions from the heap are translated into SMT formulas, so they can be
-- used during synthesis.
toSygus :: H.Heap -> [Example] -> String
toSygus h es =
    let
        hf = concat . intersperse " " .  HM.elems $ H.mapWithKey' toSygusFunExpr h

        fs = collectFuncs es
        fspec = concatMap (\(n, it, ot) -> genSynthFun h n it ot) fs

        constraints = concat . intersperse "\n" $ map toSygusExample es
    in
    "(set-logic SLIA)\n" ++ hf ++ "\n" ++ fspec ++ "\n"
        ++ constraints ++ "\n(check-synth)"

toSygusExample :: Example -> String
toSygusExample (Example { func = f, input = is, output = out }) =
    let
        as = concat . intersperse " " $ map toSygusLit is 
        call = "(" ++ idName f ++ " " ++ as ++ ")"
    in
    "(constraint (= " ++ call ++ " " ++ toSygusLit out ++ "))"

toSygusId :: Id -> String
toSygusId (Id n _) = n

toSygusIdWithType :: Id -> String
toSygusIdWithType (Id n t) = "(" ++ n ++ " " ++ toSygusType t ++ ")"

toSygusExpr :: Expr -> String
toSygusExpr (Var i) = toSygusId i
toSygusExpr (Lam _ e) = toSygusExpr e
toSygusExpr e@(App _ _) =
    "(" ++ (concat . intersperse " " . map toSygusExpr $ unApp e) ++ ")"
toSygusExpr (Lit l) = toSygusLit l

toSygusLit :: Lit -> String
toSygusLit (LInt i) = show i

toSygusType :: Type -> String
toSygusType (TyCon n _) = n
toSygusType t@(TyFun _ _) =
    let
        as = concat . intersperse " " . map toSygusType . argTypes $ PresType t
        r = toSygusType $ returnType (PresType t)
    in
    "(" ++ as ++ ") " ++ r
toSygusType TYPE = "TYPE"

toSygusFunExpr :: Name -> Expr -> String
toSygusFunExpr n e =
    let
        as = concat . intersperse " " . map toSygusIdWithType $ leadingLams e
        r = toSygusType $ returnType e

        se = toSygusExpr e
    in
    "(define-fun " ++ n ++ " (" ++ as ++ ") " ++ r ++ " " ++ se ++ ")"

genSynthFun :: H.Heap -> Name -> [Type] -> Type -> String
genSynthFun h n it ot =
    let
        xs = ["x" ++ show i | i <- [1..] :: [Integer]]

        xs' = take (length it) xs

        sit = concatMap (\(n', t) -> "(" ++ n' ++ " " ++ toSygusType t ++ ")") $ zip xs' it
        sot = toSygusType ot
    in
    "(synth-fun " ++ n ++ " (" ++ sit ++ ")"
        ++ " " ++ sot ++ "\n" ++ sygusInt h xs' ++ ")"

-- | Get all unique function names and types
collectFuncs :: [Example] -> [(Name, [Type], Type)]
collectFuncs = nub 
             . map (\e -> ( funcName e
                          , map typeOf . input $ e
                          , typeOf $ output e)
                   )

sygusInt :: H.Heap -> [String] -> String
sygusInt h xs =
    let
        sc = getSynthCalls h
    in
       "((Start Int (ntInt))\n"
    ++ "(ntInt Int\n" 
    ++ "(0 1 2 3 4 5 "
    ++ concat (intersperse " " xs) ++ "\n"
    ++ sc
    ++ "(+ ntInt ntInt)\n"
    ++ "(- ntInt ntInt)\n"
    ++ "(* ntInt ntInt))))"

getSynthCalls :: H.Heap -> String
getSynthCalls =
    concat . H.mapWithKey'
        (\n e -> 
            let
                ts = concat . intersperse " " . map (const "ntInt") $ argTypes e
            in
            "(" ++ n ++ " " ++ ts ++ ")\n")

-- "(plus ntInt ntInt)\n"