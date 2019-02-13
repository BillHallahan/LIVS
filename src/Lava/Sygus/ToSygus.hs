module Lava.Sygus.ToSygus (toSygus) where

import Lava.Language.Syntax
import Lava.Language.Typing

import Data.List

toSygus :: [Example] -> String
toSygus es =
    let
        fs = collectFuncs es
        fspec = concatMap (\(n, it, ot) -> genSynthFun n it ot) fs

        constraints = concat . intersperse "\n" $ map toSygusExample es
    in
    "(set-logic SLIA)\n" ++ fspec ++ "\n" ++ constraints ++ "\n(check-synth)"

toSygusExample :: Example -> String
toSygusExample (Example { func_name = f, input = is, output = out }) =
    let
        as = concat . intersperse " " $ map toSygusLit is 
        call = "(" ++ f ++ " " ++ as ++ ")"
    in
    "(constraint (= " ++ call ++ " " ++ toSygusLit out ++ "))"

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

genSynthFun :: Name -> [Type] -> Type -> String
genSynthFun n it ot =
    let
        xs = ["x" ++ show i | i <- [1..]]

        xs' = take (length it) xs

        sit = concatMap (\(n, t) -> "(" ++ n ++ " " ++ toSygusType t ++ ")") $ zip xs' it
        sot = toSygusType ot
    in
    "(synth-fun " ++ n ++ " (" ++ sit ++ ")"
        ++ " " ++ sot ++ "\n" ++ sygusInt xs' ++ ")"

-- | Get all unique function names and types
collectFuncs :: [Example] -> [(Name, [Type], Type)]
collectFuncs = nub 
             . map (\e -> ( func_name e
                          , map typeOf . input $ e
                          , typeOf $ output e)
                   )

sygusInt :: [String] -> String
sygusInt xs =
           "((Start Int (ntInt))\n"
        ++ "(ntInt Int\n" 
        ++ "(0 1 2 3 4 5 "
        ++ concat (intersperse " " xs) ++ "\n"
        ++ "(+ ntInt ntInt)\n"
        ++ "(- ntInt ntInt)\n"
        ++ "(* ntInt ntInt))))"