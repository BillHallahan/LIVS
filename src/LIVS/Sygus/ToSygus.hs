module LIVS.Sygus.ToSygus ( toSygus 
                          , toSygusWithGrammar
                          , toSygusFunExpr
                          , toSygusExpr
                          , toSygusType) where

import LIVS.Language.CallGraph
import LIVS.Language.Expr
import qualified LIVS.Language.Heap as H
import LIVS.Language.Naming
import LIVS.Language.Syntax
import qualified LIVS.Language.TypeEnv as T
import LIVS.Language.Typing

import qualified Data.HashMap.Lazy as HM
import qualified Data.HashSet as HS
import Data.List
import Data.Maybe

-- | Translates examples into a SyGuS problem.
-- Functions from the heap are translated into SMT formulas, so they can be
-- used during synthesis.
toSygus :: CallGraph -> H.Heap -> T.TypeEnv -> [Example] -> String
toSygus cg h tenv = toSygusWithGrammar cg h tenv (HS.fromList $ H.keys h)

-- | Translates examples into a SyGuS problem.
-- Functions from the heap are translated into SMT formulas, so they can be
-- used during synthesis. The passed Name's restricts the grammar to only
-- directly use the names in the Set.
toSygusWithGrammar :: CallGraph
                   -> H.Heap
                   -> T.TypeEnv
                   -> HS.HashSet Name
                   -> [Example]
                   -> String
toSygusWithGrammar cg h tenv hsr es =
    let
        tspec = toSygusTypeEnv tenv

        -- Functions in SMT formulas need to be declared before they are used,
        -- so we add them to the formula in post-order.
        post = map idName $ postOrderList cg
        h' = H.mapWithKeyDefs' toSygusFunExpr h
        hf = intercalate "\n" $ mapMaybe (flip HM.lookup h') post

        ls = map LInt [0..2]

        -- We narrow the heap to the allowable functions that are directly
        -- used in the function definition, but add selector functions and
        -- data constructors, to allow types to be passed between different
        -- sorts of data constructors
        fs = collectFuncs es
        hr = H.filterWithKey (\n _ -> n `HS.member` hsr) h
        hr' = T.mergeConstructors tenv hr
        hr'' = T.mergeSelectorsAndTesters tenv hr'
        fspec = concatMap (\(n, it, ot) -> genSynthFun hr'' n ls it ot) fs

        constraints = concat . intersperse "\n" $ map toSygusExample es
    in
    "(set-logic SLIA)\n" ++ tspec ++ "\n" ++  hf ++ "\n" ++ fspec ++ "\n"
        ++ constraints ++ "\n(check-synth)"

toSygusExample :: Example -> String
toSygusExample (Example { func = f, input = is, output = out }) =
    let
        as = concat . intersperse " " $ map toSygusVal is 
        call = "(" ++ toSygusId f ++ " " ++ as ++ ")"
    in
    "(constraint (= " ++ call ++ " " ++ toSygusVal out ++ "))"

toSygusId :: Id -> String
toSygusId (Id n _) = nameToString n

toSygusIdWithType :: Id -> String
toSygusIdWithType (Id n t) =
    "(" ++ nameToString n ++ " " ++ toSygusType t ++ ")"

toSygusExpr :: Expr -> String
toSygusExpr (Var i) = toSygusId i
toSygusExpr (Data dc) = toSygusDC dc
toSygusExpr (Lit l) = toSygusLit l
toSygusExpr (Lam _ e) = toSygusExpr e
toSygusExpr e@(App _ _) =
    "(" ++ (concat . intersperse " " . map toSygusExpr $ unApp e) ++ ")"
toSygusExpr (Let (i, b) e) =
    "(let ((" ++ toSygusId i
        ++ " (" ++ toSygusExpr b ++ ")))" ++ toSygusExpr e ++ ")"

toSygusVal :: Val -> String
toSygusVal (DataVal dc) = toSygusDC dc
toSygusVal (LitVal dc) = toSygusLit dc
toSygusVal (AppVal v1 v2) = "(" ++ toSygusVal v1 ++ " " ++ toSygusVal v2 ++ ")"

toSygusDC :: DC -> String
toSygusDC (DC n _) = nameToString n

toSygusLit :: Lit -> String
toSygusLit (LInt i) = show i
toSygusLit (LString s) = show s

toSygusType :: Type -> String
toSygusType (TyCon n _) = nameToString n
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
    "(define-fun " ++ nameToString n ++ " (" ++ as ++ ") " ++ r ++ " " ++ se ++ ")"

genSynthFun :: H.Heap -> Name -> [Lit] -> [Type] -> Type -> String
genSynthFun h n ls it ot =
    let
        vs = [Name "x" (Just i) | i <- [1..] :: [Integer]]

        vs' = map (uncurry Id) $ zip vs it

        sit = concatMap (\(i, t) -> 
            "(" ++ nameToString (idName i) ++ " " ++ toSygusType t ++ ")") $ zip vs' it
        sot = toSygusType ot

        rts = nub . map returnType $ H.elems h
        gs = concat . intersperse "\n" $ map (\t -> sygusGrammar t h ls vs') rts
    in
    "(synth-fun " ++ nameToString n ++ " (" ++ sit ++ ")" ++ sot ++ "\n"
        ++ "((Start " ++ sot ++ " (" ++ typeSymbol ot ++ "))\n"
        ++ gs ++ "))"

-- | Get all unique function names and types
collectFuncs :: [Example] -> [(Name, [Type], Type)]
collectFuncs = nub 
             . map (\e -> ( funcName e
                          , map typeOf . input $ e
                          , typeOf $ output e)
                   )

-- | Returns a grammar to return values of the given type
sygusGrammar :: Type
             -> H.Heap
             -> [Lit]
             -> [Id] -- ^ Variables usable in the grammar
             -> String
sygusGrammar t@(TyCon n _) h ls vs =
    let
        sc = sygusGrammar' t h
        vs' = map nameToString . map idName $ filter (\i -> typeOf i == t) vs
        ls' = map toSygusLit $ filter (\l -> typeOf l == t) ls
    in
       "(" ++ typeSymbol t ++ " " ++ nameToString n ++ "\n" 
    ++ "(" ++ concat (intersperse " " ls') ++ " "
    ++ concat (intersperse " " vs') ++ "\n"
    ++ sc
    ++ "))"
sygusGrammar t _ _ _ = error $ "sygusGrammar: Bad type." ++ show t

sygusGrammar' :: Type -> H.Heap -> String
sygusGrammar' t =
    concat . H.mapWithKey'
        (\n e -> 
            let
                at = argTypes e
                ts = concat . intersperse " " $ map typeSymbol at
            in
            case at of
                [] -> nameToString n ++ "\n"
                _ -> "(" ++ nameToString n ++ " " ++ ts ++ ")\n")
        . H.filter (\e -> t == returnType e)

typeSymbol :: Type -> String
typeSymbol (TyCon n _) = "nt" ++ nameToString n
typeSymbol _ = error $ "typeSymbol: Bad type."

toSygusTypeEnv :: T.TypeEnv -> String
toSygusTypeEnv = intercalate " " . map (uncurry toSygusTypeEnv') . T.toList

toSygusTypeEnv' :: Name -> T.ADTSpec -> String
toSygusTypeEnv' n (T.ADTSpec ts) =
    let
        ts' = intercalate " " $ map (toSygusSelectorDC) ts
        testers = intercalate "\n" $ map (toSygusTesters n) ts
    in
    "(declare-datatype " ++ nameToString n ++ " (" ++ ts' ++ "))\n" ++ testers

toSygusSelectorDC :: T.SelectorDC -> String
toSygusSelectorDC (T.SelectorDC n nt) =
    "(" ++ nameToString n ++ " "
        ++ intercalate " " (map toSygusNamedType nt) ++ ")"

toSygusNamedType :: T.NamedType -> String
toSygusNamedType (T.NamedType n t) =
    "(" ++ nameToString n ++ " " ++ toSygusType t ++ ")"

toSygusTesters :: Name -> T.SelectorDC -> String
toSygusTesters tn (T.SelectorDC n _) =
   toSygusTester tn n

toSygusTester :: Name -> Name -> String
toSygusTester tn dcn = 
    "(define-fun is" ++ nameToString dcn ++ " ((i " ++ nameToString tn ++ ")) Bool ((_ is " ++ nameToString dcn ++ ") i))"