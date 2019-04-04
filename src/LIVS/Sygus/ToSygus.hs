module LIVS.Sygus.ToSygus ( toSygus 
                          , toSygusWithGrammar
                          , toSygusTypeEnv
                          , toSygusFunExpr
                          , toSygusExpr
                          , toSygusType) where

import LIVS.Language.CallGraph
import LIVS.Language.Expr
import qualified LIVS.Language.Heap as H
import LIVS.Language.Naming
import qualified LIVS.Language.SubFunctions as Sub
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
toSygus :: CallGraph  -> [Val] -> H.Heap -> Sub.SubFunctions -> T.TypeEnv -> [Example] -> String
toSygus cg cons_val h sub tenv = toSygusWithGrammar cg cons_val h sub tenv (HS.fromList $ H.keys h)

-- | Translates examples into a SyGuS problem.
-- Functions from the heap are translated into SMT formulas, so they can be
-- used during synthesis. The passed Name's restricts the grammar to only
-- directly use the names in the Set.
toSygusWithGrammar :: CallGraph
                   -> [Val]
                   -> H.Heap
                   -> Sub.SubFunctions
                   -> T.TypeEnv
                   -> HS.HashSet Name
                   -> [Example]
                   -> String
toSygusWithGrammar cg cons_val h sub tenv hsr es@(e:_) =
    let
        tenv' = filterTypeEnv h es tenv
        tspec = toSygusTypeEnv tenv'

        -- Functions in SMT formulas need to be declared before they are used,
        -- so we add them to the formula in post-order.
        post = nub $ flip Sub.lookupAllNames sub . map idName $ postOrderList cg

        elimSynthH = H.filterWithKey (\n _ -> n /= idName (func e)) h
        tyFilH = filterHeapToValidTypes tenv' elimSynthH

        h' = H.mapWithKeyDefs' toSygusFunExpr tyFilH
        hf = intercalate "\n" $ mapMaybe (flip HM.lookup h') post

        -- We narrow the heap to the allowable functions that are directly
        -- used in the function definition, but add selector functions and
        -- data constructors, to allow types to be passed between different
        -- sorts of data constructors
        fs = collectFuncs es
        hr = H.filterWithKey (\n _ -> n `HS.member` hsr) tyFilH
        fspec = concatMap (\(n, it, ot) -> genSynthFun hr n cons_val it ot) fs

        constraints = concat . intersperse "\n" $ map toSygusExample es
    in
    "(set-logic SLIA)\n" ++ tspec ++ "\n" ++  hf ++ "\n" ++ fspec ++ "\n"
        ++ constraints ++ "\n(check-synth)"
toSygusWithGrammar _ _ _ _ _ _ [] = error "toSygusWithGrammar: No examples"

toSygusExample :: Example -> String
toSygusExample (Example { func = f, input = is, output = out }) =
    let
        as = concat . intersperse " " $ map toSygusVal is 
        call = "(" ++ toSygusId f ++ " " ++ as ++ ")"
    in
    "(constraint (= " ++ call ++ " " ++ toSygusVal out ++ "))"

toSygusId :: Id -> String
toSygusId (Id n _) = nameToStringSMT n

toSygusIdWithType :: Id -> String
toSygusIdWithType (Id n t) =
    "(" ++ nameToStringSMT n ++ " " ++ toSygusType t ++ ")"

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
toSygusDC (DC n _) = nameToStringSMT n

toSygusLit :: Lit -> String
toSygusLit (LInt i)
    | i >= 0 = show i
    | otherwise = "(- " ++ show (-i) ++ ")"
toSygusLit (LFloat f)
    | f >= 0 = show f
    | otherwise = "(- " ++ show (-f) ++ ")"
toSygusLit (LString s) = "\"" ++ s ++ "\""

toSygusType :: Type -> String
toSygusType (TyCon n _) = nameToStringSMT n
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
    "(define-fun " ++ nameToStringSMT n ++ " (" ++ as ++ ") " ++ r ++ " " ++ se ++ ")"

genSynthFun :: H.Heap -> Name -> [Val] -> [Type] -> Type -> String
genSynthFun h n ls it ot =
    let
        vs = [Name Ident ("x" ++ show i ++ "_") Nothing | i <- [1..] :: [Integer]]

        vs' = map (uncurry Id) $ zip vs it

        sit = concatMap (\(i, t) -> 
            "(" ++ nameToStringSMT (idName i) ++ " " ++ toSygusType t ++ ")") $ zip vs' it
        sot = toSygusType ot

        rts = nub . map returnType $ H.elems h
        gs = concat . intersperse "\n" $ map (\t -> sygusGrammar t h ls vs') rts
    in
    "(synth-fun " ++ nameToStringSMT n ++ " (" ++ sit ++ ")" ++ sot ++ "\n"
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
             -> [Val]
             -> [Id] -- ^ Variables usable in the grammar
             -> String
sygusGrammar t@(TyCon n _) h ls vs =
    let
        sc = sygusGrammar' t h
        vs' = map nameToStringSMT . map idName $ filter (\i -> typeOf i == t) vs
        ls' = map toSygusVal $ filter (\l -> typeOf l == t) ls
    in
       "(" ++ typeSymbol t ++ " " ++ nameToStringSMT n ++ "\n" 
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
                [] -> nameToStringSMT n ++ "\n"
                _ -> "(" ++ nameToStringSMT n ++ " " ++ ts ++ ")\n")
        . H.filter (\e -> t == returnType e)

typeSymbol :: Type -> String
typeSymbol (TyCon n _) = "nt" ++ nameToStringSMT n
typeSymbol _ = error $ "typeSymbol: Bad type."

toSygusTypeEnv :: T.TypeEnv -> String
toSygusTypeEnv = intercalate " " . map (uncurry toSygusTypeEnv') . T.toList

toSygusTypeEnv' :: Name -> T.ADTSpec -> String
toSygusTypeEnv' n (T.ADTSpec ts) =
    let
        ts' = intercalate " " $ map (toSygusSelectorDC) ts
        testers = intercalate "\n" $ map (toSygusTesters n) ts
    in
    "(declare-datatype " ++ nameToStringSMT n ++ " (" ++ ts' ++ "))\n" ++ testers

toSygusSelectorDC :: T.SelectorDC -> String
toSygusSelectorDC (T.SelectorDC n nt) =
    "(" ++ nameToStringSMT n ++ " "
        ++ intercalate " " (map toSygusNamedType nt) ++ ")"

toSygusNamedType :: T.NamedType -> String
toSygusNamedType (T.NamedType n t) =
    "(" ++ nameToStringSMT n ++ " " ++ toSygusType t ++ ")"

toSygusTesters :: Name -> T.SelectorDC -> String
toSygusTesters tn (T.SelectorDC n _) =
   toSygusTester tn n

toSygusTester :: Name -> Name -> String
toSygusTester tn dcn = 
    "(define-fun is" ++ nameToStringSMT dcn ++ " ((i " ++ nameToStringSMT tn ++ ")) Bool ((_ is " ++ nameToStringSMT dcn ++ ") i))"

-- | Filters out (some) unneeded types from the TypeEnv
filterTypeEnv :: H.Heap -> [Example] -> T.TypeEnv -> T.TypeEnv
filterTypeEnv h es tenv = T.filterWithKey (\n _ -> n `HS.member` tyConNs) tenv
    where

        esTys = concatMap (\e -> (typeOf $ output e):map typeOf (input e)) es

        -- cons = T.constructorNames tenv
        -- h' = H.filterWithKey (\n _ -> n `notElem` cons) h
        -- hRetTys = map returnType $ H.elems h'

        -- tyConNs = HS.unions . map tyConNames $ esTys ++ hRetTys
        tyConNs = HS.unions $ map tyConNames esTys

-- | Filter a Heap to eliminate functions where the return type is not one of
-- the primitives or in the TypeEnv
filterHeapToValidTypes :: T.TypeEnv -> H.Heap -> H.Heap
filterHeapToValidTypes tenv =
    H.filter (\e -> all (`HS.member` tycons) $ tyConNames (typeOf e))
    where
        tycons = HS.unions $ HS.fromList (T.keys tenv):map tyConNames [intType, stringType, boolType]