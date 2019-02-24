module LIVS.Sygus.ToSygus ( toSygus 
                          , toSygusWithGrammar) where

import LIVS.Language.CallGraph
import LIVS.Language.Expr
import qualified LIVS.Language.Heap as H
import LIVS.Language.Syntax
import LIVS.Language.Typing

import qualified Data.HashMap.Lazy as HM
import qualified Data.HashSet as HS
import Data.List
import Data.Maybe

-- | Translates examples into a SyGuS problem.
-- Functions from the heap are translated into SMT formulas, so they can be
-- used during synthesis.
toSygus :: CallGraph -> H.Heap -> [Example] -> String
toSygus cg h = toSygusWithGrammar cg h (HS.fromList $ H.keys h)

-- | Translates examples into a SyGuS problem.
-- Functions from the heap are translated into SMT formulas, so they can be
-- used during synthesis. The passed Name's restricts the grammar to only
-- directly use the names in the Set.
toSygusWithGrammar :: CallGraph -> H.Heap -> HS.HashSet Name -> [Example] -> String
toSygusWithGrammar cg h hsr es =
    let
        -- Functions in SMT formulas need to be declared before they are used,
        -- so we add them to the formula in post-order.
        post = map idName $ postOrderList cg
        h' = H.mapWithKeyDefs' toSygusFunExpr h
        hf = concat . intersperse "\n" $ mapMaybe (flip HM.lookup h') post

        ls = map LInt [0..3]

        fs = collectFuncs es
        hr = H.filterWithKey (\n _ -> n `HS.member` hsr) h
        fspec = concatMap (\(n, it, ot) -> genSynthFun hr n ls it ot) fs

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

genSynthFun :: H.Heap -> Name -> [Lit] -> [Type] -> Type -> String
genSynthFun h n ls it ot =
    let
        vs = ["x" ++ show i | i <- [1..] :: [Integer]]

        vs' = map (uncurry Id) $ zip vs it

        sit = concatMap (\(i, t) -> "(" ++ idName i ++ " " ++ toSygusType t ++ ")") $ zip vs' it
        sot = toSygusType ot

        rts = nub . map returnType $ H.elems h
        gs = concat . intersperse "\n" $ map (\t -> sygusGrammar t h ls vs') rts
    in
    "(synth-fun " ++ n ++ " (" ++ sit ++ ")" ++ sot ++ "\n"
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
        vs' = map idName $ filter (\i -> typeOf i == t) vs
        ls' = map toSygusLit $ filter (\l -> typeOf l == t) ls
    in
       "(" ++ typeSymbol t ++ " " ++ n ++ "\n" 
    ++ "(" ++ concat (intersperse " " ls') ++ " "
    ++ concat (intersperse " " vs') ++ "\n"
    ++ sc
    ++ "))"
sygusGrammar _ _ _ _ = error $ "sygusGrammar: Bad type."

sygusGrammar' :: Type -> H.Heap -> String
sygusGrammar' t =
    concat . H.mapWithKey'
        (\n e -> 
            let
                ts = concat . intersperse " " . map typeSymbol $ argTypes e
            in
            "(" ++ n ++ " " ++ ts ++ ")\n")
        . H.filter (\e -> t == returnType e)

typeSymbol :: Type -> String
typeSymbol (TyCon n _) = "nt" ++ n
typeSymbol _ = error $ "typeSymbol: Bad type."