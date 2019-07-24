-- Hides the warnings about deriving
{-# OPTIONS_GHC -fno-warn-orphans #-}

{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE TemplateHaskell #-}

module LIVS.Target.JavaScript.Extract ( module Language.JavaScript.Parser
                                      , DotNoteNames
                                      , parseJS
                                      , extractDefinition
                                      , extractDefinedFunctions
                                      , extractFunctions ) where

import LIVS.Language.AST
import LIVS.Language.Syntax
import LIVS.Language.Typing
import LIVS.Language.Expr
import LIVS.Target.General.LanguageEnv
import LIVS.Target.General.JSON
import LIVS.Target.JavaScript.JSIdentifier

import Language.JavaScript.Parser
import Language.JavaScript.Parser.AST

import qualified Data.HashSet as S
import Data.Semigroup

import Debug.Trace

-- | A set of names that use dot notation.
type DotNoteNames = S.HashSet Name

parseJS :: FilePath -> IO (Either String JSAST)
parseJS fp = do
    js <- readFile fp
    return $ parse js fp

extractDefinedFunctions :: JSAST -> [Id]
extractDefinedFunctions (JSAstProgram stmts _) =
    map extractDefinedFunctions' stmts
extractDefinedFunctions (JSAstStatement stmt _) =
    [extractDefinedFunctions' stmt]
extractDefinedFunctions _ = mempty

extractDefinedFunctions' :: JSStatement -> Id
extractDefinedFunctions' (JSFunction _ ident _ args _ block _) =
    nameCLToId (identToName ident) args

extractFunctions :: JSAST -> ([(Id, FuncInfo)], S.HashSet Name)
extractFunctions (JSAstProgram stmts _) = mconcat $ map extractFunctionsStmt stmts
extractFunctions (JSAstStatement stmt _) = extractFunctionsStmt stmt
extractFunctions _ = (mempty, S.empty)

extractFunctionsStmt :: JSStatement -> ([(Id, FuncInfo)], DotNoteNames)
extractFunctionsStmt (JSFunction _ ident _ args _ block _) =
    let
        (is, ns) = extractCalledFunctionsExpr block
        (is', ns') = extractCalledFunctionsStmt block
    in
    ([( nameCLToId (identToName ident) args, is <> is')], S.union ns ns')
extractFunctionsStmt _ = (mempty, S.empty)

extractCalledFunctionsStmt :: ASTContainer c JSStatement => c -> (FuncInfo, DotNoteNames)
extractCalledFunctionsStmt = evalASTs extractCalledFunctionsStmt'

extractCalledFunctionsStmt' :: JSStatement -> (FuncInfo, S.HashSet Name)
extractCalledFunctionsStmt' _ = (mempty, S.empty)

extractCalledFunctionsExpr :: ASTContainer c JSExpression => c -> (FuncInfo, DotNoteNames)
extractCalledFunctionsExpr = evalASTs extractCalledFunctionsExpr'

extractCalledFunctionsExpr' :: JSExpression -> (FuncInfo, DotNoteNames)
-- extractCalledFunctionsExpr' e@(JSIdentifier _ _) = error $ "extractCalledFunctionsExpr: JSIdentifier" ++ show e
extractCalledFunctionsExpr' (JSDecimal _ d) =
    let
        d' = jsJSONToVal $ d ++ "\n"
    in
    (FuncInfo { calls = mempty, consts = [d'] }, S.empty)
extractCalledFunctionsExpr' (JSStringLiteral _ s) =
    let
        s' = jsJSONToVal $ s ++ "\n"
    in
    (FuncInfo { calls = [], consts = [s'] }, S.empty)
-- extractCalledFunctionsExpr' e@(JSCallExpression _ _ _ _) = error $ "extractCalledFunctionsExpr: JSCallExpression" ++ show e
-- extractCalledFunctionsExpr' e@(JSCallExpressionDot _ _ (JSIdentifier _ n)) =
--     let
--         nm = Name Ident n Nothing
--     in
--     (FuncInfo {calls = [nameCLToId nm], consts = mempty }, S.singleton nm)
-- extractCalledFunctionsExpr' e@(JSCallExpressionDot _ _ _) = error $ "extractCalledFunctionsExpr: JSCallExpressionDot" ++ show e
extractCalledFunctionsExpr' (JSExpressionBinary _ bop _) =
    (FuncInfo { calls = [binOpToId bop], consts = mempty}, S.empty)
extractCalledFunctionsExpr' (JSMemberExpression (JSIdentifier _ n) _ args _) =
    (FuncInfo { calls = [nameCLToId (Name Ident n Nothing) args], consts = mempty }, S.empty)
extractCalledFunctionsExpr' (JSCallExpression (JSCallExpressionDot _ _ (JSIdentifier _ n)) _ args _) =
    let
        nm = Name Ident n Nothing
    in
    (FuncInfo { calls = [nameCLToIdWithExtraArgs nm args 1], consts = mempty }, S.singleton nm)
extractCalledFunctionsExpr' (JSMemberExpression (JSMemberDot (JSIdentifier _ first) _ (JSIdentifier _ second)) _ args _) =
    let
        nm = Name Ident (first ++ "." ++ second) Nothing
    in
    (FuncInfo {calls = [nameCLToIdWithExtraArgs nm args 1], consts = mempty }, S.empty)
extractCalledFunctionsExpr' (JSMemberExpression (JSMemberDot _ _ _) _ _ _) = error $ "extractCalledFunctionsExpr': complex JSMemberExpression"
extractCalledFunctionsExpr' _ = (mempty, S.empty)

extractDefinition :: JSAST -> Name -> Expr
extractDefinition (JSAstProgram stmts _) n = head $ filter (\e -> e /= EmptyExpr) $ map (flip extractDefinitionFxn n) stmts
extractDefinition (JSAstStatement stmt _) n = extractDefinitionFxn stmt n
extractDefinition _ _ = EmptyExpr

extractDefinitionFxn :: JSStatement -> Name -> Expr
extractDefinitionFxn (JSFunction _ ident _ args _ block _) n
    | (identToName ident == n) = mkLams (argsToId args) (extractDefinitionBlock block)
    | otherwise = EmptyExpr
extractDefinitionFxn _ _ = EmptyExpr

extractDefinitionBlock :: JSBlock -> Expr
extractDefinitionBlock (JSBlock _ b@(x:xs) _)
    | xs == [] = extractDefinitionStmt x
    | otherwise = error "More than one statement in function body"
extractDefinitionBlock _ = error "Empty function body"

extractDefinitionStmt :: JSStatement -> Expr
extractDefinitionStmt (JSReturn _ (Just e) _) = extractCallExpr e
extractDefinitionStmt _ = error "Statement is not a return followed by an expression"

extractCallExpr :: JSExpression -> Expr
extractCallExpr (JSCallExpression (JSIdentifier _ n) _ args _) =
    let
        argExprs = map extractCallExpr (argsToExpr args)
    in
    mkApp $ [Var $ Id (Name Ident n Nothing) (mkTyFun $ (map typeOf argExprs) ++ [jsIdentType])] ++ argExprs
extractCallExpr (JSMemberExpression (JSIdentifier _ n) _ args _) =
    let
        argExprs = map extractCallExpr (argsToExpr args)
    in
    mkApp $ [Var $ Id (Name Ident n Nothing) (mkTyFun $ (map typeOf argExprs) ++ [jsIdentType])] ++ argExprs
extractCallExpr (JSStringLiteral _ s) = (\(AppVal _ l) -> valToExpr l) $ jsJSONToVal (s ++ "\n")
extractCallExpr (JSDecimal _ d) = (\(AppVal _ l) -> valToExpr l) $ jsJSONToVal (d ++ "\n")
extractCallExpr (JSLiteral _ b) = valToExpr $ jsJSONToVal (b ++ "\n")
extractCallExpr i = case (jsExpressionToName i) of
                        Just n -> Var (Id n jsIdentType)
                        _ -> error "Expression not recognized"

argsToId :: JSCommaList JSIdent -> [Id]
argsToId (JSLCons list _ a) = argsToId list ++ [Id (identToName a) jsIdentType]
argsToId (JSLOne a) = [Id (identToName a) jsIdentType]

argsToExpr :: JSCommaList JSExpression -> [JSExpression]
argsToExpr (JSLCons list _ e) = argsToExpr list ++ [e]
argsToExpr (JSLOne e) = [e]

nameCLToIdWithExtraArgs :: Name -> JSCommaList a -> Int -> Id
nameCLToIdWithExtraArgs n args i =
    let
        jsident = jsIdentType
        t = foldr TyFun jsident $ replicate (commaListLength args + i) jsident
    in
    Id n t

nameCLToId :: Name -> JSCommaList a -> Id
nameCLToId n args = nameCLToIdWithExtraArgs n args 0

jsExpressionToName :: JSExpression -> Maybe Name
jsExpressionToName (JSIdentifier _ n) = Just (Name Ident n Nothing)
jsExpressionToName _ = Nothing

identToName :: JSIdent -> Name
identToName (JSIdentName _ s) = Name Ident s Nothing
identToName (JSIdentNone) = Name Ident "None" Nothing

commaListLength :: JSCommaList a -> Int
commaListLength (JSLCons cl _ _) = 1 + commaListLength cl
commaListLength (JSLOne _) = 1
commaListLength JSLNil = 0

binOpToId :: JSBinOp -> Id
binOpToId (JSBinOpAnd _) = binOp "&&"
binOpToId (JSBinOpEq _) = binOp "=="
binOpToId (JSBinOpGt _) = binOp ">"
binOpToId (JSBinOpGe _) = binOp ">="
binOpToId (JSBinOpLt _) = binOp "<"
binOpToId (JSBinOpLe _) = binOp "<="
binOpToId (JSBinOpMinus _) = binOp "-"
binOpToId (JSBinOpPlus _) = binOp "+"
binOpToId (JSBinOpTimes _) = binOp "*"
binOpToId _ = error "Unhandled Binary Operator"

binOp :: String -> Id
binOp s = Id (Name Ident s Nothing) (TyFun jsIdentType (TyFun jsIdentType jsIdentType))

$(derivingASTWithContainers ''JSExpression)
$(derivingASTWithContainers ''JSStatement)
-- $(derivingASTContainer ''JSStatement ''JSExpression)
-- $(derivingASTContainer ''JSAST ''JSExpression)
