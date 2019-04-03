-- Hides the warnings about deriving 
{-# OPTIONS_GHC -fno-warn-orphans #-}

{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE TemplateHaskell #-}

module LIVS.Target.JavaScript.Extract ( module Language.JavaScript.Parser
                                      , DotNoteNames
                                      , parseJS
                                      , extractFunctions ) where

import LIVS.Language.AST
import LIVS.Language.Syntax
import LIVS.Target.General.LanguageEnv
import LIVS.Target.General.JSON
import LIVS.Target.JavaScript.JSIdentifier

import Language.JavaScript.Parser
import Language.JavaScript.Parser.AST

import qualified Data.HashSet as S
import Data.Semigroup

-- | A set of names that use dot notation.
type DotNoteNames = S.HashSet Name

parseJS :: FilePath -> IO (Either String JSAST)
parseJS fp = do
    js <- readFile fp
    return $ parse js fp

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
-- extractCalledFunctionsExpr' (JSLiteral _ l) = error $ "lit = " ++ show l
extractCalledFunctionsExpr' (JSExpressionBinary _ bop _) =
    (FuncInfo { calls = [binOpToId bop], consts = mempty}, S.empty)
extractCalledFunctionsExpr' (JSMemberExpression (JSIdentifier _ n) _ args _) =
    (FuncInfo { calls = [nameCLToId (Name Ident n Nothing) args], consts = mempty }, S.empty)
extractCalledFunctionsExpr' (JSMemberExpression (JSMemberDot _ _ (JSIdentifier _ n)) _ args _) =
    let
        nm = Name Ident n Nothing
    in
    (FuncInfo {calls = [nameCLToIdWithExtraArgs nm args 1], consts = mempty }, S.singleton nm)
extractCalledFunctionsExpr' _ = (mempty, S.empty)

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
binOpToId (JSBinOpEq _) = binOp "=="
binOpToId (JSBinOpGe _) = binOp ">="
binOpToId (JSBinOpMinus _) = binOp "-"
binOpToId (JSBinOpPlus _) = binOp "+"
binOpToId (JSBinOpTimes _) = binOp "*"
binOpToId _ = error "Unhandled Binary Operator"

binOp :: String -> Id
binOp s = Id (Name Ident s Nothing) (TyFun jsIdentType (TyFun jsIdentType jsIdentType))

$(derivingASTWithContainers ''JSExpression)
$(derivingASTWithContainers ''JSStatement)
$(derivingASTContainer ''JSStatement ''JSExpression)
$(derivingASTContainer ''JSAST ''JSExpression)