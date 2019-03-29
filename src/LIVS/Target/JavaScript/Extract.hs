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
import LIVS.Language.Typing
import LIVS.Target.JavaScript.JSIdentifier

import Language.JavaScript.Parser
import Language.JavaScript.Parser.AST

import qualified Data.HashSet as S

-- | A set of names that use dot notation.
type DotNoteNames = S.HashSet Name

parseJS :: FilePath -> IO (Either String JSAST)
parseJS fp = do
    js <- readFile fp
    return $ parse js fp

extractFunctions :: JSAST -> ([(Id, [Id])], S.HashSet Name)
extractFunctions (JSAstProgram stmts _) = mconcat $ map extractFunctionsStmt stmts
extractFunctions (JSAstStatement stmt _) = extractFunctionsStmt stmt
extractFunctions _ = ([], S.empty)

extractFunctionsStmt :: JSStatement -> ([(Id, [Id])], DotNoteNames)
extractFunctionsStmt (JSFunction _ ident _ args _ block _) =
    let
        (is, ns) = extractCalledFunctionsExpr block
        (is', ns') = extractCalledFunctionsStmt block
    in
    ([( nameCLToId (identToName ident) args, is ++ is')], S.union ns ns')
extractFunctionsStmt _ = ([], S.empty)

extractCalledFunctionsStmt :: ASTContainer c JSStatement => c -> ([Id], DotNoteNames)
extractCalledFunctionsStmt = evalASTs extractCalledFunctionsStmt'

extractCalledFunctionsStmt' :: JSStatement -> ([Id], S.HashSet Name)
extractCalledFunctionsStmt' _ = ([], S.empty)

extractCalledFunctionsExpr :: ASTContainer c JSExpression => c -> ([Id], DotNoteNames)
extractCalledFunctionsExpr = evalASTs extractCalledFunctionsExpr'

extractCalledFunctionsExpr' :: JSExpression -> ([Id], DotNoteNames)
-- extractCalledFunctionsExpr' (JSCallExpression e _ es _) = error $ "e = " ++ show e ++ " es = " ++ show es
-- extractCalledFunctionsExpr' (JSCallExpressionDot e _ es) = error $ "e = " ++ show e ++ " es = " ++ show es
-- extractCalledFunctionsExpr' (JSMemberDot e _ le) = error $ "e = " ++ show e ++ " le = " ++ show le
extractCalledFunctionsExpr' (JSMemberExpression (JSIdentifier _ n) _ args _) =
    ([nameCLToId (Name n Nothing) args], S.empty)
extractCalledFunctionsExpr' (JSMemberExpression (JSMemberDot _ _ (JSIdentifier _ n)) _ args _) =
    let
        nm = Name n Nothing
    in
    ([nameCLToIdWithExtraArgs nm args 1], S.singleton nm)
extractCalledFunctionsExpr' _ = ([], S.empty)

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
jsExpressionToName (JSIdentifier _ n) = Just (Name n Nothing)
jsExpressionToName _ = Nothing

identToName :: JSIdent -> Name
identToName (JSIdentName _ s) = Name s Nothing
identToName (JSIdentNone) = Name "None" Nothing

commaListLength :: JSCommaList a -> Int
commaListLength (JSLCons cl _ _) = 1 + commaListLength cl
commaListLength (JSLOne _) = 1
commaListLength JSLNil = 0

$(derivingASTWithContainers ''JSExpression)
$(derivingASTWithContainers ''JSStatement)
$(derivingASTContainer ''JSStatement ''JSExpression)
$(derivingASTContainer ''JSAST ''JSExpression)