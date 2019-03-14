-- Hides the warnings about deriving 
{-# OPTIONS_GHC -fno-warn-orphans #-}

{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE TemplateHaskell #-}

module LIVS.Target.JavaScript.Extract ( module Language.JavaScript.Parser
                                      , parseJS
                                      , extractFunctions ) where

import LIVS.Language.AST
import LIVS.Language.Syntax
import LIVS.Language.Typing

import Language.JavaScript.Parser
import Language.JavaScript.Parser.AST

parseJS :: FilePath -> IO (Either String JSAST)
parseJS fp = do
    js <- readFile fp
    return $ parse js fp

extractFunctions :: JSAST -> [(Id, [Id])]
extractFunctions (JSAstProgram stmts _) = concatMap extractFunctionsStmt stmts
extractFunctions (JSAstStatement stmt _) = extractFunctionsStmt stmt
extractFunctions _ = []

extractFunctionsStmt :: JSStatement -> [(Id, [Id])]
extractFunctionsStmt (JSFunction _ ident _ args _ block _) =
    [( nameCLToId (identToName ident) args
     , extractCalledFunctionsExpr block ++ extractCalledFunctionsStmt block)]
extractFunctionsStmt _ = []

extractCalledFunctionsStmt :: ASTContainer c JSStatement => c -> [Id]
extractCalledFunctionsStmt = evalASTs extractCalledFunctionsStmt'

extractCalledFunctionsStmt' :: JSStatement -> [Id]
extractCalledFunctionsStmt' _ = []

extractCalledFunctionsExpr :: ASTContainer c JSExpression => c -> [Id]
extractCalledFunctionsExpr = evalASTs extractCalledFunctionsExpr'

extractCalledFunctionsExpr' :: JSExpression -> [Id]
extractCalledFunctionsExpr' (JSMemberExpression e _ args _) =
    case jsExpressionToName e of
        Just n -> [nameCLToId n args]
        Nothing -> [] 
extractCalledFunctionsExpr' _ = []

nameCLToId :: Name -> JSCommaList a -> Id
nameCLToId n args =
    let
        jsident = intType -- TyCon (Name "JSIdentifier" Nothing) TYPE
        t = foldr TyFun jsident $ replicate (commaListLength args) jsident
    in
    Id n t

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