module LIVS.Target.JavaScript.Interface ( 
          JavaScriptREPL
        , DotNoteNames
        , jsLanguageEnv
        , extractFileJavaScript
        , loadFileJavaScript
        , defJavaScript
        , callJavaScript
        , jsJSONToVal
        , initJavaScriptREPL
        , runAndReadJavaScript
        , runJavaScript
        , closeJavaScript
        , toJavaScriptDef
        , toJavaScriptExpr ) where

import LIVS.Language.Expr
import LIVS.Language.Naming
import LIVS.Language.Syntax
import LIVS.Target.General.LanguageEnv
import LIVS.Target.General.Process
import LIVS.Target.General.JSON
import qualified LIVS.Target.JavaScript.Extract as Ext
import LIVS.Target.JavaScript.Extract (DotNoteNames)
import LIVS.Target.JavaScript.JSIdentifier

import Data.List

import qualified Data.HashSet as S

newtype JavaScriptREPL = JavaScriptREPL Process

jsLanguageEnv :: IO (LanguageEnv IO (S.HashSet Name))
jsLanguageEnv = do
    js <- initJavaScriptREPL
    return $ LanguageEnv { extract = extractFileJavaScript
                         , load = loadFileJavaScript js
                         , def = defJavaScript js
                         , call = callJavaScript js }

extractFileJavaScript :: FilePath -> IO ([(Id, FuncInfo)], S.HashSet Name)
extractFileJavaScript fp = do
    jsast <- Ext.parseJS fp
    case jsast of
        Left e -> error $ show e
        Right jsast' -> return $ Ext.extractFunctions jsast'

loadFileJavaScript :: JavaScriptREPL -> FilePath -> IO ()
loadFileJavaScript js p = do
    _ <- runAndReadJavaScript js $ "LOAD " ++ p ++ "\n"
    return ()

defJavaScript :: JavaScriptREPL -> DotNoteNames -> Id -> Expr -> IO ()
defJavaScript js dnn (Id n _) e = do
    _ <- runAndReadJavaScript js $ toJavaScriptDef dnn n e
    return ()

callJavaScript :: JavaScriptREPL -> DotNoteNames -> Expr -> IO Val
callJavaScript js dnn e = do
    r <- runAndReadJavaScript js (toJavaScriptCall dnn e)
    -- putStrLn $ "call = " ++ toJavaScriptCall dnn e
    -- putStrLn $ "r = " ++ r

    return $ jsJSONToVal r

initJavaScriptREPL:: IO JavaScriptREPL
initJavaScriptREPL = do
    pr <- getProcess "node" ["language_interface/nodeREPL.js"]
    return $ JavaScriptREPL pr

runAndReadJavaScript :: JavaScriptREPL -> String -> IO String
runAndReadJavaScript (JavaScriptREPL js) = runAndReadProcess js

runJavaScript :: JavaScriptREPL -> String -> IO ()
runJavaScript (JavaScriptREPL js) s = runProcess js s

closeJavaScript :: JavaScriptREPL -> IO ()
closeJavaScript (JavaScriptREPL js) = closeProcess js "process.exit()\n"

toJavaScriptDef :: DotNoteNames -> Name -> Expr -> String
toJavaScriptDef dnn n e =
    let
        args = concat . intersperse " " . map toJavaScriptId $ leadingLams e
        e' = toJavaScriptExpr dnn $ stripLeadingLams e
    in
    nameToString n ++ " = function (" ++ args ++ ") { return " ++ e' ++ "}\n"

toJavaScriptCall :: DotNoteNames -> Expr -> String
toJavaScriptCall dnn e = toJavaScriptExpr dnn e ++ ";\n"

toJavaScriptExpr :: DotNoteNames -> Expr -> String
toJavaScriptExpr _ (Var i) = toJavaScriptId i
toJavaScriptExpr _ (Data dc)
    | dc == trueDC = "true"
    | dc == falseDC = "false"
    | dc == jsNaNDC = "NaN"
    | dc == jsErrorDC = "(0).indexof(\"\")" -- Throws a JS type error intentionally 
    | otherwise = ""
toJavaScriptExpr _ (Lit l) = "(" ++ toJavaScriptLit l ++ ")"
toJavaScriptExpr dnn (Lam i e) = "(" ++ (nameToString $ idName i) ++ " => " ++ (toJavaScriptExpr dnn e) ++ ")"
toJavaScriptExpr dnn e@(App _ _)
    | App (App (App (Var (Id (Name _ "ite" _) _)) e1) e2) e3 <- e =
        "(" ++ toJavaScriptExpr dnn e1 ++ "?" ++ toJavaScriptExpr dnn e2 ++ ":" ++ toJavaScriptExpr dnn e3 ++ ")"
        -- "(if (" ++ toJavaScriptExpr e1 ++ ") {" ++ toJavaScriptExpr e2 ++ "} else {" ++ toJavaScriptExpr e3 ++ "})"
    | App (App (Var (Id n _)) e1) e2 <- e
    , n `elem` operators = "(" ++ toJavaScriptExpr dnn e1 ++ " " ++ nameToString n ++ " " ++ toJavaScriptExpr dnn e2 ++ ") "
    | v@(Var (Id n _)):e:es <- unApp e
    , n `S.member` dnn =
        "(" ++ toJavaScriptExpr dnn e ++ "." ++ toJavaScriptExpr dnn v ++ "("
        ++ (concat . intersperse ", " $ map (toJavaScriptExpr dnn) es) ++ "))"
    | otherwise = 
        "(" ++ toJavaScriptExpr dnn (appCenter e) ++ "("
            ++ (concat . intersperse ", " . map (toJavaScriptExpr dnn) $ appArgs e) ++ "))"
toJavaScriptExpr dnn (Let (i, b) e) =
    toJavaScriptId i ++ " = " ++ toJavaScriptExpr dnn b ++ " in " ++ toJavaScriptExpr dnn e

toJavaScriptId :: Id -> String
toJavaScriptId (Id n _) = nameToString n

toJavaScriptLit :: Lit -> String
toJavaScriptLit (LInt i) = show i
toJavaScriptLit (LString s) = show s

operators :: [Name]
operators = [ Name Ident "+" Nothing
            , Name Ident "-" Nothing
            , Name Ident "*" Nothing
            , Name Ident "=" Nothing
            , Name Ident "==" Nothing
            , Name Ident ">=" Nothing
            , Name Ident "<=" Nothing ]
