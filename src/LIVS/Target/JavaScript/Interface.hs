module LIVS.Target.JavaScript.Interface (
          JavaScriptREPL
        , DotNoteNames
        , jsLanguageEnv
        , extractDefinedFileJavaScript
        , extractFileJavaScript
        , extractJavaScriptDefinitions
        , extractJavaScriptDefinition
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
import Data.Maybe

import qualified Data.HashSet as S
import qualified Data.HashMap.Lazy as HM

newtype JavaScriptREPL = JavaScriptREPL Process

jsLanguageEnv :: IO (LanguageEnv IO (S.HashSet Name))
jsLanguageEnv = do
    js <- initJavaScriptREPL
    return $ LanguageEnv { extractCalls = extractDefinedFileJavaScript
                         , extractDefs = extractJavaScriptDefinitions
                         , load = loadFileJavaScript js
                         , def = defJavaScript js
                         , call = callJavaScript js }

extractDefinedFileJavaScript :: FilePath -> IO ([(Id, FuncInfo)], S.HashSet Name)
extractDefinedFileJavaScript fp = do
    jsast <- Ext.parseJS fp
    case jsast of
        Left e -> error $ show e
        Right jsast' -> do
            let def = Ext.extractDefinedFunctions jsast'
                (allF, hsn) = Ext.extractFunctions jsast'

            return (mapMaybe (rel def) allF, hsn)

    where
        rel :: [Id] -> (Id, FuncInfo) -> Maybe (Id, FuncInfo)
        rel is (i, fi@(FuncInfo {calls = ci }))
            | i `elem` is = Just (i, fi { calls = filter (`elem` is) ci })
            | otherwise = Nothing

extractFileJavaScript :: FilePath -> IO ([(Id, FuncInfo)], S.HashSet Name)
extractFileJavaScript fp = do
    jsast <- Ext.parseJS fp
    case jsast of
        Left e -> error $ show e
        Right jsast' -> return $ Ext.extractFunctions jsast'

extractJavaScriptDefinitions :: FilePath -> [Name] -> IO (HM.HashMap Name Expr)
extractJavaScriptDefinitions fp names = do
    jsast <- Ext.parseJS fp
    case jsast of
        Left e -> error $ show e
        Right jsast' -> return (HM.fromList $ map (\n -> (n, Ext.extractDefinition jsast' n)) names)

extractJavaScriptDefinition :: FilePath -> Name -> IO Expr
extractJavaScriptDefinition fp n = do
    jsast <- Ext.parseJS fp
    case jsast of
        Left e -> error $ show e
        Right jsast' -> return $ Ext.extractDefinition jsast' n

loadFileJavaScript :: JavaScriptREPL -> FilePath -> IO ()
loadFileJavaScript js p = do
    _ <- runAndReadJavaScript js $ "LOAD " ++ p ++ "\n"
    return ()

defJavaScript :: JavaScriptREPL -> DotNoteNames -> Id -> Expr -> IO ()
defJavaScript js dnn (Id n _) e = do
    let d = toJavaScriptDef dnn n e
    _ <- runAndReadJavaScript js d
    return ()

callJavaScript :: JavaScriptREPL -> DotNoteNames -> Expr -> IO Val
callJavaScript js dnn e = do
    let c = toJavaScriptCall dnn e
    r <- runAndReadJavaScript js c
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
        e' = putNothing e

        args = concat . intersperse ", " . map toJavaScriptId $ leadingLams e'
        e'' = toJavaScriptExpr dnn $ stripLeadingLams e'
    in
    nameToString n ++ " = function (" ++ args ++ ") { return " ++ e'' ++ "}\n"
    where
        putNothing (Var (Id n t)) = Var (Id (subsName n) t)
        putNothing (Lam i e) = Lam i (putNothing e)
        putNothing (App e1 e2) = App (putNothing e1) (putNothing e2)
        putNothing (Let (b, e1) e2) = Let (b, putNothing e1) (putNothing e2)
        putNothing e = e

        subsName name@(Name ll n' _) =
            if (Name ll n' Nothing) `S.member` dnn then Name ll n' Nothing else name

toJavaScriptCall :: DotNoteNames -> Expr -> String
toJavaScriptCall dnn (Var i) = toJavaScriptId i ++ "();\n"
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
    , nameToString n `elem` operators = "(" ++ toJavaScriptExpr dnn e1 ++ " " ++ nameToString n ++ " " ++ toJavaScriptExpr dnn e2 ++ ") "
    | App (Var (Id n _)) e2 <- e
    , n == jsIntSelectorName
        || n == jsStringSelectorName
        || n == jsBoolSelectorName = toJavaScriptExpr dnn e2
    | v@(Var (Id n _)):ex:es <- unApp e
    , n `S.member` dnn =
        "(" ++ toJavaScriptExpr dnn ex ++ "." ++ toJavaScriptExpr dnn v ++ "("
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
toJavaScriptLit (LFloat f) = show f
toJavaScriptLit (LString s) = show s

operators :: [String]
operators = [ "+"
            , "-"
            , "*"
            , "="
            , "=="
            , ">="
            , "<="
            , ">"
            , "<"
            , "&&" ]
