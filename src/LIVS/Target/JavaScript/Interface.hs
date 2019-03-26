module LIVS.Target.JavaScript.Interface ( 
          JavaScriptREPL
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
import LIVS.Target.JavaScript.JSIdentifier

import Data.List

import Data.Attoparsec.ByteString
import Data.Aeson
import qualified Data.ByteString.Char8 as B

newtype JavaScriptREPL = JavaScriptREPL Process

jsLanguageEnv :: IO (LanguageEnv IO)
jsLanguageEnv = do
    js <- initJavaScriptREPL
    return $ LanguageEnv { extract = extractFileJavaScript
                         , load = loadFileJavaScript js
                         , def = defJavaScript js
                         , call = callJavaScript js }

extractFileJavaScript :: FilePath -> IO [ (Id, [Id]) ]
extractFileJavaScript fp = do
    jsast <- Ext.parseJS fp
    case jsast of
        Left e -> error $ show e
        Right jsast' -> return $ Ext.extractFunctions jsast'

loadFileJavaScript :: JavaScriptREPL -> FilePath -> IO ()
loadFileJavaScript js p = do
    _ <- runAndReadJavaScript js $ "LOAD " ++ p ++ "\n"
    return ()

defJavaScript :: JavaScriptREPL -> Id -> Expr -> IO ()
defJavaScript js (Id n _) = runJavaScript js . toJavaScriptDef n

callJavaScript :: JavaScriptREPL -> Expr -> IO Val
callJavaScript js e = do
    r <- runAndReadJavaScript js (toJavaScriptCall e)
    putStrLn $ toJavaScriptCall e
    putStrLn $ "r = " ++ r

    return $ jsJSONToVal r

jsJSONToVal :: String -> Val
jsJSONToVal s =
    case parse json $ B.pack $ map repSnglWithDbl s of
      Fail _ _ _
        | 'N':'a':'N':_ <- s -> DataVal jsNaNDC
      Fail i _ err -> error $ "Bad parse\ni = " ++ show i ++ "\nerr = " ++ err
      Partial _ -> error "Why does this happen?"
      Done _ v -> toValue v
    where
        -- | JavaScript outputs JSON with single quotes, but Aeson
        -- expects double quotes
        repSnglWithDbl '\'' = '\"'
        repSnglWithDbl c = c

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

toJavaScriptDef :: Name -> Expr -> String
toJavaScriptDef n e =
    let
        args = concat . intersperse " " . map toJavaScriptId $ leadingLams e
        e' = toJavaScriptExpr $ stripLeadingLams e
    in
        nameToString n ++ " = function (" ++ args ++ ") {\n\t" ++ e' ++ "\n}"

toJavaScriptCall :: Expr -> String
toJavaScriptCall e = toJavaScriptExpr e ++ ";\n"

toJavaScriptExpr :: Expr -> String
toJavaScriptExpr (Var i) = toJavaScriptId i
toJavaScriptExpr (Data dc)
    | dc == trueDC = "true"
    | dc == falseDC = "false"
    | dc == jsNaNDC = "NaN"
    | otherwise = ""
toJavaScriptExpr (Lit l) = "(" ++ toJavaScriptLit l ++ ")"
toJavaScriptExpr (Lam i e) = "(" ++ (nameToString $ idName i) ++ " => " ++ (toJavaScriptExpr e) ++ ")"
toJavaScriptExpr e@(App _ _)
    | App (App (App (Var (Id (Name "ite" _) _)) e1) e2) e3 <- e =
        "if (" ++ toJavaScriptExpr e1 ++ ") {" ++ toJavaScriptExpr e2 ++ "} else {" ++ toJavaScriptExpr e3 ++ "}"
    | App (App (Var (Id n _)) e1) e2 <- e
    , n `elem` operators = "(" ++ toJavaScriptExpr e1 ++ " " ++ nameToString n ++ " " ++ toJavaScriptExpr e2 ++ ") "
    | otherwise = 
        "(" ++ toJavaScriptExpr (appCenter e) ++ "("
            ++ (concat . intersperse ", " . map toJavaScriptExpr $ appArgs e) ++ ")) "
toJavaScriptExpr (Let (i, b) e) =
    toJavaScriptId i ++ " = " ++ toJavaScriptExpr b ++ " in " ++ toJavaScriptExpr e

toJavaScriptId :: Id -> String
toJavaScriptId (Id n _) = nameToString n

toJavaScriptLit :: Lit -> String
toJavaScriptLit (LInt i) = show i
toJavaScriptLit (LString s) = show s

operators :: [Name]
operators = [ Name "+" Nothing
            , Name "-" Nothing
            , Name "*" Nothing
            , Name "=" Nothing
            , Name ">=" Nothing
            , Name "<=" Nothing ]
