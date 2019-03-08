module LIVS.Target.JavaScript.Interface ( 
          JavaScriptREPL
        , jsLanguageEnv
        , loadFileJavaScript
        , defJavaScript
        , callJavaScript
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

import Data.List

import Data.Attoparsec.ByteString
import Data.Aeson
import qualified Data.ByteString.Char8 as B

newtype JavaScriptREPL = JavaScriptREPL Process

jsLanguageEnv :: IO (LanguageEnv IO)
jsLanguageEnv = do
    js <- initJavaScriptREPL
    return $ LanguageEnv { load = loadFileJavaScript js
                         , def = defJavaScript js
                         , call = callJavaScript js }

loadFileJavaScript :: JavaScriptREPL -> FilePath -> IO ()
loadFileJavaScript js p = runJavaScript js $ ".load " ++ p ++ "\n"

defJavaScript :: JavaScriptREPL -> Id -> Expr -> IO ()
defJavaScript js (Id n _) = runJavaScript js . toJavaScriptDef n

callJavaScript :: JavaScriptREPL -> Expr -> IO Val
callJavaScript js e = do
    print $ toJavaScriptCall e
    r <- runAndReadJavaScript js (toJavaScriptCall e)
    case parse json $ B.pack r of
      Fail _ _ _ -> error "Bad parse"
      Partial _ -> error "Why does this happen?"
      Done _ v -> return $ toValue v

initJavaScriptREPL:: IO JavaScriptREPL
initJavaScriptREPL = do
    pr <- getProcess "node" []
    return $ JavaScriptREPL pr

runAndReadJavaScript :: JavaScriptREPL -> String -> IO String
runAndReadJavaScript (JavaScriptREPL js) = runAndReadProcess js

runJavaScript :: JavaScriptREPL -> String -> IO ()
runJavaScript (JavaScriptREPL js) s = do
    runProcess js s
    -- JavaScript gives output even when just defining a function, so we clean that
    -- up here
    _ <- readProcess js
    return ()

closeJavaScript :: JavaScriptREPL -> IO ()
closeJavaScript (JavaScriptREPL js) = closeProcess js "process.exit()\n"

toJavaScriptDef :: Name -> Expr -> String
toJavaScriptDef n e =
    let
        args = concat . intersperse " " . map toJavaScriptId $ leadingLams e
        e' = toJavaScriptExpr e
    in
        nameToString n ++ " = function (" ++ args ++ ") = {\n\t" ++ e' ++ "\n}"

toJavaScriptCall :: Expr -> String
toJavaScriptCall e = toJavaScriptExpr e ++ ";\n"

toJavaScriptExpr :: Expr -> String
toJavaScriptExpr (Var i) = toJavaScriptId i
toJavaScriptExpr (Data (DC n _)) = nameToString n
toJavaScriptExpr (Lit l) = "(" ++ toJavaScriptLit l ++ ")"
toJavaScriptExpr (Lam i e) = "(" ++ (nameToString $ idName i) ++ " => " ++ (toJavaScriptExpr e) ++ ")"
toJavaScriptExpr e@(App _ _)
    | App (App (App (Var (Id (Name "ite" _) _)) e1) e2) e3 <- e =
        "(if (" ++ toJavaScriptExpr e1 ++ ") {" ++ toJavaScriptExpr e2 ++ "} else {" ++ toJavaScriptExpr e3 ++ "}"
    | App (App (Var (Id n _)) e1) e2 <- e
    , n `elem` operators = "(" ++ toJavaScriptExpr e1 ++ " " ++ nameToString n ++ " " ++ toJavaScriptExpr e2 ++ ") "
    | otherwise = 
        "console.log(" ++ toJavaScriptExpr (appCenter e) ++ " "
            ++ (concat . intersperse " " . map toJavaScriptExpr $ appArgs e) ++ ") "
toJavaScriptExpr (Let (i, b) e) =
    toJavaScriptId i ++ " = " ++ toJavaScriptExpr b ++ " in " ++ toJavaScriptExpr e

toJavaScriptId :: Id -> String
toJavaScriptId (Id n _) = nameToString n

toJavaScriptLit :: Lit -> String
toJavaScriptLit (LInt i) = show i

operators :: [Name]
operators = [ Name "+" Nothing
            , Name "-" Nothing
            , Name "*" Nothing
            , Name ">=" Nothing
            , Name "<=" Nothing ]
