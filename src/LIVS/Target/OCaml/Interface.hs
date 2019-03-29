module LIVS.Target.OCaml.Interface ( OCaml
                                   , ocamlLanguageEnv
                                   , loadFileOCaml
                                   , defOCaml
                                   , callOCaml
                                   , getOCaml
                                   , runAndReadOCaml
                                   , runOCaml
                                   , closeOCaml
                                   , toOCamlDef
                                   , toOCamlExpr ) where

import LIVS.Language.Expr
import LIVS.Language.Naming
import LIVS.Language.Syntax
import LIVS.Target.General.LanguageEnv
import LIVS.Target.General.Process
import LIVS.Target.OCaml.LexerCL
import LIVS.Target.OCaml.ParserCL

import Data.List
newtype OCaml = OCaml Process

ocamlLanguageEnv :: IO (LanguageEnv IO ())
ocamlLanguageEnv = do
    ocaml <- getOCaml
    return $ LanguageEnv { load = loadFileOCaml ocaml
                         , def = \_ -> defOCaml ocaml
                         , call = \_ -> callOCaml ocaml }

loadFileOCaml :: OCaml -> FilePath -> IO ()
loadFileOCaml ocaml p = runOCaml ocaml $ "#use \"" ++ p ++ "\";;\n"

defOCaml :: OCaml -> Id -> Expr -> IO ()
defOCaml ocaml (Id n _) = runOCaml ocaml . toOCamlDef n

callOCaml :: OCaml -> Expr -> IO Val
callOCaml ocaml e = do
    r <- runAndReadOCaml ocaml (toOCamlCall e)
    lx <- return . lexer $ r
    case lx of
        Right l -> return . parse $ l
        Left err -> error $ err ++ "\n" ++ show r

getOCaml :: IO OCaml
getOCaml = do
    pr <- getProcess "ocaml" []
    _ <- readProcess pr
    return $ OCaml pr

runAndReadOCaml :: OCaml -> String -> IO String
runAndReadOCaml (OCaml ocaml) = runAndReadProcess ocaml

runOCaml :: OCaml -> String -> IO ()
runOCaml (OCaml ocaml) s = do
    runProcess ocaml s
    -- OCaml gives output even when just defining a function, so we clean that
    -- up here

    _ <- readProcess ocaml
    return ()

closeOCaml :: OCaml -> IO ()
closeOCaml (OCaml ocaml) = closeProcess ocaml "exit 0;;\n"

toOCamlDef :: Name -> Expr -> String
toOCamlDef n e =
    let
        as = concat . intersperse " " . map toOCamlId $ leadingLams e
        e' = toOCamlExpr e
    in
    "let " ++ nameToString n ++ " " ++ as ++ " =\n\t" ++ e' ++ ";;\n"

toOCamlCall :: Expr -> String
toOCamlCall e = toOCamlExpr e ++ ";;\n"

toOCamlExpr :: Expr -> String
toOCamlExpr (Var i) = toOCamlId i
toOCamlExpr (Data (DC n _)) = nameToString n
toOCamlExpr (Lit l) = "(" ++ toOCamlLit l ++ ")"
toOCamlExpr (Lam _ e) = toOCamlExpr e
toOCamlExpr e@(App _ _)
    | App (App (App (Var (Id (Name "ite" _) _)) e1) e2) e3 <- e =
        "(if " ++ toOCamlExpr e1 ++ " then " ++ toOCamlExpr e2 ++ " else " ++ toOCamlExpr e3 ++ ")"
    | App (App (Var (Id n _)) e1) e2 <- e
    , n `elem` operators = "(" ++ toOCamlExpr e1 ++ " " ++ nameToString n ++ " " ++ toOCamlExpr e2 ++ ") "
    | otherwise = 
        "(" ++ toOCamlExpr (appCenter e) ++ " "
            ++ (concat . intersperse " " . map toOCamlExpr $ appArgs e) ++ ") "
toOCamlExpr (Let (i, b) e) =
    "let " ++ toOCamlId i ++ " = " ++ toOCamlExpr b ++ " in " ++ toOCamlExpr e

toOCamlId :: Id -> String
toOCamlId (Id n _) = nameToString n

toOCamlLit :: Lit -> String
toOCamlLit (LInt i) = show i

operators :: [Name]
operators = [ Name "+" Nothing
            , Name "-" Nothing
            , Name "*" Nothing
            , Name ">=" Nothing
            , Name "<=" Nothing ]