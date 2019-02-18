module Lava.Target.OCaml.Interface ( OCaml
                                   , getOCaml
                                   , runAndReadOCaml
                                   , runOCaml
                                   , closeOCaml
                                   , toOCamlExpr ) where

import Lava.Language.Expr
import Lava.Language.Syntax
import Lava.Target.General.Process

import Data.List

newtype OCaml = OCaml Process

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

toOCamlExpr :: Name -> Expr -> String
toOCamlExpr n e =
    let
        as = concat . intersperse " " . map toOCamlId $ leadingLams e
        e' = toOCamlExpr' e
    in
    "let " ++ n ++ " " ++ as ++ " =\n\t" ++ e' ++ ";;\n"

toOCamlExpr' :: Expr -> String
toOCamlExpr' (Var i) = toOCamlId i
toOCamlExpr' (Lam _ e) = toOCamlExpr' e
toOCamlExpr' e@(App _ _)
    | App (App (Var (Id n _)) e1) e2 <- e
    , n `elem` operators = toOCamlExpr' e2 ++ " " ++ n ++ " " ++ toOCamlExpr' e1
    | otherwise = 
        toOCamlExpr' (appCenter e)
            ++ "(" ++ (concat . intersperse " " . map toOCamlExpr' $ appArgs e) ++ ")"
toOCamlExpr' (Lit l) = toOCamlLit l

toOCamlId :: Id -> String
toOCamlId (Id n _) = n

toOCamlLit :: Lit -> String
toOCamlLit (LInt i) = show i

operators :: [Name]
operators = ["+", "-", "*"]