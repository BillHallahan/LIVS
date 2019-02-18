module Lava.Target.Python.Interface ( Python
                                    , getPython
                                    , runAndReadPython
                                    , runPython
                                    , closePython
                                    , toPythonExpr ) where

import Lava.Language.Expr
import Lava.Language.Syntax
import Lava.Target.General.Process

import Data.List

newtype Python = Python Process

getPython :: IO Python
getPython = return . Python =<< getProcess "python" []

runAndReadPython :: Python -> String -> IO String
runAndReadPython (Python python) = runAndReadProcess python

runPython :: Python -> String -> IO ()
runPython (Python python) = runProcess python

closePython :: Python -> IO ()
closePython (Python python) = closeProcess python "exit()"

toPythonExpr :: Name -> Expr -> String
toPythonExpr n e =
    let
        as = concat . intersperse ", " . map toPythonId $ leadingLams e
        e' = toPythonExpr' e
    in
    "def " ++ n ++ "(" ++ as ++ "):\n\treturn (" ++ e' ++ ")\n\n"

toPythonExpr' :: Expr -> String
toPythonExpr' (Var i) = toPythonId i
toPythonExpr' (Lam _ e) = toPythonExpr' e
toPythonExpr' e@(App _ _)
    | App (App (Var (Id n _)) e1) e2 <- e
    , n `elem` operators = toPythonExpr' e2 ++ " " ++ n ++ " " ++ toPythonExpr' e1
    | otherwise = 
        toPythonExpr' (appCenter e)
            ++ "(" ++ (concat . intersperse ", " . map toPythonExpr' $ appArgs e) ++ ")"
toPythonExpr' (Lit l) = toPythonLit l

toPythonId :: Id -> String
toPythonId (Id n _) = n

toPythonLit :: Lit -> String
toPythonLit (LInt i) = show i

operators :: [Name]
operators = ["+", "-", "*"]