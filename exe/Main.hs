module Main where

import qualified Lava.Language.Heap as H
import Lava.Language.Syntax
import Lava.Language.Typing

import Lava.Sygus.CVC4Interface
import Lava.Sygus.SMTParser
import Lava.Sygus.SMTLexer
import Lava.Sygus.ToSygus

import Lava.Target.OCaml.Interface
import Lava.Target.Python.Interface

import qualified Data.Map as M

main :: IO ()
main = do
    let h = H.fromList [("add", Lam 
                                (Id "x" intType) 
                                (Lam 
                                    (Id "y" intType) 
                                    (App 
                                        (App 
                                            (Var (Id "+" (TyFun intType (TyFun intType intType))))
                                            (Var (Id "y" intType))
                                        )
                                        (Var (Id "x" intType))
                                    )
                                ))]

    let form = toSygus h examples

    putStrLn form

    putStrLn ""

    cvc4 <- getCVC4
    r <- runAndReadCVC4 cvc4 form

    putStrLn r

    let l = lexer r
    putStrLn $ show l

    let p = parse (M.fromList [("+", TyFun intType (TyFun intType intType))]) l
    putStrLn $ show p

    
    mapM_ (putStrLn . uncurry toPythonExpr) $ H.toList h
    mapM_ (putStrLn . toPythonExpr "f") p

    ocaml <- getOCaml
    putStrLn "Got ocaml"
    mapM_ (runOCaml ocaml . uncurry toOCamlExpr) $ H.toList h
    putStrLn "Ran ocaml"
    print =<< runAndReadOCaml ocaml ("add 1 2;;\n")
    putStrLn "Ran ocaml 2"
    print =<< runAndReadOCaml ocaml ("add 2 3;;\n")

    python <- getPython
    putStrLn "Got python"
    mapM_ (runPython python . uncurry toPythonExpr) $ H.toList h
    putStrLn "Ran python"
    print =<< runAndReadPython python ("add(1, 2)\n")

examples :: [Example]
examples = [ Example { func_name = "double"
                     , input = [LInt 1]
                     , output = LInt 2 }
           , Example { func_name = "double"
                     , input = [LInt 2]
                     , output = LInt 4 }
           -- , Example { func_name = "doubleAndAdd"
           --           , input = [LInt 2, LInt 3]
           --           , output = LInt 10 }
           -- , Example { func_name = "doubleAndAdd"
           --           , input = [LInt 3, LInt 4]
           --           , output = LInt 14 }
           ]