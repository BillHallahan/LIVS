module Main where

import LIVS.Core.Fuzz
import LIVS.Core.LIVS

import qualified LIVS.Language.Heap as H

import LIVS.Language.CallGraph
import LIVS.Language.Syntax
import LIVS.Language.Typing

import LIVS.Sygus.CVC4Interface
import LIVS.Sygus.SMTParser
import LIVS.Sygus.SMTLexer
import LIVS.Sygus.ToSygus

import LIVS.Target.OCaml.Interface
import qualified LIVS.Target.OCaml.LexerCL as OCaml
import qualified LIVS.Target.OCaml.ParserCL as OCaml
import LIVS.Target.Python.Interface

import Control.Monad.IO.Class
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
    putStrLn "Right before"
    r <- runAndReadCVC4 cvc4 form
    putStrLn "Right after"

    putStrLn r

    let l = lexer r
    putStrLn $ show l

    let p = parse (M.fromList [("+", TyFun intType (TyFun intType intType))]) l
    putStrLn $ show p

    
    mapM_ (putStrLn . uncurry toPythonExpr) $ H.toList h
    mapM_ (putStrLn . toPythonExpr "f") p

    ocaml <- getOCaml
    putStrLn "Got ocaml"

    mapM_ (runOCaml ocaml . uncurry toOCamlDef) $ H.toList h
    putStrLn "Ran ocaml"
    r1 <- runAndReadOCaml ocaml ("add 1 2;;\n")

    print (OCaml.parse . OCaml.lexer $ r1)
    putStrLn "Ran ocaml 2"
    r2 <- runAndReadOCaml ocaml ("add 2 3;;\n")
    print (OCaml.parse . OCaml.lexer $ r2)

    es <- fuzzExamplesM (callOCaml ocaml) (Id "abs" (TyFun intType intType)) 5
    print es

    -- lr <- liftIO $ livs (defOCaml ocaml) (callOCaml ocaml) cvc4 graph
    -- print lr

    -- python <- getPython
    -- putStrLn "Got python"
    -- mapM_ (runPython python . uncurry toPythonExpr) $ H.toList h
    -- putStrLn "Ran python"
    -- print =<< runAndReadPython python ("add(1, 2)\n")

graph :: CallGraph
graph = createCallGraph
    [ (Id "double" (TyFun intType intType), [Id "add" (TyFun intType intType)])
    , (Id "add" (TyFun intType intType), []) ]


examples :: [Example]
examples = [ Example { func = Id "double" (TyFun intType intType)
                     , input = [LInt 1]
                     , output = LInt 2 }
           , Example { func = Id "double" (TyFun intType intType)
                     , input = [LInt 2]
                     , output = LInt 4 }
           -- , Example { func_name = "doubleAndAdd"
           --           , input = [LInt 2, LInt 3]
           --           , output = LInt 10 }
           -- , Example { func_name = "doubleAndAdd"
           --           , input = [LInt 3, LInt 4]
           --           , output = LInt 14 }
           ]