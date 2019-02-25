module Main where

import LIVS.Core.Fuzz
import LIVS.Core.LIVS

import qualified LIVS.Language.Heap as H

import LIVS.Language.CallGraph
import LIVS.Language.Syntax
import LIVS.Language.Typing

import LIVS.Sygus.CVC4Interface
import LIVS.Sygus.SMTLexer
import LIVS.Sygus.ToSygus

import LIVS.Target.OCaml.Interface

import Control.Monad.IO.Class

main :: IO ()
main = do
    let h = H.fromList [ ("add", H.Def $ Lam 
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
                                ))
                        , ("+", H.Primitive $ TyFun intType (TyFun intType intType))]
        cg = createCallGraph
            [ (Id "add" (TyFun intType (TyFun intType intType)), [Id "+" (TyFun intType (TyFun intType intType))])
            , (Id "+" (TyFun intType (TyFun intType intType)), []) ]

    let form = toSygus cg h examples

    putStrLn form

    putStrLn ""

    -- cvc4 <- getCVC4
    -- putStrLn "Right before"
    -- r <- runAndReadCVC4 cvc4 form
    -- putStrLn "Right after"

    r <- runCVC4WithFile form

    putStrLn r

    let l = lexSMT r
    putStrLn $ show l

    -- closeCVC4 cvc4

    -- mapM_ (putStrLn . uncurry toPythonExpr) . H.toList $ H.filter H.isDef h
    -- mapM_ (putStrLn . toPythonExpr "f") p

    ocaml <- getOCaml
    putStrLn "Got ocaml"

    mapM_ (\(n, hObj) -> case hObj of
                        H.Def e -> runOCaml ocaml $ toOCamlDef n e
                        _ -> return ()) . H.toList $ H.filter H.isDefObj h
    putStrLn "Ran ocaml"

    -- print (OCaml.parse . OCaml.lexer $ r1)
    -- putStrLn "Ran ocaml 2"
    -- r2 <- runAndReadOCaml ocaml ("add 2 3;;\n")
    -- print (OCaml.parse . OCaml.lexer $ r2)

    es <- fuzzExamplesM (callOCaml ocaml) 2 (Id "abs" (TyFun intType intType))
    print es

    let livsH = H.fromList [ ("+", H.Primitive $ TyFun intType (TyFun intType intType))
                           , ("-", H.Primitive $ TyFun intType (TyFun intType intType))
                           , ("=", H.Primitive $ TyFun intType (TyFun intType boolType))
                           , (">=", H.Primitive $ TyFun intType (TyFun intType boolType))
                           , ("ite", H.Primitive $ TyFun boolType (TyFun intType (TyFun intType intType)))]

    putStrLn "HERE"
    loadFileOCaml ocaml "target_files/OCaml/ints.ml"
    lr <- liftIO $ livsCVC4 (defOCaml ocaml) (callOCaml ocaml) graph livsH
    print lr

    -- python <- getPython
    -- putStrLn "Got python"
    -- mapM_ (runPython python . uncurry toPythonExpr) $ H.toList h
    -- putStrLn "Ran python"
    -- print =<< runAndReadPython python ("add(1, 2)\n")

graph :: CallGraph
graph = createCallGraph
    [ (Id "double" (TyFun intType intType), [Id "add" (TyFun intType (TyFun intType intType))])
    , (Id "quadruple" (TyFun intType intType), [Id "double" (TyFun intType intType)])
    , (Id "add" (TyFun intType (TyFun intType intType)), [Id "+" (TyFun intType (TyFun intType intType))])
    , (Id "abs2" (TyFun intType intType), [ Id "-" (TyFun intType (TyFun intType intType))
                                          , Id ">=" (TyFun intType (TyFun intType boolType))
                                          , Id "ite" (TyFun boolType (TyFun intType (TyFun intType intType)))])
    , (Id "abs3" (TyFun intType intType), [ Id "abs2" (TyFun intType intType) ])
    , (Id "abs4" (TyFun intType intType), [ Id "abs3" (TyFun intType intType) ]) ]


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