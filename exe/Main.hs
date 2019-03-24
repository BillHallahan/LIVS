module Main where

import LIVS.Core.LIVS

import LIVS.Config.Config

import LIVS.Interpreter.Interpreter

import LIVS.Language.AST
import LIVS.Language.CallGraph
import qualified LIVS.Language.Heap as H
import LIVS.Language.Naming
import LIVS.Language.Syntax
import qualified LIVS.Language.TypeEnv as T
import LIVS.Language.Typing

import LIVS.Sygus.CVC4Interface
import LIVS.Sygus.SMTLexer
import LIVS.Sygus.ToSygus

import LIVS.Target.General.LanguageEnv
import LIVS.Target.JavaScript.Interface
import LIVS.Target.JavaScript.Extract
import LIVS.Target.JavaScript.JSIdentifier
import LIVS.Target.OCaml.Interface

import Control.Monad.IO.Class
import Control.Monad.Trans
import System.Console.CmdArgs

main :: IO ()
main = do
    config <- cmdArgs livsConfig

    jsEnv <- jsLanguageEnv

    synth config jsEnv

synth :: LIVSConfigCL -> LanguageEnv IO -> IO ()
synth config@(LIVSConfig { code_file = fp }) lenv = do
    putStrLn $ "fp = " ++ fp
    -- print =<< getFileSystemEncoding
    -- setFileSystemEncoding char8
    -- print =<< getFileSystemEncoding
    -- load lenv fp
    -- r <- call lenv testFxn
    
    -- print r

    -- return ()

    ids <- extract lenv fp

    whenLoud (putStrLn "Verbose")

    let cg = createCallGraph ids
        heap = H.fromList [ (Name "=" Nothing, H.Primitive $ TyFun jsIdentType (TyFun jsIdentType boolType))
                          , (Name "+" Nothing, H.Primitive $ TyFun intType (TyFun intType intType))
                          , (Name "*" Nothing, H.Primitive $ TyFun intType (TyFun intType intType))
                          , (Name "ite" Nothing, H.Primitive $ TyFun boolType (TyFun jsIdentType (TyFun jsIdentType jsIdentType)))
                          , (Name "str.++" Nothing, H.Primitive $ TyFun stringType (TyFun stringType stringType))
                          , (Name "int.to.str" Nothing, H.Primitive $ TyFun intType stringType)
                          , (Name "\"true\"" Nothing, H.Primitive $ stringType)
                          , (Name "\"false\"" Nothing, H.Primitive $ stringType)
                          , (Name "\"NaN\"" Nothing, H.Primitive $ stringType) ]

    let config' = toLIVSConfigNames heap config

    print $ core_funcs config'

    -- let tenv = T.fromList
    --                 [ ( Name "IntList" Nothing
    --                   , T.ADTSpec [ T.SelectorDC (Name "Nil" Nothing) []
    --                               , T.SelectorDC (Name "Cons" Nothing)
    --                                 [ T.NamedType (Name "val" Nothing) (TyCon (Name "Int" Nothing) TYPE)
    --                                 , T.NamedType (Name "xs" Nothing) (TyCon (Name "IntList" Nothing) TYPE)]
    --                               ]
    --                   )
    --                 ]
    let tenv = jsTypeEnv

    -- We want type constructors, selectors and testers to be available in the
    -- SyGuS grammar, so we add them to the heap and the list of grammatical
    -- elements to always be included
    let config'' = addCoreFuncs config'
                    (T.constructorNames tenv ++ T.selectorNames tenv ++ T.testerNames tenv)

    let heap' = T.mergeConstructors tenv heap
        heap'' = T.mergeSelectorsAndTesters tenv heap'

    lr <- livsCVC4 config'' lenv fp cg heap'' tenv

    print lr

-- testFxn :: Expr
-- testFxn = 
--   App 
--     (App
--         (Var (Id (Name "add" Nothing) TYPE))
--         (Lit $ LInt 4)
--     )
--     (Lit $ LInt 1)

testFxn :: Expr
testFxn = 
  App (
    Lam 
      (Id (Name "x" Nothing) (intType))
      (Lit $ LInt 3)
    )
    (Lit $ LInt 0)

    -- jsast <- parseJS "target_files/JavaScript/math.js"
    -- case jsast of
    --     Left _ -> return ()
    --     Right jsast' -> do
    --         print $ extractFunctions jsast'

    -- let h = H.fromList [ (Name "add" Nothing, H.Def $ Lam 
    --                             (Id (Name "x" Nothing) intType) 
    --                             (Lam 
    --                                 (Id (Name "y" Nothing) intType) 
    --                                 (App 
    --                                     (App 
    --                                         (Var (Id (Name "+" Nothing) (TyFun intType (TyFun intType intType))))
    --                                         (Var (Id (Name "y" Nothing) intType))
    --                                     )
    --                                     (Var (Id (Name "x" Nothing) intType))
    --                                 )
    --                             ))
    --                     , (Name "+" Nothing, H.Primitive $ TyFun intType (TyFun intType intType))]
    --     cg = createCallGraph
    --         [ (Id (Name "add" Nothing) (TyFun intType (TyFun intType intType)), [Id (Name "+" Nothing) (TyFun intType (TyFun intType intType))])
    --         , (Id (Name "+" Nothing) (TyFun intType (TyFun intType intType)), []) ]

    -- let form = toSygus cg h examples

    -- putStrLn form

    -- putStrLn ""

    -- -- cvc4 <- getCVC4
    -- -- putStrLn "Right before"
    -- -- r <- runAndReadCVC4 cvc4 form
    -- -- putStrLn "Right after"

    -- r <- runCVC4WithFile form

    -- putStrLn r

    -- let l = lexSMT r
    -- putStrLn $ show l

    -- -- closeCVC4 cvc4

    -- -- mapM_ (putStrLn . uncurry toPythonExpr) . H.toList $ H.filter H.isDef h
    -- -- mapM_ (putStrLn . toPythonExpr "f") p

    -- ocaml <- getOCaml
    -- putStrLn "Got ocaml"

    -- mapM_ (\(n, hObj) -> case hObj of
    --                     H.Def e -> runOCaml ocaml $ toOCamlDef n e
    --                     _ -> return ()) . H.toList $ H.filter H.isDefObj h
    -- putStrLn "Ran ocaml"

    -- -- print (OCaml.parse . OCaml.lexer $ r1)
    -- -- putStrLn "Ran ocaml 2"
    -- -- r2 <- runAndReadOCaml ocaml ("add 2 3;;\n")
    -- -- print (OCaml.parse . OCaml.lexer $ r2)

    -- let livsH = H.fromList [ (Name "+" Nothing, H.Primitive $ TyFun intType (TyFun intType intType))
    --                        , (Name "-" Nothing, H.Primitive $ TyFun intType (TyFun intType intType))
    --                        , (Name "=" Nothing, H.Primitive $ TyFun intType (TyFun intType boolType))
    --                        , (Name ">=" Nothing, H.Primitive $ TyFun intType (TyFun intType boolType))
    --                        , (Name "ite" Nothing, H.Primitive $ TyFun boolType (TyFun intType (TyFun intType intType)))]

    -- putStrLn "HERE"
    -- ocamlEnv <- ocamlLanguageEnv
    -- lr <- liftIO $ livsCVC4 ocamlEnv "target_files/OCaml/ints.ml" graph livsH
    -- print lr

    -- res <- runCollectingExamples ocamlEnv 100 lr (mkNameGen []) (App (Var (Id (Name "abs4" Nothing) (TyFun intType intType))) (Lit (LInt (-4))))
    -- print res

    -- python <- getPython
    -- putStrLn "Got python"
    -- mapM_ (runPython python . uncurry toPythonExpr) $ H.toList h
    -- putStrLn "Ran python"
    -- print =<< runAndReadPython python ("add(1, 2)\n")

graph :: CallGraph
graph = createCallGraph
    [ (Id (Name "double" Nothing) (TyFun intType intType), [Id (Name "add" Nothing) (TyFun intType (TyFun intType intType))])
    , (Id (Name "quadruple" Nothing) (TyFun intType intType), [Id (Name "double" Nothing) (TyFun intType intType)])
    , (Id (Name "add" Nothing) (TyFun intType (TyFun intType intType)), [Id (Name "+" Nothing) (TyFun intType (TyFun intType intType))])
    , (Id (Name "abs2" Nothing ) (TyFun intType intType), [ Id (Name "-" Nothing) (TyFun intType (TyFun intType intType))
                                                          , Id (Name ">=" Nothing) (TyFun intType (TyFun intType boolType))
                                                          , Id (Name "ite" Nothing) (TyFun boolType (TyFun intType (TyFun intType intType)))])
    , (Id (Name "abs3" Nothing) (TyFun intType intType), [ Id (Name "abs2" Nothing) (TyFun intType intType) ])
    , (Id (Name "abs4" Nothing) (TyFun intType intType), [ Id (Name "abs3" Nothing) (TyFun intType intType) ]) ]


examples :: [Example]
examples = [ Example { func = Id (Name "double" Nothing) (TyFun intType intType)
                     , input = [LitVal $ LInt 1]
                     , output = LitVal $ LInt 2 }
           , Example { func = Id (Name "double" Nothing) (TyFun intType intType)
                     , input = [LitVal $ LInt 2]
                     , output = LitVal $ LInt 4 }
           -- , Example { func_name = "doubleAndAdd"
           --           , input = [LInt 2, LInt 3]
           --           , output = LInt 10 }
           -- , Example { func_name = "doubleAndAdd"
           --           , input = [LInt 3, LInt 4]
           --           , output = LInt 14 }
           ]
