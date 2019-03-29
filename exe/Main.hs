module Main where

import LIVS.Core.Fuzz
import LIVS.Core.LIVSSynth

import LIVS.Config.Config

import LIVS.Language.CallGraph
import qualified LIVS.Language.Heap as H
import LIVS.Language.Naming
import LIVS.Language.Syntax
import qualified LIVS.Language.TypeEnv as T
import LIVS.Language.Typing

import LIVS.Target.General.LanguageEnv
import LIVS.Target.JavaScript.Interface
import LIVS.Target.JavaScript.JSIdentifier

import LIVS.UI.Parse

import System.Console.CmdArgs
import System.Random

main :: IO ()
main = do
    config <- cmdArgs livsConfig

    case seed config of
        Just s -> setStdGen $ mkStdGen s
        Nothing -> return ()

    jsEnv <- jsLanguageEnv

    synth config jsEnv

synth :: LIVSConfigCL -> LanguageEnv IO b -> IO ()
synth config@(LIVSConfig { code_file = fp }) lenv = do
    putStrLn $ "fp = " ++ fp

    synth_ex <- examplesFromFile jsJSONToVal fp

    print synth_ex

    (ids, b) <- extract lenv fp

    whenLoud (putStrLn "Verbose")

    let cg = createCallGraph ids
        heap = H.fromList [ (Name "=" Nothing, H.Primitive $ TyFun jsIdentType (TyFun jsIdentType boolType))
                          , (Name "+" Nothing, H.Primitive $ TyFun intType (TyFun intType intType))
                          , (Name "-" Nothing, H.Primitive $ TyFun intType (TyFun intType intType))
                          , (Name "*" Nothing, H.Primitive $ TyFun intType (TyFun intType intType))
                          , (Name "ite" Nothing, H.Primitive $ TyFun boolType (TyFun jsIdentType (TyFun jsIdentType jsIdentType)))
                          -- , (Name "str.substr" Nothing, H.Primitive $ TyFun stringType (TyFun intType (TyFun intType stringType)))
                          , (Name "str.++" Nothing, H.Primitive $ TyFun stringType (TyFun stringType stringType))
                          , (Name "int.to.str" Nothing, H.Primitive $ TyFun intType stringType)
                          , (Name "\"true\"" Nothing, H.Primitive $ stringType)
                          , (Name "\"false\"" Nothing, H.Primitive $ stringType)
                          , (Name "\"NaN\"" Nothing, H.Primitive $ stringType) ]

    let config' = toLIVSConfigNames heap config

    print $ core_funcs config'

    let tenv = jsTypeEnv

    -- We want type constructors, selectors and testers to be available in the
    -- SyGuS grammar, so we add them to the heap and the list of grammatical
    -- elements to always be included
    let config'' = addCoreFuncs config'
                    (T.constructorNames tenv ++ T.selectorNames tenv ++ T.testerNames tenv)

    let heap' = T.mergeConstructors tenv heap
        heap'' = T.mergeSelectorsAndTesters tenv heap'

    lr <- livsSynthCVC4 config'' lenv b (\le b' ex -> fuzzFromOutputsM le b' (synth_ex ++ ex)) fp cg heap'' tenv synth_ex

    print lr