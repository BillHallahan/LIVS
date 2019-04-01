module Main where

import LIVS.Core.Fuzz
import LIVS.Core.GenConsts
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

import qualified Data.HashMap.Lazy as HM

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
    -- (_, b) <- extract jsEnv (code_file config)
    -- es <- fuzzExamplesM jsEnv b [] jsTypeEnv (fuzz_num config) (Id (Name "substring" Nothing) (TyFun jsIdentType (TyFun jsIdentType (TyFun jsIdentType jsIdentType))))
    -- print es
    -- return ()

synth :: LIVSConfigCL -> LanguageEnv IO b -> IO ()
synth config@(LIVSConfig { code_file = fp }) lenv = do
    putStrLn $ "fp = " ++ fp

    synth_ex <- examplesFromFile jsJSONToVal fp

    print synth_ex

    (ids, b) <- extract lenv fp

    whenLoud (putStrLn "Verbose")

    let cg = createCallGraph (idsAndCalls ids)
        heap = H.fromList [ (SMTName "=", H.Primitive $ TyFun jsIdentType (TyFun jsIdentType boolType))
                          , (SMTName "+", H.Primitive $ TyFun intType (TyFun intType intType))
                          , (SMTName "-", H.Primitive $ TyFun intType (TyFun intType intType))
                          , (SMTName "*", H.Primitive $ TyFun intType (TyFun intType intType))
                          , (SMTName "ite", H.Primitive $ TyFun boolType (TyFun jsIdentType (TyFun jsIdentType jsIdentType)))
                          , (SMTName "str.substr", H.Primitive $ TyFun stringType (TyFun intType (TyFun intType stringType)))
                          , (SMTName "str.indexof", H.Primitive $ TyFun stringType (TyFun stringType (TyFun intType intType)))
                          , (SMTName "str.++", H.Primitive $ TyFun stringType (TyFun stringType stringType))
                          , (SMTName "int.to.str", H.Primitive $ TyFun intType stringType)
                          , (SMTName "\"true\"", H.Primitive $ stringType)
                          , (SMTName "\"false\"", H.Primitive $ stringType)
                          , (SMTName "\"NaN\"", H.Primitive $ stringType) ]

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

    let cs = concatMap (consts . snd) ids
        cs' = genConsts $ cs ++ concatMap exampleVals synth_ex
        fuzz_with = genFuzzConsts $ cs ++ concatMap exampleVals synth_ex
        fuzz_with' = expandVals fuzz_with tenv
        ics = genIntsConsts cs

    let r = toRational (1 :: Double) 
        w = HM.fromList [(jsIntDC, r), (jsStringDC, r), (jsBoolDC, r)]

    putStrLn $ "cs' = " ++ show cs'

    putStrLn $ "fuzz_with' = " ++ show (fuzz_with')

    lr <- livsSynthCVC4 config'' lenv b (fuzzFromValsAndOutputsM w fuzz_with') fp cg cs' heap'' tenv synth_ex

    print lr