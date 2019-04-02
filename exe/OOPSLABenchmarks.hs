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
import LIVS.Language.Monad.Naming

import LIVS.Target.General.LanguageEnv
import LIVS.Target.JavaScript.Interface
import LIVS.Target.JavaScript.JSIdentifier

import LIVS.UI.Parse

import Control.Monad.IO.Class
import Control.Monad.Random.Class

import qualified Data.HashMap.Lazy as HM

import System.Console.CmdArgs
import System.Random
import System.Directory

main :: IO ()
main = do

    setStdGen $ mkStdGen 1

    jsEnv <- jsLanguageEnv

    let benchmarkDir = "benchmarks/synthesis/"
    benchmarksFilepaths <- listDirectory benchmarkDir

    mapM_
       (\fp -> synth (livsConfig {code_file = fp}) jsEnv)
       (map (\b -> benchmarkDir++b++"/fullGrammar.js") benchmarksFilepaths) --TODO fix naming convention for benchmarks

synth :: (MonadRandom m, MonadIO m) => LIVSConfigCL -> LanguageEnv m b -> m ()
synth config@(LIVSConfig { code_file = fp }) lenv = do
    liftIO $ putStrLn $ "fp = " ++ fp

    synth_ex <- examplesFromFile jsJSONToVal fp

    liftIO $ putStrLn "Extracted Examples:"
    liftIO $ print synth_ex

    (ids, b) <- extract lenv fp

    liftIO $ whenLoud (putStrLn "Verbose")

    let cg = createCallGraph (idsAndCalls ids)
        heap = H.fromList [ (Name SMT "=" Nothing, H.Primitive $ TyFun jsIdentType (TyFun jsIdentType boolType))
                          , (Name SMT "+" Nothing, H.Primitive $ TyFun intType (TyFun intType intType))
                          , (Name SMT "-" Nothing, H.Primitive $ TyFun intType (TyFun intType intType))
                          , (Name SMT "*" Nothing, H.Primitive $ TyFun intType (TyFun intType intType))
                          , (Name SMT "ite" Nothing, H.Primitive $ TyFun boolType (TyFun jsIdentType (TyFun jsIdentType jsIdentType)))
                          , (Name SMT "str.substr" Nothing, H.Primitive $ TyFun stringType (TyFun intType (TyFun intType stringType)))
                          , (Name SMT "str.indexof" Nothing, H.Primitive $ TyFun stringType (TyFun stringType (TyFun intType intType)))
                          , (Name SMT "str.++" Nothing, H.Primitive $ TyFun stringType (TyFun stringType stringType))
                          , (Name SMT "int.to.str" Nothing, H.Primitive $ TyFun intType stringType)
                          , (Name SMT "\"true\"" Nothing, H.Primitive $ stringType)
                          , (Name SMT "\"false\"" Nothing, H.Primitive $ stringType)
                          , (Name SMT "\"NaN\"" Nothing, H.Primitive $ stringType) ]

    let config' = toLIVSConfigNames heap config

    liftIO $ putStrLn "running synthesis with the following core_funcs:"
    liftIO $ print $ core_funcs config'

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

    liftIO $ putStrLn $ "cs' = " ++ show cs'

    liftIO $ putStrLn $ "fuzz_with' = " ++ show (fuzz_with')

    let ng = mkNameGen []

    let lenv' = liftLanguageEnv nameGenT lenv
        fuzz = liftFuzz nameGenT lenv (fuzzFromValsAndOutputsM w fuzz_with')
    lr <- evalNameGenT (livsSynthCVC4 config'' lenv' b fuzz fp cg cs' heap'' tenv synth_ex) ng

    liftIO $ print lr
