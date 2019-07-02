module LIVS.Repair where

import Helpers.Interpreter
import Helpers.Language

import LIVS.Config.Config
import LIVS.Core.Init
import LIVS.Language.Syntax
import LIVS.Target.JavaScript.Interface
import LIVS.Target.General.LanguageEnv

import Control.Monad.IO.Class
import Control.Monad.Random.Class
import qualified Data.HashSet as S

import Test.Tasty
import Test.Tasty.HUnit

repairTests :: IO TestTree
repairTests = do
    ts <- testSimple
    return $ testGroup "Repair" [ ts ]

defaultConfig :: FilePath -> String -> IO (LIVSConfigCL, (LanguageEnv IO (S.HashSet Name)))
defaultConfig fp fname = do
    jsEnv <- jsLanguageEnv
    let con = LIVSConfig {
        code_file = fp,
        program_mode = fname,
        seed = Nothing,
        fuzz_num = 20,
        core_funcs = coreFuncs,
        smt_timeout = 20 }
    return (con, jsEnv)

defaultSynth :: FilePath -> String -> IO String
defaultSynth fp fname = do
    con <- defaultConfig ("tests/test_files/" ++ fp) fname
    (uncurry synth) con

testSimple :: IO TestTree
testSimple = do
    res <- defaultSynth "simple.js" "f"
    return $ testCase "Simple Functions" $ assertBool "Correct simple.js" (res == expected_res)
        where
            expected_res = "f = function (n) { return (add(add(n, n), add(n, n))}"
