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
    -- let alltests = [ testSingleArg, testMultiArg, testSingleEx, testMultiFxn,
    --                  testIntLiteral, testBoolLiteral, testFloatLiteral, testStringLiteral,
    --                  testIntType, testBoolType, testFloatType, testStringType,
    --                  testDataConstructor, testMultiTypeInpt, testMultiTypeOtpt ]
    s1 <- testSingleArg
    s2 <- testMultiArg
    s3 <- testSingleEx
    s4 <- testMultiFxn
    l1 <- testIntLiteral
    l2 <- testBoolLiteral
    l3 <- testFloatLiteral
    l4 <- testStringLiteral
    l5 <- testConstCollection
    t1 <- testBoolType
    t2 <- testFloatType
    t3 <- testStringType
    t4 <- testDataConstructor
    t5 <- testMultiTypeInpt
    t6 <- testMultiTypeOtpt
    return $ testGroup "js Repair" [ s1, s2, s3, s4, l1, l2, l3, l4, l5, t1, t2, t3, t4, t5, t6 ]

defaultConfig :: FilePath -> IO (LIVSConfigCL, (LanguageEnv IO (S.HashSet Name)))
defaultConfig fp = do
    jsEnv <- jsLanguageEnv
    let con = LIVSConfig {
        code_file = fp,
        program_mode = "f",
        seed = Nothing,
        fuzz_num = 20,
        core_funcs = coreFuncs,
        smt_timeout = 20 }
    return (con, jsEnv)

defaultSynth :: FilePath -> IO String
defaultSynth fp = do
    con <- defaultConfig $ "tests/test_files/" ++ fp
    uncurry synth con

failPrefix :: String
failPrefix = "Failed test_files/"

testSingleArg :: IO TestTree
testSingleArg = do
    actual_output <- defaultSynth testfile
    return $ testCase testname $ assertBool (failPrefix ++ testfile) (actual_output == expected_output)
        where
            testname = "Simple - Single-Arg Fxns"
            testfile = "simple/single_arg.js"
            expected_output = "f = function (n) { return (add((add(n, n)), (n + n) ))}\n"

testMultiArg :: IO TestTree
testMultiArg = do
    actual_output <- defaultSynth testfile
    return $ testCase testname $ assertBool (failPrefix ++ testfile) (actual_output == expected_output)
        where
            testname = "Simple - Multi-Arg Fxns"
            testfile = "simple/multi_arg.js"
            expected_output = "f = function (n, m) { return (add((add(n, m)), (add(n, m))))}\n"

testSingleEx :: IO TestTree
testSingleEx = do
    actual_output1 <- defaultSynth testfile1
    actual_output2 <- defaultSynth testfile2
    return $ testCase testname $ assertBool (failPrefix ++ testfile) (actual_output1 == expected_output1 &&
                                                                      actual_output2 == expected_output2)
        where
            testname = "Simple - One PBE Example"
            testfile = "simple/single_ex[1|2].js"
            testfile1 = "simple/single_ex1.js"
            testfile2 = "simple/single_ex2.js"
            expected_output1 = "f = function (n, m) { return (add((add(n, m)), (add(n, m))))}\n"
            expected_output2 = "f = function (n, m) { return (42)}\n"

testMultiFxn :: IO TestTree
testMultiFxn = do
    actual_output <- defaultSynth testfile
    return $ testCase testname $ assertBool (failPrefix ++ testfile) (actual_output == expected_output)
        where
            testname = "Simple - Many Fxns With Examples"
            testfile = "simple/multi_fxn.js"
            expected_output = "f = function (n, m) { return (add((add(n, m)), (add(n, m))))}\n"

testIntLiteral :: IO TestTree
testIntLiteral = do
    actual_output <- defaultSynth testfile
    return $ testCase testname $ assertBool (failPrefix ++ testfile) (actual_output == expected_output)
        where
            testname = "Literals - Int"
            testfile = "literals/int.js"
            expected_output = "f = function (n) { return (add((2), (add(n, n))))}\n"

testBoolLiteral :: IO TestTree
testBoolLiteral = do
    actual_output <- defaultSynth testfile
    return $ testCase testname $ assertBool (failPrefix ++ testfile) (actual_output == expected_output)
        where
            testname = "Literals - Bool"
            testfile = "literals/bool.js"
            expected_output = "" -- TODO

testFloatLiteral :: IO TestTree
testFloatLiteral = do
    actual_output <- defaultSynth testfile
    return $ testCase testname $ assertBool (failPrefix ++ testfile) (actual_output == expected_output)
        where
            testname = "Literals - Float"
            testfile = "literals/float.js"
            expected_output = "" -- TODO

testStringLiteral :: IO TestTree
testStringLiteral = do
    actual_output <- defaultSynth testfile
    return $ testCase testname $ assertBool (failPrefix ++ testfile) (actual_output == expected_output)
        where
            testname = "Literals - String"
            testfile = "literals/string.js"
            expected_output = "" -- TODO

testConstCollection :: IO TestTree
testConstCollection = do
    actual_output <- defaultSynth testfile
    return $ testCase testname $ assertBool (failPrefix ++ testfile) (actual_output == expected_output)
        where
            testname = "Literals - Use Consts In File"
            testfile = "literals/collect_consts.js"
            expected_output = "" -- TODO

testBoolType :: IO TestTree
testBoolType = do
    actual_output <- defaultSynth testfile
    return $ testCase testname $ assertBool (failPrefix ++ testfile) (actual_output == expected_output)
        where
            testname = "Types - Bool"
            testfile = "types/bool.js"
            expected_output = "" -- TODO

testFloatType :: IO TestTree
testFloatType = do
    actual_output <- defaultSynth testfile
    return $ testCase testname $ assertBool (failPrefix ++ testfile) (actual_output == expected_output)
        where
            testname = "Types - Float"
            testfile = "types/float.js"
            expected_output = "" -- TODO

testStringType :: IO TestTree
testStringType = do
    actual_output <- defaultSynth testfile
    return $ testCase testname $ assertBool (failPrefix ++ testfile) (actual_output == expected_output)
        where
            testname = "Types - String"
            testfile = "types/string.js"
            expected_output = "" -- TODO

testDataConstructor :: IO TestTree
testDataConstructor = do
    actual_output <- defaultSynth testfile
    return $ testCase testname $ assertBool (failPrefix ++ testfile) (actual_output == expected_output)
        where
            testname = "Types - Data Constructors"
            testfile = "types/dc.js"
            expected_output = "" -- TODO

testMultiTypeInpt :: IO TestTree
testMultiTypeInpt = do
    actual_output <- defaultSynth testfile
    return $ testCase testname $ assertBool (failPrefix ++ testfile) (actual_output == expected_output)
        where
            testname = "Types - Multiple Input Types"
            testfile = "types/multi_inpt.js"
            expected_output = "" -- TODO

testMultiTypeOtpt :: IO TestTree
testMultiTypeOtpt = do
    actual_output <- defaultSynth testfile
    return $ testCase testname $ assertBool (failPrefix ++ testfile) (actual_output == expected_output)
        where
            testname = "Types - Multiple Output Types"
            testfile = "types/multi_otpt.js"
            expected_output = "" -- TODO
