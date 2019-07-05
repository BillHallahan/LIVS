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
    -- FULL TEST SET : 30 tests
    -- let all_tests = [ testSingleEx, testSingleArg, testMultiArg, testMultiFxn, testConstCollection, testIntLiteral
    --                 , testBoolLiteral, testFloatLiteral, testStringLiteral, testBoolType, testFloatType, testStringType
    --                 , testMultiTypeInpt, testMultiTypeOtpt, testExternDirectCall, testExternIndirectCall
    --                 , testMultiExternFxns, testMultiPathToTarget, testNoExsForTarget, testJSAssignment, testJSBinOps
    --                 , testJSConditions, testJSLoops, testJSIf, testJSTernary, testComplexGlobals, testComplexScoring
    --                 , testComplexRecursion, testComplexExtern, testComplexReal ]

    -- SUBSET OF TESTS THAT DON'T THROW ERRORS : 9 tests
    let all_tests = [ testSingleEx, testSingleArg, testMultiArg, testMultiFxn, testConstCollection, testIntLiteral
                    , testExternDirectCall, testExternIndirectCall, testMultiPathToTarget ]
    let eval_tests = sequence all_tests
    all_tests' <- eval_tests
    return $ testGroup "js Repair" all_tests'

-- TEST HARNESS

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

defaultTest :: String -> String -> String -> IO TestTree
defaultTest expected_output name file = do
    actual_output <- defaultSynth file
    return $ testCase name $ assertBool (failPrefix ++ file) (actual_output == expected_output)

-- TESTS

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

testSingleArg :: IO TestTree
testSingleArg = defaultTest expected "Simple - Single-Arg Fxns" "simple/single_arg.js"
    where expected = "f = function (n) { return (add((add(n, n)), (n + n) ))}\n"

testMultiArg :: IO TestTree
testMultiArg = defaultTest expected "Simple - Multi-Arg Fxns" "simple/multi_arg.js"
    where expected = "f = function (n, m) { return (add((add(n, m)), (add(n, m))))}\n"

testMultiFxn :: IO TestTree
testMultiFxn = defaultTest expected "Simple - Many Fxns With Examples" "simple/multi_fxn.js"
    where expected = "f = function (n, m) { return (add((add(n, m)), (add(n, m))))}\n"

testConstCollection :: IO TestTree
testConstCollection = defaultTest expected "Literals - Use Consts In File" "literals/collect_consts.js"
    where expected = "f = function (n) { return (add(n, (add((2), n))))}\n"

testIntLiteral :: IO TestTree
testIntLiteral = defaultTest expected "Literals - Int" "literals/int.js"
    where expected = "f = function (n) { return (add((2), (add(n, n))))}\n"

testBoolLiteral :: IO TestTree
testBoolLiteral = defaultTest expected "Literals - Bool" "literals/bool.js"
    where expected = "" -- TODO

testFloatLiteral :: IO TestTree
testFloatLiteral = defaultTest expected "Literals - Float" "literals/float.js"
    where expected = "" -- TODO

testStringLiteral :: IO TestTree
testStringLiteral = defaultTest expected "Literals - String" "literals/string.js"
    where expected = "" -- TODO

testBoolType :: IO TestTree
testBoolType = defaultTest expected "Types - Bool" "types/bool.js"
    where expected = "" -- TODO

testFloatType :: IO TestTree
testFloatType = defaultTest expected "Types - Float" "types/float.js"
    where expected = "" -- TODO

testStringType :: IO TestTree
testStringType = defaultTest expected "Types - String" "types/string.js"
    where expected = "" -- TODO

testMultiTypeInpt :: IO TestTree
testMultiTypeInpt = defaultTest expected "Types - Multiple Input Types" "types/multi_inpt.js"
    where expected = "" -- TODO

testMultiTypeOtpt :: IO TestTree
testMultiTypeOtpt = defaultTest expected "Types - Multiple Output Types" "types/multi_otpt.js"
    where expected = "" -- TODO

testExternDirectCall :: IO TestTree
testExternDirectCall = defaultTest expected "Extern - Directly Calls Target" "extern_exs/direct_call.js"
    where expected = "f = function (n) { return (add((add(n, n)), (n + n) ))}\n"

testExternIndirectCall :: IO TestTree
testExternIndirectCall = defaultTest expected "Extern - Indirectly Calls Target" "extern_exs/indirect_call.js"
    where expected = "f = function (n) { return (add(n, (n + n) ))}\n"

testMultiExternFxns :: IO TestTree
testMultiExternFxns = defaultTest expected "Extern - Multiple Constraining Fxns" "extern_exs/multi_extern_fxns.js"
    where expected = "" -- TODO

testMultiPathToTarget :: IO TestTree
testMultiPathToTarget = defaultTest expected "Extern - Many Paths To Target" "extern_exs/multi_path_to_target.js"
    where expected = "f = function (n) { return (mult(n, (mult(n, n))))}\n"

testNoExsForTarget :: IO TestTree
testNoExsForTarget = defaultTest expected "Extern - No Examples For Target" "extern_exs/no_exs_for_target.js"
    where expected = "" -- TODO

testJSAssignment :: IO TestTree
testJSAssignment = defaultTest expected "JS Syntax - Assignment" "js_syntax/assignment.js"
    where expected = "" -- TODO

testJSBinOps :: IO TestTree
testJSBinOps = defaultTest expected "JS Syntax - Binary Ops" "js_syntax/binary_op.js"
    where expected = "" -- TODO

testJSConditions :: IO TestTree
testJSConditions = defaultTest expected "JS Syntax - Conditionals" "js_syntax/condition.js"
    where expected = "" -- TODO

testJSLoops :: IO TestTree
testJSLoops = defaultTest expected "JS Syntax - For Loops" "js_syntax/for_loop.js"
    where expected = "" -- TODO

testJSIf :: IO TestTree
testJSIf = defaultTest expected "JS Syntax - If Statements" "js_syntax/if_statement.js"
    where expected = "" -- TODO

testJSTernary :: IO TestTree
testJSTernary = defaultTest expected "JS Syntax - Ternary Op" "js_syntax/ternary_op.js"
    where expected = "" -- TODO

testComplexGlobals :: IO TestTree
testComplexGlobals = defaultTest expected "Complex - Global Vars" "js_syntax/global_var.js"
    where expected = "" -- TODO

testComplexScoring :: IO TestTree
testComplexScoring = defaultTest expected "Complex - Narrow Scoring" "js_syntax/scoring.js"
    where expected = "" -- TODO

testComplexRecursion :: IO TestTree
testComplexRecursion = defaultTest expected "Complex - Recursion" "js_syntax/recursion.js"
    where expected = "" -- TODO

testComplexExtern :: IO TestTree
testComplexExtern = defaultTest expected "Complex - External Constraints" "js_syntax/typed_extern.js"
    where expected = "" -- TODO

testComplexReal :: IO TestTree
testComplexReal = defaultTest expected "Complex - Real-World JS" "js_syntax/real_js.js"
    where expected = "" -- TODO
