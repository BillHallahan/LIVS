module Sygus.SMTLexer where

import LIVS.Sygus.SMTLexer

import Test.Tasty
import Test.Tasty.HUnit

smtLexerTests :: TestTree
smtLexerTests = testGroup "SMT Lexer" [ smtLexerTest1
                                      , smtLexerTest2 ]

smtLexerTest1 :: TestTree
smtLexerTest1 = testCase "smtLexer Test 1"
    $ assertBool "Can't read whitespace in string res"
        (lexSMT "\" \"" == [TokenString " "])

smtLexerTest2 :: TestTree
smtLexerTest2 = testCase "smtLexer Test 2"
    $ assertBool "Can't read any string res ="
        (lexSMT "\"TEST\"" == [TokenString "TEST"])
