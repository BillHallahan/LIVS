module LIVS.LIVS where

import LIVS.Language.CallGraph
import LIVS.Language.Syntax
import LIVS.Language.Typing
import LIVS.Core.LIVS

import Test.Tasty
import Test.Tasty.HUnit

livsTests :: TestTree
livsTests = testGroup "LIVS" [ ]