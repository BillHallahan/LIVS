module LIVS.LIVS where

import LIVS.Core.LIVS
import LIVS.Language.CallGraph
import qualified LIVS.Language.Heap as H
import LIVS.Language.Syntax
import LIVS.Language.Typing
import LIVS.Target.General.LanguageEnv

import Helpers.Language

import Control.Monad.Random.Lazy
import Data.Functor.Identity

import Test.Tasty
import Test.Tasty.HUnit

livsTests :: TestTree
livsTests = testGroup "LIVS" [ ]

f :: H.Heap
f = evalRand (livs undefined undefined undefined undefined undefined) (mkStdGen 0)

callGraph1 :: CallGraph
callGraph1 = createCallGraph
    [ ( Id (Name "double" Nothing) (TyFun intType intType)
      , [Id (Name "add" Nothing) (TyFun intType (TyFun intType intType))])
    , ( Id (Name "quadruple" Nothing) (TyFun intType intType)
      , [Id (Name "double" Nothing) (TyFun intType intType)])
    , ( Id (Name "add" Nothing) (TyFun intType (TyFun intType intType))
      , [Id (Name "+" Nothing) (TyFun intType (TyFun intType intType))])
    ]

testEnv :: LanguageEnv Identity
testEnv = LanguageEnv { load = const $ return ()
                      , def = undefined
                      , call = undefined }