module Interpreter.Interpreter (interpreterTests) where

import LIVS.Interpreter.Interpreter
import LIVS.Language.Expr
import qualified LIVS.Language.Heap as H
import LIVS.Language.Naming
import LIVS.Language.Syntax
import LIVS.Language.Typing
import LIVS.Language.Monad.Heap
import LIVS.Target.General.LanguageEnv

import Helpers.Interpreter
import Helpers.Language

import Data.Functor.Identity
import Data.HashSet as HS

import Test.Tasty
import Test.Tasty.HUnit

interpreterTests :: TestTree
interpreterTests = testGroup "Interpreter" [ run1
                                           , run2
                                           , runCollectingExamples1
                                           , runCollectingExamples2
                                           , runCollectingExamples3 ]

run1 :: TestTree
run1 = testCase "Run Test 1"
    $ assertBool "Correct run1" 
            (runWithIdentity (callPrimExprM heapAbs) 100 heapAbs (mkNameGen []) e == Lit (LInt 4))
    where
        abs2 = Var (Id (Name Ident "abs2" Nothing) (TyFun intType intType))
        e = App abs2 (Lit (LInt 4))

run2 :: TestTree
run2 = testCase "Run Test 2"
    $ assertBool "Correct run2" 
            (runWithIdentity (callPrimExprM heapAbs) 100 heapAbs (mkNameGen []) callE == Lit (LInt 1))
    where
        e = Lam 
              (Id (Name Ident "x1" Nothing) intType) 
              (Lam 
                  (Id (Name Ident "x2" Nothing) intType) 
                  (Var (Id (Name Ident "x1" Nothing) intType))
              )
        callE = App (App e (Lit (LInt 1))) (Lit (LInt 2))

runCollectingExamples1 :: TestTree
runCollectingExamples1 = testCase "runCollectingExamples Test 1"
    $ assertBool "Correct examples in runCollectingExamples1" 
            (let
                exs = HS.fromList (snd $ runCollectingExamplesWithIdentity (callPrimExprM heapAbs) 100 heapAbs (mkNameGen []) e)
            in
            (Suspect abs2Ex) `HS.member` exs && (Suspect iteEx) `HS.member` exs
            )
    where
        abs3 = Var (Id (Name Ident "abs3" Nothing) (TyFun intType intType))
        e = App abs3 (Lit (LInt (-4)))

        abs2Ex = Example { func = Id (Name Ident "abs2" Nothing) (TyFun intType intType)
                        , input = [ LitVal (LInt (-4)) ]
                        , output = LitVal (LInt 4) }

        iteEx = Example { func = iteId
                        , input = [ DataVal trueDC
                                  , LitVal (LInt 4), LitVal (LInt (-4)) ]
                        , output = LitVal (LInt 4) }

runCollectingExamples2 :: TestTree
runCollectingExamples2 = testCase "runCollectingExamples Test 2"
    $ assertBool "Correct number of examples in runCollectingExamples2" 
            (let
                exs = snd $ runCollectingExamplesWithIdentity (callPrimExprM heapAbs) 100 heapAbs (mkNameGen []) e
            in
            length exs == 5
            )
    where
        abs3 = Var (Id (Name Ident "abs3" Nothing) (TyFun intType intType))
        e = App abs3 (Lit (LInt (-4)))

runCollectingExamples3 :: TestTree
runCollectingExamples3 = testCase "runCollectingExamples Test 3"
    $ assertBool "Correct examples in runCollectingExamples3"
            (let
                exs = HS.fromList (snd $ runCollectingExamplesWithIdentity (callPrimExprM h) 100 h (mkNameGen []) e)
            in
            (Suspect idEx) `HS.member` exs
            )
    where
        h = H.fromList 
            [ ( Name Ident "id" Nothing
              , H.Def
                    (Lam
                        (Id (Name Ident "x1" Nothing) intType)
                        (Var (Id (Name Ident "x1" Nothing) intType))
                    )
              )
            , ( Name Ident "f" Nothing
              , H.Def
                    (Lam
                        (Id (Name Ident "x1" Nothing) intType)
                        (App
                            (Var idF)
                            (Var (Id (Name Ident "x1" Nothing) intType))
                        )
                    )
              )
            , ( Name SMT "ite" Nothing
              , H.Primitive (TyFun boolType (TyFun intType (TyFun intType intType)))
              )
            , ( Name SMT ">=" Nothing 
              , H.Primitive (TyFun intType (TyFun intType boolType))
              )
            , ( Name SMT "-" Nothing 
              , H.Primitive (TyFun intType (TyFun intType intType))
              )
            ]

        f = Id (Name Ident "f" Nothing) (TyFun intType intType)
        idF = Id (Name Ident "id" Nothing) (TyFun intType intType)

        e = App (Var f) (Lit (LInt (-3)))

        idEx = Example { func = Id (Name Ident "id" Nothing) (TyFun intType intType)
                       , input = [ LitVal (LInt (-3)) ]
                       , output = LitVal (LInt (-3)) }

runWithIdentity :: EvalPrimitive Identity -> Int -> H.Heap -> NameGen -> Expr -> Expr
runWithIdentity ep n h ng e = runIdentity (run ep n h ng e)

runCollectingExamplesWithIdentity :: EvalPrimitive Identity -> Int -> H.Heap -> NameGen -> Expr ->  (Expr, [SuspectExample])
runCollectingExamplesWithIdentity ep n h ng e = runIdentity (runCollectingExamples ep n h ng e)