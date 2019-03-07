module Interpreter.Interpreter (interpreterTests) where

import LIVS.Interpreter.Interpreter
import qualified LIVS.Language.Heap as H
import LIVS.Language.Naming
import LIVS.Language.Syntax
import LIVS.Language.Typing
import LIVS.Language.Monad.Heap
import LIVS.Target.General.LanguageEnv

import Helpers.Language

import Data.Functor.Identity
import Data.HashSet as HS

import Test.Tasty
import Test.Tasty.HUnit

interpreterTests :: TestTree
interpreterTests = testGroup "Interpreter" [ run1
                                           , runCollectingExamples1
                                           , runCollectingExamples2 ]

run1 :: TestTree
run1 = testCase "Run Test 1"
    $ assertBool "Correct run1" 
            (runWithIdentity (langEnv heapAbs2) 100 heapAbs2 (mkNameGen []) e == Lit (LInt 4))
    where
        abs2 = Var (Id (Name "abs2" Nothing) (TyFun intType intType))
        e = App abs2 (Lit (LInt 4))

runCollectingExamples1 :: TestTree
runCollectingExamples1 = testCase "runCollectingExamples Test 1"
    $ assertBool "Correct examples in runCollectingExamples1" 
            (let
                exs = HS.fromList (snd $ runCollectingExamplesWithIdentity (langEnv heapAbs2) 100 heapAbs2 (mkNameGen []) e)
            in
            (Suspect abs2Ex) `HS.member` exs && (Suspect iteEx) `HS.member` exs
            )
    where
        abs3 = Var (Id (Name "abs3" Nothing) (TyFun intType intType))
        e = App abs3 (Lit (LInt (-4)))

        abs2Ex = Example { func = Id (Name "abs2" Nothing) (TyFun intType intType)
                        , input = [ LitVal (LInt (-4)) ]
                        , output = LitVal (LInt 4) }

        iteEx = Example { func = iteId
                        , input = [ DataVal (DC (Name "true" Nothing) (TyCon (Name "Bool" Nothing) TYPE))
                                  , LitVal (LInt 4), LitVal (LInt (-4)) ]
                        , output = LitVal (LInt 4) }

runCollectingExamples2 :: TestTree
runCollectingExamples2 = testCase "runCollectingExamples Test 2"
    $ assertBool "Correct number of examples in runCollectingExamples2" 
            (let
                exs = snd $ runCollectingExamplesWithIdentity (langEnv heapAbs2) 100 heapAbs2 (mkNameGen []) e
            in
            length exs == 5
            )
    where
        abs3 = Var (Id (Name "abs3" Nothing) (TyFun intType intType))
        e = App abs3 (Lit (LInt (-4)))

runWithIdentity :: LanguageEnv Identity -> Int -> H.Heap -> NameGen -> Expr -> Expr
runWithIdentity le n h ng e = runIdentity (run le n h ng e)

runCollectingExamplesWithIdentity :: LanguageEnv Identity -> Int -> H.Heap -> NameGen -> Expr ->  (Expr, [SuspectExample])
runCollectingExamplesWithIdentity le n h ng e = runIdentity (runCollectingExamples le n h ng e)

langEnv :: Monad m => H.Heap -> LanguageEnv m
langEnv h = LanguageEnv { load = const $ return ()
                        , def = const . const $ return ()
                        , call = \e -> return . fst $ runHeapM (callPrim e) h
                        }

callPrim :: HeapMonad m => Expr -> m Val
callPrim (App (App (App (Var (Id (Name "ite" _) _)) b) e) e') =
    case b of
        Data (DC (Name "true" _) _) ->
            reduceToVal e
        Data (DC (Name "false" _) _) ->
            reduceToVal e'
        _ -> error $ "callPrim: Unhandled expression from ite" ++ show b ++ "\n" ++ show e ++ "\n" ++ show e'
callPrim (App (App (Var (Id (Name ">=" _) _)) (Lit (LInt l))) (Lit (LInt l')))
    | l >= l' =
        return . DataVal $ DC (Name "true" Nothing) (TyCon (Name "Bool" Nothing) TYPE)
    | otherwise =
        return . DataVal $ DC (Name "false" Nothing) (TyCon (Name "Bool" Nothing) TYPE)
callPrim (App (App (Var (Id (Name "-" _) _)) (Lit (LInt l))) (Lit (LInt l'))) =
    return . LitVal $ LInt (l - l')
callPrim _ = error "callPrim: Unhandled expression"

reduceToVal :: HeapMonad m => Expr -> m Val
reduceToVal (Var (Id n _)) = do
    e <- lookupH n
    case e of
        Just (H.Def e') -> reduceToVal e'
        _ -> error "reduceToVal: bad expr"
reduceToVal (Lit l) = return $ LitVal l
reduceToVal (Data dc) = return $ DataVal dc
reduceToVal _ = error "reduceToVal: bad expr"