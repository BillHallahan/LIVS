module Interpreter.Interpreter (interpreterTests) where

import LIVS.Interpreter.Interpreter
import qualified LIVS.Language.Heap as H
import LIVS.Language.Naming
import LIVS.Language.Syntax
import LIVS.Language.Typing
import LIVS.Language.Monad.Heap
import LIVS.Target.General.LanguageEnv

import Data.Functor.Identity

import Test.Tasty
import Test.Tasty.HUnit

interpreterTests :: TestTree
interpreterTests = testGroup "Interpreter" [ run1 ]

run1 :: TestTree
run1 = testCase "Run Test 1"
    $ assertBool "Correct run1" 
            (runWithIdentity (langEnv heap) 100 e heap (mkNameGen []) == Lit (LInt 4))
    where
        abs2 = Var (Id (Name "abs2" Nothing) (TyFun intType intType))
        e = App abs2 (Lit (LInt 4))

runWithIdentity :: LanguageEnv Identity -> Int -> Expr ->  H.Heap -> NameGen -> Expr
runWithIdentity le n e h ng = runIdentity (run le n e h ng)

heap :: H.Heap
heap = H.fromList
    [ ( Name "abs2" Nothing
      , H.Def 
            (Lam 
                (Id (Name "x1" Nothing) intType) 
                (App 
                    (App 
                        (App 
                            (Var (Id (Name "ite" Nothing) (TyFun (TyCon (Name "Bool" Nothing) TYPE) (TyFun intType (TyFun intType intType))))) 
                            (App 
                                (App 
                                    (Var (Id (Name ">=" Nothing) (TyFun intType (TyFun intType (TyCon (Name "Bool" Nothing) TYPE))))) 
                                    (Lit (LInt 0))
                                ) 
                                (Var (Id (Name "x1" Nothing) intType))
                            )
                        ) 
                        (App 
                            (App 
                                (Var (Id (Name "-" Nothing) (TyFun intType (TyFun intType intType)))) 
                                (Lit (LInt 0))
                            ) 
                            (Var (Id (Name "x1" Nothing) intType))
                        )
                    ) 
                    (Var (Id (Name "x1" Nothing) intType))
                )
            )
        )
    , ( Name "ite" Nothing
      , H.Primitive (TyFun (TyCon (Name "Bool" Nothing) TYPE) (TyFun intType (TyFun intType intType)))
      )
    , ( Name ">=" Nothing 
      , H.Primitive (TyFun intType (TyFun intType (TyCon (Name "Bool" Nothing) TYPE)))
      )
    , ( Name "-" Nothing 
      , H.Primitive (TyFun intType (TyFun intType intType))
      )
    ]

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