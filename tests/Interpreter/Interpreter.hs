module Interpreter.Interpreter (interpreterTests) where

import LIVS.Interpreter.Interpreter
import qualified LIVS.Language.Heap as H
import LIVS.Language.Syntax
import LIVS.Language.Monad.Heap
import LIVS.Target.General.LanguageEnv

import Test.Tasty
import Test.Tasty.HUnit

interpreterTests :: TestTree
interpreterTests = testGroup "Interpreter" [ ]

heap :: H.Heap
heap = H.fromList
    [ ( Name "abs2" Nothing
      , H.Def 
            (Lam 
                (Id (Name "x1" Nothing) (TyCon (Name "Int" Nothing) TYPE)) 
                (App 
                    (App 
                        (App 
                            (Var (Id (Name "ite" Nothing) (TyFun (TyCon (Name "Bool" Nothing) TYPE) (TyFun (TyCon (Name "Int" Nothing) TYPE) (TyFun (TyCon (Name "Int" Nothing) TYPE) (TyCon (Name "Int" Nothing) TYPE)))))) 
                            (App 
                                (App 
                                    (Var (Id (Name ">=" Nothing) (TyFun (TyCon (Name "Int" Nothing) TYPE) (TyFun (TyCon (Name "Int" Nothing) TYPE) (TyCon (Name "Bool" Nothing) TYPE))))) 
                                    (Lit (LInt 0))
                                ) 
                                (Var (Id (Name "x1" Nothing) (TyCon (Name "Int" Nothing) TYPE)))
                            )
                        ) 
                        (App 
                            (App 
                                (Var (Id (Name "-" Nothing) (TyFun (TyCon (Name "Int" Nothing) TYPE) (TyFun (TyCon (Name "Int" Nothing) TYPE) (TyCon (Name "Int" Nothing) TYPE))))) 
                                (Lit (LInt 0))
                            ) 
                            (Var (Id (Name "x1" Nothing) (TyCon (Name "Int" Nothing) TYPE)))
                        )
                    ) 
                    (Var (Id (Name "x1" Nothing) (TyCon (Name "Int" Nothing) TYPE)))
                )
            )
        )
    , ( Name "ite" Nothing
      , H.Primitive (TyFun (TyCon (Name "Bool" Nothing) TYPE) (TyFun (TyCon (Name "Int" Nothing) TYPE) (TyFun (TyCon (Name "Int" Nothing) TYPE) (TyCon (Name "Int" Nothing) TYPE))))
      )
    , ( Name ">=" Nothing 
      , H.Primitive (TyFun (TyCon (Name "Int" Nothing) TYPE) (TyFun (TyCon (Name "Int" Nothing) TYPE) (TyCon (Name "Bool" Nothing) TYPE)))
      )
    , ( Name "-" Nothing 
      , H.Primitive (TyFun (TyCon (Name "Int" Nothing) TYPE) (TyFun (TyCon (Name "Int" Nothing) TYPE) (TyCon (Name "Int" Nothing) TYPE)))
      )
    ]

langEnv :: HeapMonad m => LanguageEnv m
langEnv = LanguageEnv { load = const $ return ()
                      , def = const . const $ return ()
                      , call = callPrim
                      }

callPrim :: HeapMonad m => Expr -> m Val
callPrim (App (App (App (Var (Id (Name "ite" _) _)) b) e) e') =
    case b of
        Var (Id (Name "true" _) _) -> undefined -- e
        Var (Id (Name "false" _) _) -> undefined -- e'
callPrim (App (App (Var (Id (Name ">=" _) _)) (Lit (LInt l))) (Lit (LInt l')))
    | l <= l' = undefined -- Var (Id (Name "true" Nothing) (TyCon (Name "Bool" Nothing) TYPE))
    | otherwise = undefined -- Var (Id (Name "false" Nothing) (TyCon (Name "Bool" Nothing) TYPE))
callPrim (App (App (Var (Id (Name "-" _) _)) (Lit (LInt l))) (Lit (LInt l'))) = return . LitVal $ LInt (l - l')