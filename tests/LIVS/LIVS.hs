module LIVS.LIVS where

import LIVS.Core.LIVS
import LIVS.Language.CallGraph
import qualified LIVS.Language.Heap as H
import LIVS.Language.Syntax
import LIVS.Language.Typing
import LIVS.Target.General.LanguageEnv

import Helpers.Interpreter
import Helpers.Language

import Data.Functor.Identity
import Data.HashSet as HS

import Test.Tasty
import Test.Tasty.HUnit

livsTests :: TestTree
livsTests = testGroup "LIVS" [ livsSatCheckIncorrect1
                             , livsSatCheckIncorrect2 ]

livsSatCheckIncorrect1 :: TestTree
livsSatCheckIncorrect1 = testCase "livsSatCheckIncorrect Test 1"
    $ assertBool "Correct examples from livsSatCheckIncorrect"
        (HS.fromList (fst livsSatCheckIncorrect1_2) == HS.fromList fix_exs)
    where
        abs2 = Id (Name "abs2" Nothing) (TyFun intType intType)

        -- Input/output counterexamples for abs2, that are the result of running
        -- the interpreter on the exs  
        fix_exs = [ Example { func = abs2
                            , input = [LitVal (LInt (-3))]
                            , output = LitVal (LInt 3) }
                  , Example { func = abs2
                            , input = [LitVal (LInt (-12))]
                            , output = LitVal (LInt 12) }
                  ]

livsSatCheckIncorrect2 :: TestTree
livsSatCheckIncorrect2 = testCase "livsSatCheckIncorrect Test 2"
    $ assertBool "Correct to-synthesize list from livsSatCheckIncorrect"
        (let
            (_, r) = livsSatCheckIncorrect1_2
        in
        r == [abs2, f, g] || r == [abs2, g, f])
    where
        f = Id (Name "f" Nothing) (TyFun intType intType)
        g = Id (Name "g" Nothing) (TyFun intType intType)
        abs2 = Id (Name "abs2" Nothing) (TyFun intType intType)

-- | This is used by both livsSatCheckIncorrect1 and livsSatCheckIncorrect2
-- Two heaps are used: correctHeap corresponds to actual function definitions,
-- while h is the synthesized guessed version.  correctHeap is used, along with
-- the interpreter, as a ground truth, so that we can check that we correctly
-- identify needed examples and which functions to resynthesize 
livsSatCheckIncorrect1_2 :: ([Example], [Id])
livsSatCheckIncorrect1_2 =
    runIdentity (livsSatCheckIncorrect (langEnvInterpFallBack correctHeap) () (callPrimExprM correctHeap)
                                            callGraphAbsC [] h exs)
    where
        callGraphAbsC = createCallGraph $ [(f, [ abs2 ]), (g, [abs2])]

        correctHeap = H.fromList 
            [ ( Name "abs2" Nothing
              , H.Def 
                    (Lam 
                        (Id (Name "x1" Nothing) intType) 
                        (App 
                            (App 
                                (App 
                                    (Var iteId) 
                                    (App 
                                        (App 
                                            (Var gteId) 
                                            (Lit (LInt 0))
                                        ) 
                                        (Var (Id (Name "x1" Nothing) intType))
                                    )
                                ) 
                                (App 
                                    (App 
                                        (Var subId) 
                                        (Lit (LInt 0))
                                    ) 
                                    (Var (Id (Name "x1" Nothing) intType))
                                )
                            ) 
                            (Var (Id (Name "x1" Nothing) intType))
                        )
                    )
                )
            , ( Name "f" Nothing
              , H.Def
                    (Lam
                        (Id (Name "x1" Nothing) intType)
                        (Var (Id (Name "x1" Nothing) intType))
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
        -- Here, the component function is the absolute value function, but 
        -- \x -> x has been incorrectly guessed
        h = H.fromList 
            [ ( Name "abs2" Nothing
              , H.Def
                    (Lam
                        (Id (Name "x1" Nothing) intType)
                        (Var (Id (Name "x1" Nothing) intType))
                    )
              )
            , ( Name "f" Nothing
              , H.Def
                    (Lam
                        (Id (Name "x1" Nothing) intType)
                        (App
                            (Var abs2)
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

        f = Id (Name "f" Nothing) (TyFun intType intType)
        g = Id (Name "g" Nothing) (TyFun intType intType)
        abs2 = Id (Name "abs2" Nothing) (TyFun intType intType)

        exs = [ Example { func = f
                        , input = [LitVal (LInt (-3))]
                        , output = LitVal (LInt (-3)) }
              , Example { func = f
                        , input = [LitVal (LInt (-12))]
                        , output = LitVal (LInt (-12)) }
              , Example { func = f
                        , input = [LitVal (LInt 6)]
                        , output = LitVal (LInt 6) }
              ]


-- f :: H.Heap
-- f = evalRand (livs undefined undefined undefined undefined undefined) (mkStdGen 0)

-- callGraph1 :: CallGraph
-- callGraph1 = createCallGraph
--     [ ( Id (Name "double" Nothing) (TyFun intType intType)
--       , [Id (Name "add" Nothing) (TyFun intType (TyFun intType intType))])
--     , ( Id (Name "quadruple" Nothing) (TyFun intType intType)
--       , [Id (Name "double" Nothing) (TyFun intType intType)])
--     , ( Id (Name "add" Nothing) (TyFun intType (TyFun intType intType))
--       , [Id (Name "+" Nothing) (TyFun intType (TyFun intType intType))])
--     ]

testEnv :: LanguageEnv Identity ()
testEnv = LanguageEnv { load = const $ return ()
                      , def = undefined
                      , call = undefined }