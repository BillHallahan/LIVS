module Helpers.Language ( heapPrim
                        , heapAbs
                        , callGraphAbs
                        , callGraphAbs'
                        , iteId
                        , gteId
                        , subId) where

import LIVS.Language.CallGraph
import qualified LIVS.Language.Heap as H
import LIVS.Language.Syntax
import LIVS.Language.Typing

heapPrim :: H.Heap
heapPrim = H.fromList [ (SMTName "+", H.Primitive $ TyFun intType (TyFun intType intType))
                      , (SMTName "-", H.Primitive $ TyFun intType (TyFun intType intType))
                      , (SMTName "=", H.Primitive $ TyFun intType (TyFun intType boolType))
                      , (SMTName ">=", H.Primitive $ TyFun intType (TyFun intType boolType))
                      , (SMTName "ite", H.Primitive $ TyFun boolType (TyFun intType (TyFun intType intType)))]

heapAbs :: H.Heap
heapAbs = H.fromList
    [ ( IdentName "abs2"
      , H.Def 
            (Lam 
                (Id (IdentName "x1") intType) 
                (App 
                    (App 
                        (App 
                            (Var iteId) 
                            (App 
                                (App 
                                    (Var gteId) 
                                    (Lit (LInt 0))
                                ) 
                                (Var (Id (IdentName "x1") intType))
                            )
                        ) 
                        (App 
                            (App 
                                (Var subId) 
                                (Lit (LInt 0))
                            ) 
                            (Var (Id (IdentName "x1") intType))
                        )
                    ) 
                    (Var (Id (IdentName "x1") intType))
                )
            )
        )
    , ( IdentName "abs3"
      , H.Def
            (Lam 
                (Id (IdentName "x1") intType) 
                (App 
                    (Var (Id (IdentName "abs2") (TyFun intType intType))) 
                    (Var (Id (IdentName "x1") intType))
                )
            )
      )
    , ( SMTName "ite"
      , H.Primitive (TyFun boolType (TyFun intType (TyFun intType intType)))
      )
    , ( SMTName ">=" 
      , H.Primitive (TyFun intType (TyFun intType boolType))
      )
    , ( SMTName "-" 
      , H.Primitive (TyFun intType (TyFun intType intType))
      )
    ]

callGraphAbs :: CallGraph
callGraphAbs = createCallGraph callGraphAbs'

callGraphAbs' :: [ (Id, [Id])]
callGraphAbs' =
    [ ( Id (IdentName "abs2") (TyFun intType intType)
      , [subId, gteId, iteId])
    , ( Id (IdentName "abs3") (TyFun intType intType)
      , [Id (IdentName "abs2") (TyFun intType intType)])
    ]


iteId :: Id
iteId = Id (SMTName "ite") (TyFun boolType (TyFun intType (TyFun intType intType)))

gteId :: Id
gteId = Id (SMTName ">=") (TyFun intType (TyFun intType boolType))

subId :: Id
subId = Id (SMTName "-") (TyFun intType (TyFun intType intType))
