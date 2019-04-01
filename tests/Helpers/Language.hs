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
heapPrim = H.fromList [ (Name SMT "+" Nothing, H.Primitive $ TyFun intType (TyFun intType intType))
                      , (Name SMT "-" Nothing, H.Primitive $ TyFun intType (TyFun intType intType))
                      , (Name SMT "=" Nothing, H.Primitive $ TyFun intType (TyFun intType boolType))
                      , (Name SMT ">=" Nothing, H.Primitive $ TyFun intType (TyFun intType boolType))
                      , (Name SMT "ite" Nothing, H.Primitive $ TyFun boolType (TyFun intType (TyFun intType intType)))]

heapAbs :: H.Heap
heapAbs = H.fromList
    [ ( Name Ident "abs2" Nothing
      , H.Def 
            (Lam 
                (Id (Name Ident "x1" Nothing) intType) 
                (App 
                    (App 
                        (App 
                            (Var iteId) 
                            (App 
                                (App 
                                    (Var gteId) 
                                    (Lit (LInt 0))
                                ) 
                                (Var (Id (Name Ident "x1" Nothing) intType))
                            )
                        ) 
                        (App 
                            (App 
                                (Var subId) 
                                (Lit (LInt 0))
                            ) 
                            (Var (Id (Name Ident "x1" Nothing) intType))
                        )
                    ) 
                    (Var (Id (Name Ident "x1" Nothing) intType))
                )
            )
        )
    , ( Name Ident "abs3" Nothing
      , H.Def
            (Lam 
                (Id (Name Ident "x1" Nothing) intType) 
                (App 
                    (Var (Id (Name Ident "abs2" Nothing) (TyFun intType intType))) 
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

callGraphAbs :: CallGraph
callGraphAbs = createCallGraph callGraphAbs'

callGraphAbs' :: [ (Id, [Id])]
callGraphAbs' =
    [ ( Id (Name Ident "abs2" Nothing) (TyFun intType intType)
      , [subId, gteId, iteId])
    , ( Id (Name Ident "abs3" Nothing) (TyFun intType intType)
      , [Id (Name Ident "abs2" Nothing) (TyFun intType intType)])
    ]


iteId :: Id
iteId = Id (Name SMT "ite" Nothing) (TyFun boolType (TyFun intType (TyFun intType intType)))

gteId :: Id
gteId = Id (Name SMT ">=" Nothing) (TyFun intType (TyFun intType boolType))

subId :: Id
subId = Id (Name SMT "-" Nothing) (TyFun intType (TyFun intType intType))
