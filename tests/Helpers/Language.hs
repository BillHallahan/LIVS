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
heapPrim = H.fromList [ (Name "+" Nothing, H.Primitive $ TyFun intType (TyFun intType intType))
                      , (Name "-" Nothing, H.Primitive $ TyFun intType (TyFun intType intType))
                      , (Name "=" Nothing, H.Primitive $ TyFun intType (TyFun intType boolType))
                      , (Name ">=" Nothing, H.Primitive $ TyFun intType (TyFun intType boolType))
                      , (Name "ite" Nothing, H.Primitive $ TyFun boolType (TyFun intType (TyFun intType intType)))]

heapAbs :: H.Heap
heapAbs = H.fromList
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
    , ( Name "abs3" Nothing
      , H.Def
            (Lam 
                (Id (Name "x1" Nothing) intType) 
                (App 
                    (Var (Id (Name "abs2" Nothing) (TyFun intType intType))) 
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

callGraphAbs :: CallGraph
callGraphAbs = createCallGraph callGraphAbs'

callGraphAbs' :: [ (Id, [Id])]
callGraphAbs' =
    [ ( Id (Name "abs2" Nothing) (TyFun intType intType)
      , [subId, gteId, iteId])
    , ( Id (Name "abs3" Nothing) (TyFun intType intType)
      , [Id (Name "abs2" Nothing) (TyFun intType intType)])
    ]


iteId :: Id
iteId = Id (Name "ite" Nothing) (TyFun (TyCon (Name "Bool" Nothing) TYPE) (TyFun intType (TyFun intType intType)))

gteId :: Id
gteId = Id (Name ">=" Nothing) (TyFun intType (TyFun intType (TyCon (Name "Bool" Nothing) TYPE)))

subId :: Id
subId = Id (Name "-" Nothing) (TyFun intType (TyFun intType intType))
