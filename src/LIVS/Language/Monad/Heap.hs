{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE MultiParamTypeClasses #-}

module LIVS.Language.Monad.Heap ( HeapMonad (..)
                                , HeapT
                                , HeapM
                                , heapT

                                , runHeapT
                                , evalHeapT
                                , runHeapM
                                , evalHeapM
                                , insertDefH
                                , insertPrimitiveH
                                , lookupH
                                , mapH
                                , mapMH
                                , mapDefsMH ) where

import LIVS.Language.Heap (Heap, HeapObj)
import qualified LIVS.Language.Heap as H
import LIVS.Language.Syntax

import Control.Monad.State.Lazy
import Data.Functor.Identity

import LIVS.Language.Monad.Naming

class Monad m => HeapMonad m where
    getHeap :: m Heap
    putHeap :: Heap -> m ()

newtype HeapT m a = HeapT (StateT Heap m a)
                    deriving (Applicative, Functor, Monad)

type HeapM a = HeapT Identity a

instance MonadTrans HeapT where
    lift = HeapT . lift
    
instance Monad m => MonadState Heap (HeapT m) where
    state f = HeapT (state f)

instance Monad m => HeapMonad (HeapT m) where
    getHeap = get
    putHeap = put

instance HeapMonad m => HeapMonad (NameGenT m) where
    getHeap = lift getHeap
    putHeap = lift . putHeap

instance NameGenMonad m => NameGenMonad (HeapT m) where
    freshNameM = lift . freshNameM
    unseededFreshNameM = lift unseededFreshNameM

heapT :: Monad m => (Heap -> m (a, Heap)) -> HeapT m a
heapT = HeapT . StateT

runHeapT :: Monad m => HeapT m a -> Heap -> m (a, Heap)
runHeapT (HeapT ht) = runStateT ht

evalHeapT :: Monad m => HeapT m a -> Heap -> m a
evalHeapT (HeapT h) = evalStateT h

runHeapM :: HeapM a -> Heap -> (a, Heap)
runHeapM hm = runIdentity . runHeapT hm

evalHeapM :: HeapM a -> Heap -> a
evalHeapM hm = runIdentity . evalHeapT hm

insertDefH :: HeapMonad m => Name -> Expr -> m ()
insertDefH = liftHeap2 H.insertDef

insertPrimitiveH :: HeapMonad m => Name -> Type -> m ()
insertPrimitiveH = liftHeap2 H.insertPrimitive

lookupH :: HeapMonad m => Name -> m (Maybe HeapObj)
lookupH n = do
    h <- getHeap
    return $ H.lookup n h

mapH :: HeapMonad m => (HeapObj -> HeapObj) -> m ()
mapH = liftHeap1 H.map

mapMH :: HeapMonad m => (HeapObj -> m HeapObj) -> m ()
mapMH f = do
    h <- getHeap
    putHeap =<< H.mapM f h

mapDefsMH :: HeapMonad m => (Expr -> m Expr) -> m ()
mapDefsMH f = do
    h <- getHeap
    putHeap =<< H.mapM f' h
    where
        f' (H.Def e) = return . H.Def =<< f e
        f' p@(H.Primitive _) = return p

liftHeap1 :: HeapMonad m => (a -> Heap -> Heap) -> a -> m ()
liftHeap1 f x = do
    h <- getHeap
    putHeap $ f x h

liftHeap2 :: HeapMonad m => (a -> b -> Heap -> Heap) -> a -> b -> m ()
liftHeap2 f x y = do
    h <- getHeap
    putHeap $ f x y h