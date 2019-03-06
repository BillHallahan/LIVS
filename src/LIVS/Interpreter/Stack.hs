{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE MultiParamTypeClasses #-}

module LIVS.Interpreter.Stack ( Stack
                              , StackMonad (..)
                              , StackT
                              , StackM

                              , empty
                              , push
                              , pop
                              , peek

                              , runStackT
                              , evalStackT
                              , runStackM
                              , evalStackM ) where

import LIVS.Language.Monad.Heap
import LIVS.Language.Monad.Naming

import Control.Monad.State.Lazy
import Data.Functor.Identity

newtype Stack b = Stack [b]

empty :: Stack b
empty = Stack []

push :: b -> Stack b -> Stack b
push b (Stack stck) = Stack $ b:stck

pop :: Stack b -> Maybe (b, Stack b)
pop (Stack []) = Nothing
pop (Stack (b:stck)) = Just (b, Stack stck)

peek :: Stack b -> Maybe b
peek = fmap fst . pop

class Monad m => StackMonad b m where
    pushM :: b -> m ()
    popM :: m (Maybe b)
    peekM :: m (Maybe b)

newtype StackT b m a = StackT (StateT (Stack b) m a)
                       deriving (Applicative, Functor, Monad)

type StackM b a = StackT b Identity a

instance MonadTrans (StackT b) where
    lift = StackT . lift

instance Monad m => MonadState (Stack b) (StackT b m) where
    state f = StackT (state f)

instance Monad m => StackMonad b (StackT b m) where
    pushM a = do
        stck <- get
        put $ push a stck

    popM = do
        stck <- get
        case pop stck of
            Just (a, stck') -> do
                put stck'
                return $ Just a
            Nothing -> return Nothing

    peekM = do
        stck <- get
        return $ peek stck

instance HeapMonad m => HeapMonad (StackT b m) where
    getHeap = lift getHeap
    putHeap = lift . putHeap

instance NameGenMonad m => NameGenMonad (StackT b m) where
    freshNameM = lift . freshNameM
    unseededFreshNameM = lift unseededFreshNameM

instance StackMonad b m => StackMonad b (HeapT m) where
    pushM = lift . pushM
    popM = lift popM
    peekM = lift peekM

instance StackMonad b m => StackMonad b (NameGenT m) where
    pushM = lift . pushM
    popM = lift popM
    peekM = lift peekM

runStackT :: Monad m => StackT b m a -> Stack b -> m (a, Stack b)
runStackT (StackT ht) = runStateT ht

evalStackT :: Monad m => StackT b m a -> Stack b -> m a
evalStackT (StackT h) = evalStateT h

runStackM :: StackM b a -> Stack b -> (a, Stack b)
runStackM hm = runIdentity . runStackT hm

evalStackM :: StackM b a -> Stack b -> a
evalStackM hm = runIdentity . evalStackT hm
