{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE MultiParamTypeClasses #-}

module LIVS.Language.Monad.Naming ( NameGenMonad (..)
                                  , NameGenT
                                  , NameGenM
                                  , nameGenT

                                  , runNameGenT
                                  , evalNameGenT
                                  , runNameGenM
                                  , evalNameGenM

                                  , freshIdM
                                  , unseededFreshIdM ) where

import LIVS.Language.Naming
import LIVS.Language.Syntax

import Control.Monad.State.Lazy
import Data.Functor.Identity

class Monad m => NameGenMonad m where
    freshNameM :: Name -> m Name
    unseededFreshNameM :: m Name
    unseededFreshNameM = freshNameM (InternalName "fresh" Nothing Nothing)

newtype NameGenT m a = NameGenT (StateT NameGen m a)
                       deriving (Applicative, Functor, Monad)

type NameGenM a = NameGenT Identity a

instance MonadTrans NameGenT where
    lift = NameGenT . lift

instance Monad m => MonadState NameGen (NameGenT m) where
    state f = NameGenT (state f)

instance Monad m => NameGenMonad (NameGenT m) where
    freshNameM n = do
        ng <- get
        let (n', ng') = freshName n ng
        put ng'
        return n'

nameGenT :: Monad m => (NameGen -> m (a, NameGen)) -> NameGenT m a
nameGenT = NameGenT . StateT

runNameGenT :: Monad m => NameGenT m a -> NameGen -> m (a, NameGen)
runNameGenT (NameGenT ngt) = runStateT ngt

evalNameGenT :: Monad m => NameGenT m a -> NameGen -> m a
evalNameGenT (NameGenT ng) = evalStateT ng

runNameGenM :: NameGenM a -> NameGen -> (a, NameGen)
runNameGenM ngm = runIdentity . runNameGenT ngm

evalNameGenM :: NameGenM a -> NameGen -> a
evalNameGenM ngm = runIdentity . evalNameGenT ngm

freshIdM :: NameGenMonad m => Name -> Type -> m Id
freshIdM n t = do
    n' <- freshNameM n
    return (Id n' t)

unseededFreshIdM :: NameGenMonad m => Type -> m Id
unseededFreshIdM = freshIdM (InternalName "fresh" Nothing Nothing)