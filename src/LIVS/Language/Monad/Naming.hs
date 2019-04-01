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

import Control.Monad.Random
import Control.Monad.State.Lazy
import Data.Functor.Identity

class Monad m => NameGenMonad m where
    freshNameM :: Name -> m Name
    unseededFreshNameM :: LanguageLevel -> m Name
    unseededFreshNameM ll = freshNameM (Name ll "fresh" Nothing)

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

instance MonadIO m => MonadIO (NameGenT m) where
    liftIO = lift . liftIO

instance MonadRandom m => MonadRandom (NameGenT m) where
    getRandom = lift getRandom
    getRandoms = lift getRandoms
    getRandomR = lift . getRandomR
    getRandomRs = lift . getRandomRs

nameGenT :: Monad m => m a -> NameGenT m a -- (NameGen -> m (a, NameGen)) -> NameGenT m a
nameGenT = lift -- NameGenT . StateT

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

unseededFreshIdM :: NameGenMonad m => LanguageLevel -> Type -> m Id
unseededFreshIdM ll = freshIdM (Name ll "fresh" Nothing)