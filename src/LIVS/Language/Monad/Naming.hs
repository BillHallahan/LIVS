{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE MultiParamTypeClasses #-}

module LIVS.Language.Monad.Naming ( NameGenMonad (..)
                                  , NameGenT
                                  , NameGenM
                                  , runNameGenT
                                  , evalNameGenT
                                  , runNameGenM
                                  , evalNameGenM ) where

import LIVS.Language.Naming

import Control.Monad.State.Lazy
import Data.Functor.Identity

class Monad m => NameGenMonad m where
    freshNameM :: Name -> m Name

newtype NameGenT m a = NameGenT (StateT NameGen m a)
                       deriving (Applicative, Functor, Monad)

type NameGenM a = NameGenT Identity a

instance Monad m => MonadState NameGen (NameGenT m) where
    state f = NameGenT (state f)

instance Monad m => NameGenMonad (NameGenT m) where
    freshNameM n = do
        ng <- get
        let (n', ng') = freshName n ng
        put ng'
        return n'

runNameGenT :: Monad m => NameGenT m a -> NameGen -> m (a, NameGen)
runNameGenT (NameGenT ngt) = runStateT ngt

evalNameGenT :: Monad m => NameGenT m a -> NameGen -> m a
evalNameGenT (NameGenT ng) = evalStateT ng

runNameGenM :: NameGenM a -> NameGen -> (a, NameGen)
runNameGenM ngm = runIdentity . runNameGenT ngm

evalNameGenM :: NameGenM a -> NameGen -> a
evalNameGenM ngm = runIdentity . evalNameGenT ngm