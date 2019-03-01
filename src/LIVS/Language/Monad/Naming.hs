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

newtype NameGenT m a = NameGenT (StateT NameGenW m a)
                       deriving (Applicative, Functor, Monad)

type NameGenM a = NameGenT Identity a

newtype NameGenW = NameGenW NameGen

instance Monad m => MonadState NameGenW (NameGenT m) where
    state f = NameGenT (state f)

instance Monad m => NameGenMonad (NameGenT m) where
    freshNameM n = do
        ng <- get
        case ng of
          NameGenW ng' -> do
              let (n', ng'') = freshName n ng'
              put (NameGenW ng'')
              return n'

runNameGenT :: Monad m => NameGenT m a -> NameGen -> m (a, NameGen)
runNameGenT (NameGenT ngt) ng = do
    (a, ng') <- runStateT ngt $ NameGenW ng
    case ng' of
        NameGenW ng'' -> return (a, ng'')

evalNameGenT :: Monad m => NameGenT m a -> NameGen -> m a
evalNameGenT (NameGenT ng) = evalStateT ng . NameGenW

runNameGenM :: NameGenM a -> NameGen -> (a, NameGen)
runNameGenM ngm = runIdentity . runNameGenT ngm

evalNameGenM :: NameGenM a -> NameGen -> a
evalNameGenM ngm = runIdentity . evalNameGenT ngm