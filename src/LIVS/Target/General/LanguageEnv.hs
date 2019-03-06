{-# LANGUAGE RankNTypes #-}

module LIVS.Target.General.LanguageEnv ( Load
                                       , Def
                                       , Call
                                       , LanguageEnv (..)
                                       , liftLanguageEnv ) where

import LIVS.Language.Syntax

-- | Load a file with the given name
type Load m = FilePath -> m ()

-- | Initializes an environment with a definition of a function with the given
-- name and body
type Def m = Id -> Expr -> m ()

-- | Converts the Expr to the target language, concretely computes the result,
-- and parses to a Lit
type Call m = Expr -> m Val

-- | An interface to interact with an external language interpreter/compiler
data LanguageEnv m = LanguageEnv { load :: Load m
                                 , def :: Def m
                                 , call :: Call m }

liftLanguageEnv :: (forall a . m a -> m' a) -> LanguageEnv m -> LanguageEnv m'
liftLanguageEnv f (LanguageEnv { load = l, def = d, call = c }) =
    LanguageEnv { load = \fp -> f $ l fp
                , def = \i e -> f $ d i e
                , call = \e -> f $ c e }
                