{-# LANGUAGE RankNTypes #-}

module LIVS.Target.General.LanguageEnv ( Load
                                       , Def
                                       , Call
                                       , LanguageEnv (..)
                                       , liftLanguageEnv ) where

import LIVS.Language.Syntax

-- | Given a code file, extracts:
-- 1) Function declarations, i.e. function names and types
-- 2) For each function f, the names and types of the functions f calls 
type Extract m = FilePath -> m [ (Id, [Id]) ]

-- | Load a file with the given name into a REPL
type Load m = FilePath -> m ()

-- | Initializes an environment with a definition of a function with the given
-- name and body
type Def m = Id -> Expr -> m ()

-- | Converts the Expr to the target language, concretely computes the result,
-- and parses to a Lit
type Call m = Expr -> m Val

-- | An interface to interact with an external language interpreter/compiler
data LanguageEnv m = LanguageEnv { extract :: Extract m
                                 , load :: Load m
                                 , def :: Def m
                                 , call :: Call m }

liftLanguageEnv :: (forall a . m a -> m' a) -> LanguageEnv m -> LanguageEnv m'
liftLanguageEnv f (LanguageEnv { extract = ex, load = l, def = d, call = c }) =
    LanguageEnv { extract = \fp -> f $ ex fp
                , load = \fp -> f $ l fp
                , def = \i e -> f $ d i e
                , call = \e -> f $ c e }
                