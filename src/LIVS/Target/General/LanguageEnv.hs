{-# LANGUAGE RankNTypes #-}

module LIVS.Target.General.LanguageEnv ( FuncInfo (..)
                                       , idsAndCalls
                                       , idsAndConsts
                                       , addCalls
                                       , Load
                                       , Def
                                       , Call
                                       , LanguageEnv (..)
                                       , liftLanguageEnv ) where

import LIVS.Language.Syntax

import Data.Semigroup

-- Information about the body of a function
data FuncInfo = FuncInfo { calls :: [Id]
                         , consts :: [Val] }
                deriving (Eq, Show, Read)

instance Semigroup FuncInfo where
    f1 <> f2 = FuncInfo { calls = calls f1 <> calls f2
                        , consts = consts f1 <> consts f2 }

instance Monoid FuncInfo where
    mempty = FuncInfo { calls = [], consts = [] }
    mappend = (<>)

idsAndCalls :: [(Id, FuncInfo)] -> [(Id, [Id])]
idsAndCalls = map (\(i, fi) -> (i, calls fi))

idsAndConsts :: [(Id, FuncInfo)] -> [(Id, [Val])]
idsAndConsts = map (\(i, fi) -> (i, consts fi))

addCalls :: FuncInfo -> [Id] -> FuncInfo
addCalls fi is = fi { calls = calls fi ++ is }

-- | Given a code file, extracts:
-- 1) Function declarations, i.e. function names and types
-- 2) For each function f, the names and types of the functions f calls
-- 3) For each function f, contained constant values
type Extract m b = FilePath -> m ([(Id, FuncInfo)], b)

-- | Load a file with the given name into a REPL
type Load m = FilePath -> m ()

-- | Initializes an environment with a definition of a function with the given
-- name and body
type Def m b = b -> Id -> Expr -> m ()

-- | Converts the Expr to the target language, concretely computes the result,
-- and parses to a Lit
type Call m b = b -> Expr -> m Val

-- | An interface to interact with an external language interpreter/compiler
data LanguageEnv m b = LanguageEnv { extract :: Extract m b
                                   , load :: Load m
                                   , def :: Def m b
                                   , call :: Call m b }

liftLanguageEnv :: (forall a . m a -> m' a) -> LanguageEnv m b -> LanguageEnv m' b
liftLanguageEnv f (LanguageEnv { extract = ex, load = l, def = d, call = c }) =
    LanguageEnv { extract = \fp -> f $ ex fp
                , load = \fp -> f $ l fp
                , def = \b i e -> f $ d b i e
                , call = \b e -> f $ c b e }
                