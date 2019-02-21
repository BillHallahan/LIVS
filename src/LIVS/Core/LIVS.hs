-- Language Independence Via Synthesis
module LIVS.Core.LIVS ( Call
                      , livs
                      , synthOrder ) where

import LIVS.Language.CallGraph
import qualified LIVS.Language.Heap as H
import LIVS.Language.Syntax
import LIVS.Core.Fuzz
import LIVS.Sygus.CVC4Interface
import LIVS.Sygus.SMTParser
import LIVS.Sygus.SMTLexer
import LIVS.Sygus.ToSygus

import Control.Monad.Random
import Data.List
import qualified Data.Map as M
import qualified Data.HashSet as S

-- | Converts the Expr to the target language, concretely computes the result,
-- and parses to a Lit
type Call = Expr -> IO Lit

livs :: (MonadIO m, MonadRandom m) => Call -> CVC4 -> CallGraph -> m H.Heap
livs call cvc4 cg =
    let
        ord = synthOrder cg
    in
    livs' call cvc4 cg [] H.empty ord

livs' :: (MonadIO m, MonadRandom m) => Call -> CVC4 -> CallGraph -> [Example] -> H.Heap -> [Id] -> m H.Heap
livs' _ _ _ _ h [] = return h
livs' call cvc4 cg es h (i@(Id n _):ns) = do
    -- Get examples
    let re = examplesForFunc n es
    re' <- if re == [] then fuzzExamplesM call i 10 else return re

    let relH = filterToReachable i cg h

    -- Take a guess at the definition of the function
    let form = toSygus relH re'
    m <- liftIO $ runAndReadCVC4 cvc4 form
    let m' = parse M.empty . lexer $ m
        r = case M.lookup n m' of
            Just r' -> r'
            Nothing -> error "No function definition found."

    -- Check if our guess is correct.  If it is NOT correct,
    -- it must be the case that we made an incorrect guess about some previous,
    -- component function
    cor <- checkFuncs call re' r

    let h' = H.insert n r h

    if cor
        then livs' call cvc4 cg es h' ns
        else undefined

-- | Decides an order to synthesize function definitions in.
-- The only real constraint here is that, before synthesizing a function f,
-- we want to synthesize all function's it calls, f_1...f_n.
-- This is always possible, except in the case of mutual recursion, which we
-- break arbitrarily
synthOrder :: CallGraph -> [Id]
synthOrder = nub . concatMap (reverse . synthOrder') . dfs
    where
        synthOrder' :: CallTree -> [Id]
        synthOrder' ct = vert ct:concatMap synthOrder' (trees ct)

-- | Filter the Heap to the functions relevant to the given function,
-- based on the CallGraph
filterToReachable :: Id -> CallGraph -> H.Heap -> H.Heap
filterToReachable n cg =
    let
        r = S.map idName $ reachable n cg
    in
    H.filterWithKey (\n' _ -> n' `S.member` r)

checkFuncs :: Call -> [Example] -> Expr -> m Bool
checkFuncs = undefined