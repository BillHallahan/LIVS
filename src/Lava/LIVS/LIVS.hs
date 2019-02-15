-- Language Independence Via Synthesis
module Lava.LIVS.LIVS ( Call
                      , Fuzz
                      , livs
                      , synthOrder ) where

import Lava.Language.CallGraph
import qualified Lava.Language.Heap as H
import Lava.Language.Syntax
import Lava.Sygus.CVC4Interface
import Lava.Sygus.SMTParser
import Lava.Sygus.SMTLexer
import Lava.Sygus.ToSygus

import Data.List
import qualified Data.Map as M
import qualified Data.Set as S

-- | Converts the Expr to the target language, concretely computes the result,
-- and parses back to an Expr
type Call = Expr -> IO Expr

type Fuzz = Name -> IO [Example]

livs :: Fuzz -> Call -> CVC4 -> CallGraph -> IO H.Heap
livs fuzz call cvc4 cg =
    let
        ord = synthOrder cg
    in
    livs' fuzz call cvc4 cg [] H.empty ord

livs' :: Fuzz -> Call -> CVC4 -> CallGraph -> [Example] -> H.Heap -> [Name] -> IO H.Heap
livs' _ _ _ _ _ h [] = return h
livs' fuzz call cvc4 cg es h (n:ns) = do
    -- Get examples
    let re = examplesForFunc n es
    re' <- if re == [] then fuzz n else return re

    let relH = filterToReachable n cg h

    -- Take a guess at the definition of the function
    let form = toSygus relH re'
    r <- runCVC4 cvc4 form
    let r' = parse M.empty . lexer $ r

    -- Check if our guess is correct.  If it is NOT correct,
    -- it must be the case that we made an incorrect guess about some previous,
    -- component function
    cor <- checkFuncs call re' r'

    let h' = M.foldrWithKey H.insert h r'

    if cor
        then livs' fuzz call cvc4 cg es h' ns
        else undefined

-- | Decides an order to synthesize function definitions in.
-- The only real constraint here is that, before synthesizing a function f,
-- we want to synthesize all function's it calls, f_1...f_n.
-- This is always possible, except in the case of mutual recursion, which we
-- break arbitrarily
synthOrder :: CallGraph -> [Name]
synthOrder = nub . concatMap (reverse . synthOrder') . dfs
    where
        synthOrder' :: CallTree -> [Name]
        synthOrder' ct = vert ct:concatMap synthOrder' (trees ct)

-- | Filter the Heap to the functions relevant to the given function,
-- based on the CallGraph
filterToReachable :: Name -> CallGraph -> H.Heap -> H.Heap
filterToReachable n cg =
    let
        r = reachable n cg
    in
    H.filterWithKey (\n' _ -> n' `S.member` r)

checkFuncs :: Call -> [Example] -> M.Map Name Expr -> IO Bool
checkFuncs = undefined