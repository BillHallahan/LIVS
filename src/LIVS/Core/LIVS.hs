-- Language Independence Via Synthesis
module LIVS.Core.LIVS ( Def
                      , Call
                      , livsCVC4
                      , livs
                      , synthOrder ) where

import LIVS.Language.CallGraph
import LIVS.Language.Expr
import qualified LIVS.Language.Heap as H
import LIVS.Language.Syntax
import LIVS.Core.Fuzz
import LIVS.Sygus.CVC4Interface

import Control.Monad.Random
import Data.List
import qualified Data.HashMap.Lazy as HM
import qualified Data.HashSet as S

-- | Initializes an environment with a definition of a function with the given
-- name and body
type Def m = Id -> Expr -> m ()

-- | Converts the Expr to the target language, concretely computes the result,
-- and parses to a Lit
type Call m = Expr -> m Lit

-- Generates code satisfying a set of examples
type Gen m = H.Heap -> S.HashSet Name -> [Example] -> m (HM.HashMap Name Expr)

livsCVC4 :: (MonadIO m, MonadRandom m) => Def m -> Call m -> CallGraph -> H.Heap -> m H.Heap
livsCVC4 def call = livs def call runSygusWithGrammar

livs :: MonadRandom m => Def m -> Call m -> Gen m -> CallGraph -> H.Heap -> m H.Heap
livs def call gen cg h =
    let
        ord = filter (not . flip H.isPrimitive h . idName) $ synthOrder cg
    in
    livs' def call gen cg [] h ord

livs' :: MonadRandom m => 
        Def m -> Call m -> Gen m -> CallGraph -> [Example] -> H.Heap -> [Id] -> m H.Heap
livs' _ _ _ _ _ h [] = return h
livs' def call gen cg es h (i@(Id n _):ns) = do
    -- Get examples
    let re = examplesForFunc n es
    re' <- if re == [] then fuzzExamplesM call i 3 else return re

    let relH = filterToReachable i cg h
        gram = S.map idName $ directlyCalls i cg

    -- Take a guess at the definition of the function
    m <- gen relH gram re'

    let r = case HM.lookup n m of
            Just r' -> r'
            Nothing -> error "No function definition found."

    -- Check if our guess is correct.  If it is NOT correct,
    -- it must be the case that we made an incorrect guess about some previous,
    -- component function
    cor <- checkExamples def call i r re'

    let h' = H.insertDef n r h

    if cor
        then livs' def call gen cg es h' ns
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
filterToReachable i cg =
    let
        r = S.map idName $ reachable i cg
    in
    H.filterWithKey (\n' _ -> n' `S.member` r)

-- | Checks that the given synthesized function satisfies the examples
checkExamples :: Monad m => Def m -> Call m -> Id -> Expr -> [Example] -> m Bool
checkExamples def call i e es = do
    def i e
    return . and =<< mapM (checkExample call i) es

checkExample :: Monad m => Call m -> Id -> Example -> m Bool
checkExample call i (Example { input = is, output = out}) = do
    r <- call . mkApp $ Var i:map Lit is
    return $ r == out