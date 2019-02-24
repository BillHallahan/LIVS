-- Language Independence Via Synthesis
module LIVS.Core.LIVS ( Def
                      , Call
                      , livs
                      , synthOrder ) where

import LIVS.Language.CallGraph
import LIVS.Language.Expr
import qualified LIVS.Language.Heap as H
import LIVS.Language.Syntax
import LIVS.Language.Typing
import LIVS.Core.Fuzz
import LIVS.Sygus.CVC4Interface
import LIVS.Sygus.SMTParser
import LIVS.Sygus.SMTLexer
import LIVS.Sygus.ToSygus

import Control.Monad.Random
import Data.List
import qualified Data.HashMap.Lazy as HM
import qualified Data.HashSet as S

import Debug.Trace

-- | Initializes an environment with a definition of a function with the given
-- name and body
type Def = Id -> Expr -> IO ()

-- | Converts the Expr to the target language, concretely computes the result,
-- and parses to a Lit
type Call = Expr -> IO Lit

livs :: (MonadIO m, MonadRandom m) => Def -> Call -> CallGraph -> H.Heap -> m H.Heap
livs def call cg h =
    let
        ord = synthOrder cg
    in
    livs' def call cg [] h ord

livs' :: (MonadIO m, MonadRandom m) => 
        Def -> Call -> CallGraph -> [Example] -> H.Heap -> [Id] -> m H.Heap
livs' _ _ _ _ h [] = return h
livs' def call cg es h (i@(Id n _):ns) = do
    -- Get examples
    let re = examplesForFunc n es
    re' <- if re == [] then fuzzExamplesM call i 3 else return re

    let relH = filterToReachable i cg h

    -- Take a guess at the definition of the function
    liftIO $ print h
    liftIO $ print relH
    let form = toSygus relH re'
    liftIO $ putStrLn form
    m <- liftIO $ runCVC4WithFile form

    let m' = parseSMT (H.map' typeOf h) . lexSMT $ m
        r = case HM.lookup n m' of
            Just r' -> r'
            Nothing -> error "No function definition found."

    -- Check if our guess is correct.  If it is NOT correct,
    -- it must be the case that we made an incorrect guess about some previous,
    -- component function
    cor <- liftIO $ checkExamples def call i r re'

    let h' = H.insertDef n r h

    if cor
        then livs' def call cg es h' ns
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
    trace ("r = " ++ show r) H.filterWithKey (\n' _ -> n' `S.member` r)

-- | Checks that the given synthesized function satisfies the examples
checkExamples :: MonadIO m => Def -> Call -> Id -> Expr -> [Example] -> m Bool
checkExamples def call i e es = do
    liftIO $ def i e
    return . and =<< mapM (checkExample call i) es

checkExample :: MonadIO m => Call -> Id -> Example -> m Bool
checkExample call i (Example { input = is, output = out}) = do
    r <- liftIO . call . mkApp $ Var i:map Lit is
    return $ r == out