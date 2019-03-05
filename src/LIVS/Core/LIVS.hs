-- Language Independence Via Synthesis
module LIVS.Core.LIVS ( Load
                      , Def
                      , Call
                      , Gen
                      , livsCVC4
                      , livs ) where

import LIVS.Language.CallGraph
import LIVS.Language.Expr
import qualified LIVS.Language.Heap as H
import LIVS.Language.Syntax
import LIVS.Core.Fuzz
import LIVS.Sygus.CVC4Interface
import LIVS.Sygus.Result
import LIVS.Target.General.LanguageEnv

import Control.Monad.Random
import qualified Data.HashMap.Lazy as HM
import qualified Data.HashSet as S
import Data.List

-- Generates code satisfying a set of examples
type Gen m = H.Heap -> S.HashSet Name -> [Example] -> m Result

livsCVC4 :: (MonadIO m, MonadRandom m) => LanguageEnv m -> FilePath -> CallGraph -> H.Heap -> m H.Heap
livsCVC4 le fp cg = livs le (runSygusWithGrammar cg) fp cg

livs :: MonadRandom m => LanguageEnv m -> Gen m -> FilePath -> CallGraph -> H.Heap -> m H.Heap
livs le gen fp cg h = do
    -- before synthesizing a function f, we want to synthesize all
    -- function's it calls, f_1...f_n.
    -- This is always possible, except in the case of mutual recursion, which we
    -- break arbitrarily
    let ord = filter (not . flip H.isPrimitive h . idName) $ postOrderList cg

    load le fp
    livs' le gen fp cg [] h ord

livs' :: MonadRandom m => 
        LanguageEnv m -> Gen m -> FilePath -> CallGraph -> [Example] -> H.Heap -> [Id] -> m H.Heap
livs' _ _ _ _ _ h [] = return h
livs' le gen fp cg es h (i@(Id n _):is) = do
    -- Get examples
    let re = examplesForFunc n es
    re' <- if re == [] then fuzzExamplesM le fp 2 i else return re

    let relH = H.filterWithKey (\n' _ -> n /= n') $ filterToReachable i cg h
        gram = S.map idName $ directlyCalls i cg

    -- Take a guess at the definition of the function
    m <- gen relH gram re'

    case m of
        Sat m' -> do
            let r = case HM.lookup n m' of
                    Just r' -> r'
                    Nothing -> error "livs': No function definition found."

            -- Check if our guess is correct.  If it is NOT correct,
            -- it must be the case that we made an incorrect guess about some previous,
            -- component function
            cor <- checkExamples le fp i r re'

            let h' = H.insertDef n r h

            if cor
                then livs' le gen fp cg (nub $ re' ++ es) h' is
                else error "livs': Incorrect guess"

        _ -> livsUnSatUnknown i le gen fp cg (re' ++ es) h is
        
-- | Sometimes, the SyGuS solver may return UnSat, or Unknown.  In either case,
-- it may be that previously synthesized functions had incorrect definitions.
-- However, because we don't even have a guess about the possible correct definition,
-- we simply return to and add examples for all functions directly called in the call graph.
livsUnSatUnknown :: MonadRandom m => 
        Id -> LanguageEnv m -> Gen m -> FilePath ->  CallGraph -> [Example] -> H.Heap -> [Id] -> m H.Heap
livsUnSatUnknown i le gen fp cg es h is = do
    let dc = filter (not . flip H.isPrimitive h . idName) 
                                $ S.toList $ directlyCalls i cg
        is' = dc ++ i:is

    es' <- mapM (fuzzExamplesM le fp 2) dc

    livs' le gen fp cg (es ++ concat es') h is'

-- | Filter the Heap to the functions relevant to the given function,
-- based on the CallGraph
filterToReachable :: Id -> CallGraph -> H.Heap -> H.Heap
filterToReachable i cg =
    let
        r = S.map idName $ reachable i cg
    in
    H.filterWithKey (\n' _ -> n' `S.member` r)

-- | Checks that the given synthesized function satisfies the examples
checkExamples :: Monad m => LanguageEnv m -> FilePath -> Id -> Expr -> [Example] -> m Bool
checkExamples le fp i e es = do
    load le fp
    def le i e
    return . and =<< mapM (checkExample (call le) i) es

checkExample :: Monad m => Call m -> Id -> Example -> m Bool
checkExample ca i (Example { input = is, output = out}) = do
    r <- ca . mkApp $ Var i:map valToExpr is
    return $ r == out