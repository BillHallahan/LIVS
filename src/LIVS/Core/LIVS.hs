-- Language Independence Via Synthesis
module LIVS.Core.LIVS ( Load
                      , Def
                      , Call
                      , Gen
                      , livsCVC4
                      , livs
                      , livsStep
                      , livsSatCheckIncorrect) where

import LIVS.Interpreter.Interpreter
import LIVS.Language.CallGraph
import qualified LIVS.Language.Heap as H
import LIVS.Language.Naming
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

-- Generates (typically random) inputs to a function
type Fuzz m = LanguageEnv m 
           -> Int -- ^ How many examples to fuzz
           -> Id -- ^ A function call
           -> m [Example]

livsCVC4 :: (MonadIO m, MonadRandom m) => LanguageEnv m -> FilePath -> CallGraph -> H.Heap -> m H.Heap
livsCVC4 le fp cg = livs le (runSygusWithGrammar cg) fp cg

livs :: MonadRandom m => LanguageEnv m -> Gen m -> FilePath -> CallGraph -> H.Heap -> m H.Heap
livs le gen fp cg h = do
    -- before synthesizing a function f, we want to synthesize all
    -- function's it calls, f_1...f_n.
    -- This is always possible, except in the case of mutual recursion, which we
    -- break arbitrarily
    let ord = synthOrder h cg

    load le fp
    livs' le gen cg [] h ord

livs' :: MonadRandom m => 
        LanguageEnv m -> Gen m -> CallGraph -> [Example] -> H.Heap -> [Id] -> m H.Heap
livs' _ _ _ _ h [] = return h
livs' le gen cg es h (i:is) = do
    (h', es', is') <- livsStep le gen fuzzExamplesM cg es h i
    livs' le gen cg es' h' (is' ++ is)

livsStep :: Monad m => 
        LanguageEnv m -> Gen m -> Fuzz m -> CallGraph -> [Example] -> H.Heap -> Id -> m (H.Heap, [Example], [Id])
livsStep le gen fuzz cg es h i@(Id n _) = do
    -- Get examples
    let re = examplesForFunc n es
    re' <- fuzz le 2 i
    let re'' = re ++ re'

    let relH = H.filterWithKey (\n' _ -> n /= n') $ filterToReachable i cg h
        gram = S.map idName $ directlyCalls i cg

    -- Take a guess at the definition of the function
    m <- gen relH gram re''

    case m of
        Sat m' -> do
            let r = case HM.lookup n m' of
                    Just r' -> r'
                    Nothing -> error "livs': No function definition found."

            let h' = H.insertDef n r h

            (es', is') <- livsSatCheckIncorrect le cg  (nub $ re'' ++ es) h' re''
            return (h', es', is')


        _ -> do
            let is' = livsUnSatUnknown cg h i
            return (h, nub $ re'' ++ es, is')

-- | Takes a list of examples, and determines which functions (if any) need to
-- be resynthesized, and which new examples should be used when doing so.
livsSatCheckIncorrect :: Monad m => LanguageEnv m -> CallGraph -> [Example] -> H.Heap -> [Example] -> m ([Example], [Id])
livsSatCheckIncorrect le cg es h exs = do
    -- Run the example inputs in the interpreter, collecting the suspect
    -- examples from function calls
    let runCollecting = runCollectingExamples le 1000 h (mkNameGen [])
    rs <- mapM (runCollecting) $ map exampleFuncCall exs

    -- Figure out which suspect function calls are actually incorrect.
    let maybe_incor_exs = concatMap snd rs
    incor <- incorrectSuspects le maybe_incor_exs

    -- Figure out which functions are involved in the incorrect function calls
    let bad_fs = map (func . iExample) incor
        is' = synthOrderAfter h bad_fs cg

    return (map fixIncorrect incor ++ es, is')

-- | Sometimes, the SyGuS solver may return UnSat, or Unknown.  In either case,
-- it may be that previously synthesized functions had incorrect definitions.
-- However, because we don't even have a guess about the possible correct definition,
-- we simply return to and add examples for all functions directly called in the call graph.
-- The returned list of id's is the functions which must be revisted.
livsUnSatUnknown :: CallGraph -> H.Heap -> Id -> [Id]
livsUnSatUnknown cg h i =
    let
        dc = filter (not . flip H.isPrimitive h . idName)
                                $ S.toList $ directlyCalls i cg
    in
    dc ++ [i]

-- | Filter the Heap to the functions relevant to the given function,
-- based on the CallGraph
filterToReachable :: Id -> CallGraph -> H.Heap -> H.Heap
filterToReachable i cg =
    let
        r = S.map idName $ reachable i cg
    in
    H.filterWithKey (\n' _ -> n' `S.member` r)

-- | Takes a list of possibly incorrect examples, and returns only those that are really incorrect.
incorrectSuspects :: Monad m => LanguageEnv m -> [SuspectExample] -> m [IncorrectExample]
incorrectSuspects le es = return . onlyIncorrect =<< markSuspects le es

markSuspects :: Monad m => LanguageEnv m -> [SuspectExample] -> m [MarkedExample]
markSuspects le = mapM (markSuspect le)

-- | Takes a SuspectExample and check's whether it matches the real function.
markSuspect :: Monad m => LanguageEnv m -> SuspectExample -> m MarkedExample
markSuspect (LanguageEnv { call = ca }) (Suspect ex) = do
    r <- ca $ exampleFuncCall ex
    if r == output ex
        then return $ MarkedCorrect ex
        else return $ MarkedIncorrect ex r

synthOrder :: H.Heap -> CallGraph -> [Id]
synthOrder h = filter (not . flip H.isPrimitive h . idName) . postOrderList

synthOrderAfter :: H.Heap -> [Id] -> CallGraph -> [Id]
synthOrderAfter h is =
    filter (not . flip H.isPrimitive h . idName) . postOrderListAfter is