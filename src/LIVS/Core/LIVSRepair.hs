-- | LIVS to repair functions.
-- Unlike the general LIVS algorithm, modifies existing functions and tries to
-- preserve their properties using fault localization
module LIVS.Core.LIVSRepair ( livsRepairCVC4 ) where

import LIVS.Config.Config
import LIVS.Core.Fuzz
import LIVS.Core.LIVS
import LIVS.Core.LIVSSynth
import LIVS.Language.CallGraph
import qualified LIVS.Language.Heap as H
import qualified LIVS.Language.SubFunctions as Sub
import LIVS.Language.Syntax
import qualified LIVS.Language.TypeEnv as T
import LIVS.Language.Typing
import LIVS.Language.Monad.Naming
import LIVS.Sygus.CVC4Interface
import LIVS.Sygus.Result
import LIVS.Target.General.LanguageEnv

import Control.Monad.Random
import qualified Data.HashSet as S
import Data.List

livsRepairCVC4 :: (NameGenMonad m, MonadIO m, MonadRandom m)
         => LIVSConfigNames -> LanguageEnv m b -> b -> Fuzz m b -> FilePath -> CallGraph -> [Val] -> H.Heap -> T.TypeEnv -> [Example] -> m (H.Heap, [Id])
livsRepairCVC4 con le b fuzz fp cg const_val = livsRepair con le b (runSygusWithGrammar con cg const_val) fuzz fp cg

livsRepair :: MonadIO m
           => LIVSConfigNames
           -> LanguageEnv m b
           -> b
           -> Gen m
           -> Fuzz m b
           -> FilePath
           -> CallGraph
           -> H.Heap
           -> T.TypeEnv
           -> [Example]
           -> m (H.Heap, [Id])
livsRepair con le b gen fuzz fp cg h tenv exs = do

    -- TODO: should also take an argument for WHICH function to resynth, since there might be pbe examples for multiple
    -- TODO: Get structural constraints from functions which have a path to the repair function, and add them to the list
    -- of examples

    -- Get the Id of the function to repair
    let is = nub $ map func exs

    -- Modify call graph so that it only includes the functions for which there is no path to the repair function
    -- (also exclude the repair function itself)
    let cg' = ( \g@(CallGraph _ _ _ ve) i -> createCallGraph [x | x <- ve, not $ (==) (fst x) i || path g (fst x) i] ) cg (head is)

    -- Get definitions for usable component functions
    (h', sub, exs') <- livs con le b gen fuzz fp cg' h tenv
    let exs'' = examplesForFunc (idName (head is)) (exs ++ exs')

    -- TODO: make an Example into an expression and create a simple interface to its old behavior
    -- TODO: formalize the concept of a typed "anonymous function" by looking at how the hell the
    -- call chain figures out what we're synthing, and how to get types in an expr
    -- TODO: modify cvc4 interface to follow the algorithm I wrote on the board
    -- TODO: modify livsRepair' and component functions to accept the anon fxn with type to synthesize

    -- TODO: make the below an iterative DFS over Expr in target fxn's heapObj.
    -- TODO: fill in the TODOs below

    -- Expand the call graph with the new Id TODO: does this need to be here? Will it mess things up?
    let def_ids = filterNonPrimitives h' $ verts cg'
        cg'' = addVertsToCallGraph (zip is $ repeat def_ids) cg'

    -- TODO: Create constraints from examples (exs'') plus our current location. Need to get location, infer type, tree
    -- shenanigans, make new Id, etc.

    -- Synthesize new expression TODO: pass constraints not examples
    (h'', is') <- livsRepair' con gen cg'' sub h' tenv exs'' is

    -- TODO: Check that synth was successful, if not, stop searching this branch

    -- TODO: Replace anonymized piece of target function with new expression

    -- Check that new version of the function works in the real langauge
    mapM_ (\i -> case H.lookup (idName i) h'' of
                    Just (H.Def e) -> do
                      def le b i e
                    _ -> error "livsSynth: No definition found") is'
    incor <- incorrectSuspects le b $ map Suspect exs
    case incor of
        [] -> return ()
        _ -> error $ "livsSynth: Incorrect translation back to real language"

    -- TODO: Score the new version against the old version, and save it as the max if it's better than our current max

    -- Return the highest scoring heap
    return (h'', is')

livsRepair' :: MonadIO m
            => LIVSConfigNames
            -> Gen m
            -> CallGraph
            -> Sub.SubFunctions
            -> H.Heap
            -> T.TypeEnv
            -> [Example]
            -> [Id]
            -> m (H.Heap, [Id])
livsRepair' con gen cg sub h tenv exs is = do

    liftIO $ whenLoud (putStrLn $ "Synthesizing expression " ++ show (head is))

    -- Relative heap
    let relH = H.filterWithKey (\n' _ -> idName (head is) /= n') $ filterToReachable con (head is) cg h

    -- What is a gram lol
    let gram = S.fromList $ flip Sub.lookupAllNamesDefSingleton sub $ map idName $ directlyCalls (head is) cg

    -- Take a guess at the definition of the function
    (m, sub') <- gen relH sub tenv gram exs
    case m of
        Sat m' -> do
            liftIO $ whenLoud (putStrLn $ "Synthesized expression " ++ show (head is))
            let h' = H.union (H.fromExprHashMap m') h
                is' = map (toId h') . flip Sub.lookupAllNames sub' $ map idName is
            return (h', is')

        _ -> do
            return (h, [])

    where
        toId heap n
            | Just e <- H.lookup n heap = Id n (typeOf e)
            | otherwise = error "toId: Name not in Heap"
