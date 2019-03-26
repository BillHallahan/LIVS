-- | LIVS to synthesize functions.
-- Unlike the general LIVS algorithm, guarantees that the translation back to
-- the host language also satisfies the input/output counterexamples.
module LIVS.Core.LIVSSynth ( livsSynthCVC4
                           , livsSynth ) where

import LIVS.Config.Config
import LIVS.Core.Fuzz
import LIVS.Core.LIVS
import LIVS.Language.CallGraph
import qualified LIVS.Language.Heap as H
import LIVS.Language.Syntax
import qualified LIVS.Language.TypeEnv as T
import LIVS.Sygus.CVC4Interface
import LIVS.Target.General.LanguageEnv

import Control.Monad.Random
import Data.List

livsSynthCVC4 :: (MonadIO m, MonadRandom m)
         => LIVSConfigNames -> LanguageEnv m -> FilePath -> CallGraph -> H.Heap -> T.TypeEnv -> [Example] -> m H.Heap
livsSynthCVC4 con le fp cg = livsSynth con le (runSygusWithGrammar cg) fuzzExamplesM fp cg

livsSynth :: (MonadIO m, MonadRandom m)
          => LIVSConfigNames
          -> LanguageEnv m
          -> Gen m
          -> Fuzz m
          -> FilePath
          -> CallGraph
          -> H.Heap
          -> T.TypeEnv
          -> [Example] -- ^ The examples to synthesize a new function from
          -> m H.Heap
livsSynth con le gen fuzz fp cg h tenv exs = do
    -- Get the component functions
    h' <- livs con le gen fuzz fp cg h tenv

    -- Get the Id's of the new functions we have to synthesize
    let is = nub $ map func exs

    -- Synthesize based on the user provided examples
    h'' <- livs' con le gen fuzz cg exs tenv h' is

    -- Check that the synthesized functions work in the real language
    mapM_ (\i -> case H.lookup (idName i) h'' of
                    Just (H.Def e) -> def le i e
                    _ -> error "livsSynth: No definition found") is
    incor <- incorrectSuspects le $ map Suspect exs

    case incor of
        [] -> return h''
        _ -> error $ "livsSynth: Incorrect translation back to real language" 