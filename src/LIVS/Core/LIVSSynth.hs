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
import LIVS.Language.Typing
import LIVS.Sygus.CVC4Interface
import LIVS.Target.General.LanguageEnv
import LIVS.Target.JavaScript.Interface

import Control.Monad.Random
import Data.List
import Data.Maybe

livsSynthCVC4 :: (MonadIO m, MonadRandom m)
         => LIVSConfigNames -> LanguageEnv m -> Fuzz m -> FilePath -> CallGraph -> H.Heap -> T.TypeEnv -> [Example] -> m H.Heap
livsSynthCVC4 con le fuzz fp cg = livsSynth con le (runSygusWithGrammar cg) fuzz fp cg

livsSynth :: MonadIO m
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

    -- Expand the call graph with the new id's
    let def_ids = allDefIds h'
        cg' = addVertsToCallGraph (zip is $ repeat def_ids) cg

    -- Synthesize based on the user provided examples
    let con' = con { core_funcs = filterNonPrimitives h' (core_funcs con)}

    h'' <- livs' con' le gen fuzzFake cg' exs tenv h' is

    -- Check that the synthesized functions work in the real language
    mapM_ (\i -> case H.lookup (idName i) h'' of
                    Just (H.Def e) -> do
                      liftIO . putStrLn $ toJavaScriptDef (idName i) e
                      def le i e
                    _ -> error "livsSynth: No definition found") is
    incor <- incorrectSuspects le $ map Suspect exs

    case incor of
        [] -> return h''
        _ -> error $ "livsSynth: Incorrect translation back to real language" 
  where
    -- We do not want to fuzz any inputs for the new synthesized function,
    -- since there is no way of getting new outputs
    fuzzFake _ _ _ _ _ = return []

allDefIds :: H.Heap -> [Id]
allDefIds = map (\(n, e) -> Id n (typeOf e)) . mapMaybe getDefPairs . H.toList
    where
        getDefPairs (n, H.Def e) = Just (n, e)
        getDefPairs _ = Nothing

-- | In general, we cannot convert SMT primitives back into the real language,
-- so we filter them out here.
filterNonPrimitives :: H.Heap -> [Name] ->[Name]
filterNonPrimitives h = filter (not . flip H.isPrimitive h)