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
import qualified LIVS.Language.SubFunctions as Sub
import LIVS.Language.Syntax
import qualified LIVS.Language.TypeEnv as T
import qualified Data.HashSet as S
import LIVS.Language.Typing
import LIVS.Language.Monad.Naming
import LIVS.Sygus.CVC4Interface
import LIVS.Target.General.LanguageEnv
import LIVS.Target.JavaScript.Interface

import Control.Monad.Random
import Data.List
import Data.Maybe

livsSynthCVC4 :: (NameGenMonad m, MonadIO m, MonadRandom m)
         => LIVSConfigNames -> LanguageEnv m b -> b -> Fuzz m b -> FilePath -> CallGraph -> Constants -> H.Heap -> T.TypeEnv -> [Example] -> m (H.Heap, [Id])
livsSynthCVC4 con le b fuzz fp cg consts =
  livsSynth con le b (runSygusWithGrammarWithIteFallBack con cg) (runSygusWithGrammar con cg) fuzz fp cg consts

livsSynth :: MonadIO m
          => LIVSConfigNames
          -> LanguageEnv m b
          -> b
          -> Gen m -- ^ Synthesize component functions
          -> Gen m -- ^ Synthesize the output function
          -> Fuzz m b
          -> FilePath
          -> CallGraph
          -> Constants
          -> H.Heap
          -> T.TypeEnv
          -> [Example] -- ^ The examples to synthesize a new function from
          -> m (H.Heap, [Id])
livsSynth con le b gen gen_out fuzz fp cg consts h tenv exs = do
    -- Get the component functions
    (h', sub, exs') <- livs con le b gen fuzz fp cg consts h tenv

    -- Get the Id's of the new functions we have to synthesize
    let is = nub $ map func exs

    -- Expand the call graph with the new id's
    let def_ids = filterNonPrimitives h' $ verts cg-- map (flip Id (TyCon (Name Ident "Unknown" Nothing) TYPE)) $ Sub.keys sub
        def_ids' = def_ids ++ mapMaybe (flip H.nameToId h') (T.constructorNames tenv ++ T.selectorNames tenv)
        cg' = addVertsToCallGraph (zip is $ repeat def_ids') cg

    -- Synthesize based on the user provided examples
    (h'', sub', _) <- livs' con le b (genNew is gen gen_out) (fuzzFake is fuzz) cg' consts (exs ++ exs') tenv h' sub is

    let is' = map (toId h'') . flip Sub.lookupAllNames sub' $ map idName is

    -- Check that the synthesized functions work in the real language
    mapM_ (\i -> case H.lookup (idName i) h'' of
                    Just (H.Def e) -> do
                      def le b i e
                    _ -> error "livsSynth: No definition found") is'
    incor <- incorrectSuspects le b $ map Suspect exs

    case incor of
        [] -> return (h'', is')
        _ -> error $ "livsSynth: Incorrect translation back to real language: " ++ concatMap (\i -> case H.lookup (idName i) h'' of
                                               Just (H.Def e) -> toJavaScriptDef S.empty (idName i) e
                                               _ -> error "livsSynth: No definition found") is'
  where

    toId heap n
      | Just e <- H.lookup n heap = Id n (typeOf e)
      | otherwise = error "toId: Name not in Heap"

-- We do not want to fuzz any inputs for the new synthesized function,
-- since there is no way of getting new outputs
fuzzFake :: Monad m => [Id] -> (Fuzz m b) -> Fuzz m b
fuzzFake is fuzz le b es tenv n i
    | i `elem` is = return []
    | otherwise = fuzz le b es tenv n i 

genNew :: Monad m
       => [Id]
       -> Gen m -- ^ Synthesize component functions
       -> Gen m -- ^ Synthesize the output function
       -> Gen m
genNew is gen gen_out cnsts h sub tenv hs es@(Example { func = i }:_)
  | i `elem` is = gen_out cnsts h sub tenv hs es
  | otherwise = gen cnsts h sub tenv hs es
genNew _ _ _ _ _ _ _ _ _ = error "genNew: No examples"

-- | In general, we cannot convert SMT primitives back into the real language,
-- so we filter them out here.
filterNonPrimitives :: H.Heap -> [Id] ->[Id]
filterNonPrimitives h = filter (not . flip H.isPrimitive h . idName)