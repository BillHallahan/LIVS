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
import LIVS.Language.Typing
import LIVS.Language.Monad.Naming
import LIVS.Sygus.CVC4Interface
import LIVS.Target.General.LanguageEnv

import Control.Monad.Random
import Data.List

livsSynthCVC4 :: (NameGenMonad m, MonadIO m, MonadRandom m)
         => LIVSConfigNames -> LanguageEnv m b -> b -> Fuzz m b -> FilePath -> CallGraph -> [Val] -> H.Heap -> T.TypeEnv -> [Example] -> m (H.Heap, [Id])
livsSynthCVC4 con le b fuzz fp cg const_val = livsSynth con le b (runSygusWithGrammar con cg const_val) fuzz fp cg

livsSynth :: MonadIO m
          => LIVSConfigNames
          -> LanguageEnv m b
          -> b
          -> Gen m
          -> Fuzz m b
          -> FilePath
          -> CallGraph
          -> H.Heap
          -> T.TypeEnv
          -> [Example] -- ^ The examples to synthesize a new function from
          -> m (H.Heap, [Id])
livsSynth con le b gen fuzz fp cg h tenv exs = do
    -- Get the component functions
    (h', sub) <- livs con le b gen fuzz fp cg h tenv

    -- Get the Id's of the new functions we have to synthesize
    let is = nub $ map func exs

    -- Expand the call graph with the new id's
    let def_ids = filterNonPrimitives h' $ verts cg-- map (flip Id (TyCon (Name Ident "Unknown" Nothing) TYPE)) $ Sub.keys sub
        cg' = addVertsToCallGraph (zip is $ repeat def_ids) cg

    liftIO $ putStrLn $ "verts = " ++ show def_ids

    -- Synthesize based on the user provided examples
    let con' = con -- con { core_funcs = filterNonPrimitives h' (core_funcs con)}

    (h'', sub') <- livs' con' le b gen (fuzzFake is fuzz) cg' exs tenv h' sub is

    let is' = map (toId h'') . flip Sub.lookupAllNames sub' $ map idName is

    -- Check that the synthesized functions work in the real language
    mapM_ (\i -> case H.lookup (idName i) h'' of
                    Just (H.Def e) -> do
                      def le b i e
                    _ -> error "livsSynth: No definition found") is'
    incor <- incorrectSuspects le b $ map Suspect exs

    case incor of
        [] -> return (h'', is')
        _ -> error $ "livsSynth: Incorrect translation back to real language" 
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

-- | In general, we cannot convert SMT primitives back into the real language,
-- so we filter them out here.
filterNonPrimitives :: H.Heap -> [Id] ->[Id]
filterNonPrimitives h = filter (not . flip H.isPrimitive h . idName)