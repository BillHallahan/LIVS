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
import LIVS.Target.General.LanguageEnv

import Control.Monad.Random
import Data.List

livsRepairCVC4 :: (NameGenMonad m, MonadIO m, MonadRandom m)
         => LIVSConfigNames -> LanguageEnv m b -> b -> Fuzz m b -> FilePath -> CallGraph -> [Val] -> H.Heap -> T.TypeEnv -> [Example] -> Int --m (H.Heap, [Id])
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
           -> [Example] -- ^ The examples to synthesize a new function from
           -> Int --m (H.Heap, [Id])
livsRepair con le b gen fuzz fp cg h tenv exs = 0
