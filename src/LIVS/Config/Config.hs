{-# LANGUAGE DeriveDataTypeable #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# OPTIONS_GHC -fno-cse #-}

module LIVS.Config.Config ( LIVSConfig (..)
                          , LIVSConfigCL
                          , LIVSConfigNames
                          , LIVSConfigMonad (..)
                          , LIVSConfigT
                          , LIVSConfigM

                          , livsConfig
                          , toLIVSConfigNames
                          , livsConfigT
                          , runLIVSConfigT
                          , runLIVSConfigM

                          , whenLoud ) where

import LIVS.Language.Syntax
import qualified LIVS.Language.Heap as H

import Control.Monad.IO.Class
import Control.Monad.Reader
import Data.Functor.Identity
import Data.List
import Data.Maybe
import System.Console.CmdArgs
import System.Console.CmdArgs.Verbosity

data LIVSConfig cf =
    LIVSConfig { code_file :: String
               , fuzz_num :: Int -- ^ The number of examples to fuzz
               , core_funcs :: [cf] -- ^ Functions that are always available in synthesis
               } deriving (Data, Typeable)

type LIVSConfigCL = LIVSConfig String
type LIVSConfigNames = LIVSConfig Name

livsConfig :: LIVSConfigCL
livsConfig =
    LIVSConfig {
          code_file = "" &= help "A code file, containing component functions." &= explicit &= name "code-file" &= typFile -- &= argPos 0
        , fuzz_num = 3 &= help "The number of examples to fuzz, per iteration." &= explicit &= name "fuzz-name"
        , core_funcs = coreFuncs &= help "A set of core functions, always available for use in synthesis." &= explicit &= name "core-funcs"
        } &= verbosity

toLIVSConfigNames :: H.Heap -> LIVSConfigCL -> LIVSConfigNames
toLIVSConfigNames h con@(LIVSConfig { core_funcs = cf }) =
    con { core_funcs = mapMaybe findName cf}
    where
        ns = H.keys h
        findName s = find (\(Name n _) -> n == s) ns

coreFuncs :: [String]
coreFuncs = ["=", "+", "*", "ite", "int.to.str", "str.++"]

class Monad m => LIVSConfigMonad m cf where
    askConfig :: m (LIVSConfig cf)

newtype LIVSConfigT cf m a = LIVSConfigT { configReaderT :: ReaderT (LIVSConfig cf) m a }
                          deriving (Applicative, Functor, Monad)

type LIVSConfigM cf a = LIVSConfigT cf Identity a

instance MonadTrans (LIVSConfigT cf) where
    lift = LIVSConfigT . lift

instance Monad m => MonadReader (LIVSConfig cf) (LIVSConfigT cf m) where
    ask = LIVSConfigT ask
    local f = LIVSConfigT . local f . configReaderT

instance Monad m => LIVSConfigMonad (LIVSConfigT cf m) cf where
    askConfig = ask

instance MonadIO m => MonadIO (LIVSConfigT cf m) where
    liftIO = LIVSConfigT . liftIO

livsConfigT :: (LIVSConfig cf -> m a) -> LIVSConfigT cf m a
livsConfigT = LIVSConfigT . ReaderT

runLIVSConfigT :: LIVSConfigT cf m a -> LIVSConfig cf -> m a
runLIVSConfigT (LIVSConfigT lc) = runReaderT lc

runLIVSConfigM :: LIVSConfigM cf a -> LIVSConfig cf -> a
runLIVSConfigM lc = runIdentity . runLIVSConfigT lc