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
                          , addCoreFuncs
                          , livsConfigT
                          , runLIVSConfigT
                          , runLIVSConfigM

                          , whenLoud ) where

import LIVS.Language.Syntax
import qualified LIVS.Language.Heap as H

import Control.Monad.IO.Class
import Control.Monad.Reader
import Data.Functor.Identity
import System.Console.CmdArgs

data LIVSConfig cf =
    LIVSConfig { code_file :: String
               , seed :: Maybe Int -- ^ The seed for the random number gerator
               , fuzz_num :: Int -- ^ The number of examples to fuzz
               , core_funcs :: [cf] -- ^ Functions that are always available in synthesis
               , smt_timeout :: Int -- ^ Timeout for the SMT Solver
               } deriving (Data, Typeable)

type LIVSConfigCL = LIVSConfig String
type LIVSConfigNames = LIVSConfig Name

livsConfig :: LIVSConfigCL
livsConfig =
    LIVSConfig {
          code_file = "" &= help "A code file, containing component functions." &= explicit &= name "code-file" &= typFile -- &= argPos 0
        , seed = Nothing &= help "A seed for the random number generator."
        , fuzz_num = 20 &= help "The number of examples to fuzz, per iteration." &= explicit &= name "fuzz-num"
        , core_funcs = coreFuncs &= help "A set of core functions, always available for use in synthesis." &= explicit &= name "core-funcs"
        , smt_timeout = 5 &= help "A timeout for the SMT solver, in seconds" &= explicit &= name "smt-timeout"
        } &= verbosity

toLIVSConfigNames :: H.Heap -> LIVSConfigCL -> LIVSConfigNames
toLIVSConfigNames h con@(LIVSConfig { core_funcs = cf }) =
    con { core_funcs = concatMap filterNames cf}
    where
        ns = H.keys h
        filterNames s = filter (\(Name _ n _) -> n == s) ns

coreFuncs :: [String]
coreFuncs = ["=", ">", "and", "or", "not", "+", "-", "*", "ite", "int.to.str", "str.len", "str.++", "str.substr", "str.replace", "str.indexof", "\"true\"", "\"false\"", "\"NaN\""]

addCoreFuncs :: LIVSConfig cf -> [cf] -> LIVSConfig cf
addCoreFuncs config@(LIVSConfig { core_funcs = cf }) xs = config { core_funcs = cf ++ xs}

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
