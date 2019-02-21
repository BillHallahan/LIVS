module Lava.LIVS.Fuzz ( fuzzExamplesM
                      , fuzzExampleM
                      , fuzzLitM ) where

import Lava.Language.Expr
import Lava.Language.Syntax
import Lava.Language.Typing

import Control.Monad.Random

fuzzExamplesM :: ( MonadIO m
                 , MonadRandom m) => 
                 (Expr -> IO Lit) -- ^ Executes and returns the value of the given expression
              -> Id -- ^ A function call
              -> Int -- ^ How many examples to fuzz
              -> m [Example] -- ^ A fuzzed input/output example
fuzzExamplesM exec i n = mapM (\_ -> fuzzExampleM exec i) [0..n]

fuzzExampleM :: ( MonadIO m
                , MonadRandom m) => 
                (Expr -> IO Lit) -- ^ Executes and returns the value of the given expression
             -> Id -- ^ A function call
             -> m Example -- ^ A fuzzed input/output example
fuzzExampleM exec i@(Id n t) = do
    let ts = unTyFun t
    ls <- mapM fuzzLitM ts

    let outE = mkApp (Var i:map Lit ls)
    r <- liftIO $ exec outE 

    return Example { func_name = n
                   , input = ls
                   , output = r}

fuzzLitM :: MonadRandom m => Type -> m Lit
fuzzLitM t
    | t == intType = return . LInt =<< getRandom
    | otherwise = error "fuzz: We cannot fuzz values of the given type."