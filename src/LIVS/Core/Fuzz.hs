module LIVS.Core.Fuzz ( fuzzExamplesM
                      , fuzzExampleM
                      , fuzzLitM ) where

import LIVS.Language.Expr
import LIVS.Language.Syntax
import LIVS.Language.Typing

import Control.Monad.Random

fuzzExamplesM :: ( MonadIO m
                 , MonadRandom m) => 
                 (Expr -> IO Lit) -- ^ Executes and returns the value of the given expression
              -> Id -- ^ A function call
              -> Int -- ^ How many examples to fuzz
              -> m [Example] -- ^ A fuzzed input/output example
fuzzExamplesM call i n = mapM (\_ -> fuzzExampleM call i) [1..n]

fuzzExampleM :: ( MonadIO m
                , MonadRandom m) => 
                (Expr -> IO Lit) -- ^ Executes and returns the value of the given expression
             -> Id -- ^ A function call
             -> m Example -- ^ A fuzzed input/output example
fuzzExampleM call i = do
    let ts = argTypes i
    ls <- mapM fuzzLitM ts

    let outE = mkApp (Var i:map Lit ls)
    r <- liftIO $ call outE 

    return Example { func = i
                   , input = ls
                   , output = r}

fuzzLitM :: MonadRandom m => Type -> m Lit
fuzzLitM t
    | t == intType = return . LInt =<< getRandomR (-20, 20)
    | otherwise = error "fuzz: We cannot fuzz values of the given type."