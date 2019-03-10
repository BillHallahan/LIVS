module LIVS.Core.Fuzz ( fuzzExamplesM
                      , fuzzExampleM
                      , fuzzValM ) where

import LIVS.Language.Expr
import LIVS.Language.Syntax
import LIVS.Language.Typing
import LIVS.Target.General.LanguageEnv

import Control.Monad.Random

fuzzExamplesM :: MonadRandom m => 
                 LanguageEnv m
              -> Int -- ^ How many examples to fuzz
              -> Id -- ^ A function call
              -> m [Example] -- ^ A fuzzed input/output example
fuzzExamplesM le n i = do
    mapM (\_ -> fuzzExampleM (call le) i) [1..n]

fuzzExampleM :: MonadRandom m => 
                (Expr -> m Val) -- ^ Executes and returns the value of the given expression
             -> Id -- ^ A function call
             -> m Example -- ^ A fuzzed input/output example
fuzzExampleM ca i = do
    let ts = argTypes i
    ls <- mapM fuzzValM ts

    let outE = mkApp (Var i:map valToExpr ls)
    r <- ca outE 

    return Example { func = i
                   , input = ls
                   , output = r}

fuzzValM :: MonadRandom m => Type -> m Val
fuzzValM t
    | t == intType = return . LitVal . LInt =<< getRandomR (-100 * 100, 100 * 100)
    | otherwise = error "fuzz: We cannot fuzz values of the given type."