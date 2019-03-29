{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE MultiParamTypeClasses #-}

module LIVS.Core.Fuzz ( Fuzz
                      , fuzzExamplesM
                      , fuzzExampleM
                      , fuzzValM

                      , fuzzFromOutputsM ) where

import LIVS.Language.Expr
import LIVS.Language.Syntax
import qualified LIVS.Language.TypeEnv as T
import LIVS.Language.Typing
import LIVS.Target.General.LanguageEnv

import Control.Monad.Random
import qualified Data.List as L

-- | Generates inputs to a function
type Fuzz m b = LanguageEnv m b
             -> b
             -> [Example] -- ^ The existing examples
             -> T.TypeEnv
             -> Int -- ^ How many examples to fuzz
             -> Id -- ^ A function call
             -> m [Example]

-- | Fuzz examples randomly
fuzzExamplesM :: MonadRandom m => Fuzz m b
fuzzExamplesM le b _ tenv n i = do
    mapM (\_ -> fuzzExampleM (call le b) tenv i) [1..n]

fuzzExampleM :: MonadRandom m => 
                (Expr -> m Val) -- ^ Executes and returns the value of the given expression
             -> T.TypeEnv
             -> Id -- ^ A function call
             -> m Example -- ^ A fuzzed input/output example
fuzzExampleM ca tenv i = do
    let ts = argTypes i
    ls <- mapM (fuzzValM tenv) ts

    let outE = mkApp (Var i:map valToExpr ls)
    r <- ca outE 

    return Example { func = i
                   , input = ls
                   , output = r}

fuzzValM :: MonadRandom m => T.TypeEnv -> Type -> m Val
fuzzValM tenv t
    | t == intType = return . LitVal . LInt =<< getRandomR (-100 * 100, 100 * 100)
    | t == stringType = return . LitVal . LString =<< randomString
    | t == boolType = fromListConst [DataVal trueDC, DataVal falseDC]
    | TyCon n _ <- t
    , Just specs <- T.lookup n tenv = do
        sel@(T.SelectorDC _ nt) <- fromListConst $ T.selectors specs

        let dc = T.selectorDCToDC n sel

        let ts = map T.namedTypeType nt
        vs <- mapM (fuzzValM tenv) ts

        return $ mkAppVal (DataVal dc:vs)
    | otherwise = error "fuzz: We cannot fuzz values of the given type."

randomString :: MonadRandom m => m String
randomString = do
    n <- getRandomR (0, 4)
    return . take n =<< getRandomRs ('a','z')

fromListConst :: MonadRandom m => [a] -> m a
fromListConst xs = fromList $ zip xs (repeat $ toRational (1 :: Integer))

-- | Fuzzes, drawing random values from the existing examples when possible.
-- Fuzzes randomly when no value of the given type exists.
fuzzFromOutputsM :: MonadRandom m => Fuzz m b
fuzzFromOutputsM le b es tenv n i = do
    let vs = L.nub $ concatMap exampleVals es
    mapM (\_ -> fuzzFromOutputsM' (call le b) vs tenv i) [1..n]

fuzzFromOutputsM' :: MonadRandom m => 
                     (Expr -> m Val)
                  -> [Val]
                  -> T.TypeEnv
                  -> Id
                  -> m Example
fuzzFromOutputsM' ca vs tenv i = do
    let ts = argTypes i
    ls <- mapM (fuzzFromOutputVal vs tenv) ts
    
    let outE = mkApp (Var i:map valToExpr ls)
    r <- ca outE 

    return Example { func = i
                   , input = ls
                   , output = r}

fuzzFromOutputVal :: MonadRandom m => [Val] -> T.TypeEnv -> Type -> m Val
fuzzFromOutputVal vs tenv t
    | vs'@(_:_) <- filter (\v -> typeOf v == t) vs = fromListConst vs'
    | otherwise = fuzzValM tenv t