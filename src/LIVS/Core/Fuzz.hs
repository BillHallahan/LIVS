{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE MultiParamTypeClasses #-}

module LIVS.Core.Fuzz ( Fuzz
                      , fuzzExamplesM
                      , fuzzExampleM
                      , fuzzValM

                      , fuzzFromValsAndOutputsM
                      , fuzzFromOutputsM ) where

import LIVS.Language.Expr
import LIVS.Language.Syntax
import qualified LIVS.Language.TypeEnv as T
import LIVS.Language.Typing
import LIVS.Target.General.LanguageEnv

import Control.Monad.Random
import qualified Data.List as L

import Debug.Trace

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
    | TyCon n _ <- t = do
        dc <- randomDC (fuzzValM tenv) tenv n
        case dc of
            Just dc' -> return dc'
            Nothing -> error "fuzz: We cannot fuzz values of the given type."
    | otherwise = error "fuzz: We cannot fuzz values of the given type."

randomString :: MonadRandom m => m String
randomString = do
    n <- getRandomR (0, 4)
    return . take n =<< getRandomRs ('a','z')

randomDC :: MonadRandom m => (Type -> m Val) ->  T.TypeEnv -> Name -> m (Maybe Val)
randomDC f tenv n
    | Just specs <- T.lookup n tenv = do
        sel@(T.SelectorDC _ nt) <- fromListConst $ T.selectors specs

        let dc = T.selectorDCToDC n sel

        let ts = map T.namedTypeType nt
        vs <- mapM f ts

        return . Just $ mkAppVal (DataVal dc:vs)
    | otherwise = return Nothing

fromListConst :: MonadRandom m => [a] -> m a
fromListConst xs = fromList $ zip xs (repeat $ toRational (1 :: Integer))

-- | Fuzzes, drawing random values from the existing values and examples when possible.
-- Fuzzes randomly when no value of the given type exists.
fuzzFromValsAndOutputsM :: MonadRandom m => [Val] -> Fuzz m b
fuzzFromValsAndOutputsM vs le b es tenv n i = do
    let vs' = L.nub (vs ++ concatMap subVals (concatMap exampleVals es))
    mapM (\_ -> fuzzFromOutputsM' (call le b) vs' tenv i) [1..n]

-- | Fuzzes, drawing random values from the existing examples when possible.
-- Fuzzes randomly when no value of the given type exists.
fuzzFromOutputsM :: MonadRandom m => Fuzz m b
fuzzFromOutputsM = fuzzFromValsAndOutputsM []

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
    | not $ null vs' = fromListConst vs'
    | TyCon n _ <- t = do
        dc <- randomDC (fuzzFromOutputVal vs tenv) tenv n
        case dc of
            Just dc' -> return dc'
            Nothing -> fuzzValM tenv t
    | otherwise = fuzzValM tenv t
    where
        vs' = filter (\v -> typeOf v == t) vs

fuzzStrings :: MonadRandom m => Val -> m Val
fuzzStrings (AppVal v1 v2) = do
    v1' <- fuzzStrings v1
    v2' <- fuzzStrings v2
    return $ AppVal v1' v2'
fuzzStrings (LitVal (LString s)) = do
    b <- getRandomR (0, length s)
    e <- getRandomR (b, length s)
    let s' = drop b $ take e s
    return $ LitVal (LString s')
fuzzStrings v = return v