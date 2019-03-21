module LIVS.Core.Fuzz ( fuzzExamplesM
                      , fuzzExampleM
                      , fuzzValM ) where

import LIVS.Language.Expr
import LIVS.Language.Syntax
import qualified LIVS.Language.TypeEnv as T
import LIVS.Language.Typing
import LIVS.Target.General.LanguageEnv

import Control.Monad.Random

fuzzExamplesM :: MonadRandom m => 
                 LanguageEnv m
              -> T.TypeEnv
              -> Int -- ^ How many examples to fuzz
              -> Id -- ^ A function call
              -> m [Example] -- ^ A fuzzed input/output example
fuzzExamplesM le tenv n i = do
    mapM (\_ -> fuzzExampleM (call le) tenv i) [1..n]

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
    return . take n =<< getRandoms

fromListConst :: MonadRandom m => [a] -> m a
fromListConst xs = fromList $ zip xs (repeat $ toRational (1 :: Integer))