{-# LANGUAGE BangPatterns #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE TupleSections #-}

module LIVS.Interpreter.Interpreter ( run
                                    , runM
                                    , runStepM ) where

import LIVS.Interpreter.Stack
import LIVS.Language.Expr
import qualified LIVS.Language.Heap as H
import LIVS.Language.Naming
import LIVS.Language.Syntax
import LIVS.Language.Typing
import LIVS.Language.Monad.Heap
import LIVS.Language.Monad.Naming
import LIVS.Target.General.LanguageEnv

data Frame = ApplyFrame Expr
           | Bind Id Expr -- ^ An Id from a Let Binding, and the continuation

type Env m = StackT Frame (HeapT (NameGenT m))

run :: Monad m => LanguageEnv (Env m) -> Int -> Expr ->  H.Heap -> NameGen -> m Expr
run le n e h = evalNameGenT (evalHeapT (evalStackT (runM le n e) empty) h)

runM :: (StackMonad Frame m, HeapMonad m, NameGenMonad m)
     => LanguageEnv m
     -> Int -- ^ Number of steps to take.
     -> Expr
     -> m Expr
runM le n e = rep n (runStepM le) =<< constAppNF e
    where
        rep !n' f a
            | n' <= 0 = return a
            | otherwise = rep (n' - 1) f =<< f a

runStepM :: (StackMonad Frame m, HeapMonad m) => LanguageEnv m -> Expr -> m Expr
runStepM _ l@(Lit _) = do
    frm <- popM
    case frm of
        Just (Bind i e) -> do
            insertDefH (idName i) l
            return e
        Just (ApplyFrame _) -> error "runStepM: application to Lit"
        Nothing -> return l

runStepM le v@(Var (Id n _)) = do
    r <- lookupH n

    case r of
        Just (H.Def e) -> return e
        Just (H.Primitive t) -> do
            let tn = length . argTypes $ PresType t
            ars <- popArgs tn
            case ars of
                Just ars' -> do
                    let e = mkApp (v:ars')
                    return . valToExpr =<< call le e
                Nothing -> error "runStepM: insufficient arguments for primitive"
        Nothing -> return v
runStepM _ le@(Lam i e) = do
    frm <- popM
    case frm of
        Just (ApplyFrame ae) -> do
            insertDefH (idName i) ae
            return e
        Just (Bind _ _) -> error "runStepM: bind to Lam"
        Nothing -> return le
runStepM _ (App e e') = do
    pushM (ApplyFrame e')
    return e
runStepM _ (Let (i, e) e') = do
    pushM (Bind i e')
    return e

popArgs :: StackMonad Frame m => Int -> m (Maybe [Expr])
popArgs !n
    | n <= 0 = return $ Just []
    | otherwise = do
        frm <- popM
        case frm of
            Just (ApplyFrame e) -> do
                ars <- popArgs (n - 1)
                case ars of
                    Just ars' -> return . Just $ e:ars'
                    Nothing -> return Nothing
            _ -> return Nothing

-- | By rewriting with Let's, converts an Expr into a form such that all
-- function arguments are variables or literals
constAppNF :: NameGenMonad m => Expr -> m Expr
constAppNF v@(Var _) = return v
constAppNF dc@(Data _) = return dc
constAppNF l@(Lit _) = return l
constAppNF (Lam i e) = return . Lam i =<< constAppNF e
constAppNF e@(App _ _) = do
    let (a:as) = unApp e
    
    bnd_a <- mapM (\a' -> return . (,a') =<< unseededFreshIdM (typeOf a')) as

    let e' = mkApp $ a:map (Var . fst) bnd_a
    return $ foldr Let e' bnd_a
constAppNF (Let (i, b) e) = do
    b' <- constAppNF b
    e' <- constAppNF e
    return $ Let (i, b') e'