{-# LANGUAGE BangPatterns #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE TupleSections #-}

module LIVS.Interpreter.Interpreter ( RunEnv
                                    , run
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

import Control.Monad.State.Lazy
import Data.Functor.Identity

import Debug.Trace

data Frame = ApplyFrame Expr
           | Bind Id Expr -- ^ An Id from a Let Binding, and the continuation

type RunEnv m = StackT Frame (HeapT (NameGenT m))

runEnv :: Monad m => H.Heap -> NameGen -> Stack Frame -> RunEnv m b -> m b
runEnv h ng s b = evalNameGenT (evalHeapT (evalStackT b s) h) ng

getEnv :: Monad m => m a -> RunEnv m a
getEnv a = lift . lift $ lift a

run :: Monad m => LanguageEnv m -> Int -> Expr ->  H.Heap -> NameGen -> m Expr
run le n e h ng = do
    let le' = liftLanguageEnv getEnv le
    runEnv h ng empty (runM le' n e)

runM :: (StackMonad Frame m, HeapMonad m, NameGenMonad m)
     => LanguageEnv m
     -> Int -- ^ Number of steps to take.
     -> Expr
     -> m Expr
runM le n e = do
    mapDefsMH constAppNF
    rep n (\e'' -> trace (show e'') runStepM le e'') =<< constAppNF e
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
runStepM _ dc@(Data _) = do
    frm <- popM
    case frm of
        Just (Bind i e) -> do
            insertDefH (idName i) dc
            return e
        Just (ApplyFrame _) -> error "runStepM: application to Lit"
        Nothing -> return dc

runStepM le v@(Var (Id n _)) = do
    r <- lookupH n

    case r of
        Just (H.Def e) -> return e
        Just (H.Primitive t) -> do
            let tn = length . argTypes $ PresType t
            ars <- popArgs tn
            case ars of
                Just ars' -> do
                    ars'' <- mapM redArgs ars'
                    let e = mkApp (v:ars'')
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

redArgs :: HeapMonad m => Expr -> m Expr
redArgs v@(Var (Id n _)) = do
    r <- lookupH n
    case r of
        Just (H.Def e) -> return e
        _ -> return v
redArgs (Lam i e) = return . Lam i =<< redArgs e
redArgs (App e1 e2) = do
    e1' <- redArgs e1
    e2' <- redArgs e2
    return (App e1' e2')
redArgs (Let (i, b) e) = do
    b' <- redArgs b
    e' <- redArgs e
    return (Let (i, b') e)
redArgs e = return e

-- | By rewriting with Let's, converts an Expr into a form such that all
-- function arguments are variables or literals
constAppNF :: NameGenMonad m => Expr -> m Expr
constAppNF v@(Var _) = return v
constAppNF dc@(Data _) = return dc
constAppNF l@(Lit _) = return l
constAppNF (Lam i e) = return . Lam i =<< constAppNF e
constAppNF e@(App _ _) = do
    let (a:as) = unApp e
    
    bnd_a <- mapM (\a' -> do
                        a'' <- constAppNF a'
                        i <- unseededFreshIdM (typeOf a')
                        return $ (i, a'')) as

    let e' = mkApp $ a:map (Var . fst) bnd_a
    return $ foldr Let e' bnd_a
constAppNF (Let (i, b) e) = do
    b' <- constAppNF b
    e' <- constAppNF e
    return $ Let (i, b') e'