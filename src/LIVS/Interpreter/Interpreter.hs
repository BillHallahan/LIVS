{-# LANGUAGE BangPatterns #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TupleSections #-}

module LIVS.Interpreter.Interpreter ( RunEnv
                                    , Frame (..)
                                    , EvalPrimitive
                                    , run
                                    , runCollectingExamples
                                    , runM
                                    , runStepM
                                    , runCollectingExamplesM
                                    , runStepCollectingExamplesM
                                    , evalPrimitive ) where

import LIVS.Interpreter.EvalPrimitive
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

data Frame = ApplyFrame Expr
           | Bind Id Expr -- ^ An Id from a Let Binding, and the continuation
           | FuncCall Id [Expr] -- ^ Records a previous function call's name and input arguments.
                                -- Used to collect new potential input/output pairs
           deriving (Show, Read)

type RunEnv m = StackT Frame (HeapT (NameGenT m))

runEnv :: Monad m => H.Heap -> NameGen -> Stack Frame -> RunEnv m b -> m b
runEnv h ng s b = evalNameGenT (evalHeapT (evalStackT b s) h) ng

getEnv :: Monad m => m a -> RunEnv m a
getEnv a = lift . lift $ lift a

run :: Monad m => EvalPrimitive m -> Int -> H.Heap -> NameGen -> Expr ->  m Expr
run ep n h ng e = do
    -- let le' = liftLanguageEnv getEnv le
    let ep' = liftEvalPrimitive getEnv ep
    runEnv h ng empty (runM ep' n e)

runCollectingExamples :: Monad m => EvalPrimitive m -> Int -> H.Heap -> NameGen -> Expr -> m (Expr, [SuspectExample])
runCollectingExamples ep n h ng e = do
    -- let le' = liftLanguageEnv getEnv le
    let ep' = liftEvalPrimitive getEnv ep
    runEnv h ng empty (runCollectingExamplesM ep' n e)

runM :: (StackMonad Frame m, HeapMonad m, NameGenMonad m)
     => EvalPrimitive m
     -> Int -- ^ Number of steps to take.
     -> Expr
     -> m Expr
runM ep n e = do
    mapDefsMH constAppNF
    rep n (runStepM ep) =<< constAppNF e

runCollectingExamplesM :: (StackMonad Frame m, HeapMonad m, NameGenMonad m)
                       => EvalPrimitive m
                       -> Int -- ^ Number of steps to take.
                       -> Expr
                       -> m (Expr, [SuspectExample])
runCollectingExamplesM ep n e = do
    mapDefsMH constAppNF
    e' <- constAppNF e
    rep n (uncurry (runStepCollectingExamplesM ep)) (e', [])

rep :: Monad m => Int -> (a -> m a) -> a -> m a
rep !n' f a
    | n' <= 0 = return a
    | otherwise = rep (n' - 1) f =<< f a

runStepCollectingExamplesM :: (StackMonad Frame m, HeapMonad m) => EvalPrimitive m -> Expr -> [SuspectExample] -> m (Expr, [SuspectExample])
runStepCollectingExamplesM ep e@(App _ _) exs = do
    let (f:es) = unApp e

    -- If we are calling a function, record the function and the inputs on the stack
    case f of
        Var f' -> pushM $ FuncCall f' es
        _ -> return ()

    e' <- runStepM ep e
    return (e', exs)
runStepCollectingExamplesM ep e exs
    | isVal e = do
        frm <- peekM
        case frm of
            Just (FuncCall i es) -> do
                _ :: Maybe Frame <- popM
                ex <- genExample i es e
                return $ (e, Suspect ex:exs)
            _ -> do
                e' <- runStepM ep e
                return (e', exs)
runStepCollectingExamplesM ep e exs = do
    e' <- runStepM ep e
    return (e', exs)

genExample :: HeapMonad m => Id -> [Expr] -> Expr -> m Example
genExample i inp out = do
    inp' <- mapM redArgs inp
    out' <- redArgs out
    return $ Example { func = i
                     , input = map toVal inp'
                     , output = toVal out' }
    where
        toVal (Data dc) = DataVal dc
        toVal (Lit l) = LitVal l
        toVal _ = error "toVal: bad Expr"

runStepM :: (StackMonad Frame m, HeapMonad m) => EvalPrimitive m -> Expr -> m Expr
runStepM ep v@(Var (Id n _)) = do
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
                    ep e
                    -- return . valToExpr =<< call le e
                Nothing -> error "runStepM: insufficient arguments for primitive"
        Nothing -> return v
runStepM _ lam_e@(Lam i e) = do
    frm <- popM
    case frm of
        Just (ApplyFrame ae) -> do
            insertDefH (idName i) ae
            return e
        Just (Bind _ _) -> error "runStepM: bind to Lam"
        _ -> return lam_e
runStepM _ a@(App _ _) = do
    let (f:es) = unApp a    
    mapM_ (pushM . ApplyFrame) $ reverse es
    return f
runStepM _ (Let (i, e) e') = do
    pushM (Bind i e')
    return e
runStepM _ e = do -- We have a value
    frm <- popM
    case frm of
        Just (Bind i e') -> do
            insertDefH (idName i) e
            return e'
        Just (ApplyFrame _) -> error "runStepM: application to val"
        _ -> return e

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
    return (Let (i, b') e')
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