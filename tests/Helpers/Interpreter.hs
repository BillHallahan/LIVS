module Helpers.Interpreter ( langEnv
                           , langEnvInterpFallBack
                           , callPrimExprM
                           , callPrimExpr
                           , callPrim
                           , callPrimInterpFallBackExprM
                           , callPrimInterpFallBackExpr
                           , callPrimInterpFallBack ) where

import LIVS.Interpreter.Interpreter
import LIVS.Interpreter.Stack
import LIVS.Language.Expr
import qualified LIVS.Language.Heap as H
import LIVS.Language.Naming
import LIVS.Language.Syntax
import LIVS.Language.Monad.Heap
import LIVS.Language.Monad.Naming
import LIVS.Target.General.LanguageEnv

langEnv :: Monad m => H.Heap -> LanguageEnv m ()
langEnv h = LanguageEnv { load = const $ return ()
                        , def = const . const . const $ return ()
                        , call = \_ e -> return . fst $ runHeapM (callPrim e) h
                        }

langEnvInterpFallBack :: Monad m => H.Heap -> LanguageEnv m ()
langEnvInterpFallBack h = LanguageEnv { load = const $ return ()
                                      , def = const . const . const $ return ()
                                      , call = \_ e -> return . fst
                                            $ runHeapM (callPrimInterpFallBack e) h
                                      }

callPrimInterpFallBackExprM :: Monad m => H.Heap -> Expr -> m Expr
callPrimInterpFallBackExprM h e = return $ evalHeapM (callPrimInterpFallBackExpr e) h

callPrimInterpFallBackExpr :: HeapMonad m => Expr -> m Expr
callPrimInterpFallBackExpr e = return . valToExpr =<< callPrimInterpFallBack e

callPrimExprM :: Monad m => H.Heap -> Expr -> m Expr
callPrimExprM h e = return $ evalHeapM (callPrimExpr e) h

callPrimExpr :: HeapMonad m => Expr -> m Expr
callPrimExpr e = return . valToExpr =<< callPrim e

callPrim :: HeapMonad m => Expr -> m Val
callPrim e = do
    r <- callPrim' e
    case r of
        Just r' -> return r'
        Nothing -> error "callPrim: Bad Expr"

callPrim' :: HeapMonad m => Expr -> m (Maybe Val)
callPrim' (App (App (App (Var (Id (Name _ "ite" _) _)) b) e) e') =
    case b of
        Data (DC (Name _ "true" _) _) ->
            reduceToVal e
        Data (DC (Name _ "false" _) _) ->
            reduceToVal e'
        _ -> error $ "callPrim': Unhandled expression from ite" ++ show b ++ "\n" ++ show e ++ "\n" ++ show e'
callPrim' (App (App (Var (Id (Name _ ">=" _) _)) (Lit (LInt l))) (Lit (LInt l')))
    | l >= l' =
        return . Just . DataVal $ trueDC
    | otherwise =
        return . Just . DataVal $ falseDC
callPrim' (App (App (Var (Id (Name _ "-" _) _)) (Lit (LInt l))) (Lit (LInt l'))) =
    return . Just . LitVal $ LInt (l - l')
callPrim' _ = return Nothing

-- | Runs callPrim, but falls back on running the intepreter if needed.
callPrimInterpFallBack :: HeapMonad m => Expr -> m Val
callPrimInterpFallBack e = do
    r <- callPrim' e
    case r of
        Just r' -> return r'
        Nothing -> do
            h <- getHeap
            e' <- runEnvTest (mkNameGen []) empty (runM (\e' -> return . fst $ runHeapM (callPrimExpr e') h) 1000 e)
            case exprToVal e' of
                Just v -> return v
                Nothing -> error "callPrimInterpFallBack: Did not reduce to Val"

type RunEnvTest m = StackT Frame (NameGenT m)

runEnvTest :: HeapMonad m => NameGen -> Stack Frame -> RunEnvTest m b -> m b
runEnvTest ng s b = evalNameGenT (evalStackT b s) ng

reduceToVal :: HeapMonad m => Expr -> m (Maybe Val)
reduceToVal (Var (Id n _)) = do
    e <- lookupH n
    case e of
        Just (H.Def e') -> reduceToVal e'
        _ -> error "reduceToVal: bad expr"
reduceToVal (Lit l) = return . Just $ LitVal l
reduceToVal (Data dc) = return . Just $ DataVal dc
reduceToVal _ = return Nothing