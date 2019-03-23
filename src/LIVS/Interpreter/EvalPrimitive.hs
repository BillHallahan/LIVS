{-# LANGUAGE RankNTypes #-}

module LIVS.Interpreter.EvalPrimitive ( EvalPrimitive
                                      , evalPrimitive
                                      , liftEvalPrimitive) where

import LIVS.Language.Syntax
import LIVS.Language.Typing
import LIVS.Sygus.CVC4Interface
import LIVS.Sygus.Result
import LIVS.Sygus.ToSygus

import Control.Monad.IO.Class
import qualified Data.HashMap.Lazy as HM

type EvalPrimitive m = Expr -> m Expr

evalPrimitive :: MonadIO m => Expr -> m Expr
evalPrimitive e = do
    let x = Name "x" Nothing

    let s = toSygusExpr e
        set_x = "(define-var x " ++ toSygusType (typeOf e) ++ ")\n" ++
                    "(assert (= x" ++ s ++ "))"
    m <- runCVC4OnString $ "(set-logic ALL_SUPPORTED)\n" ++ set_x

    case m of
        Sat m' -> case HM.lookup x m' of
                    Just r' -> return r'
                    Nothing -> error "evalPrimitive: No definition for x found."
        _ -> error "evalPrimitive: No definition for x found."

liftEvalPrimitive :: (forall a . m a -> m' a) -> EvalPrimitive m -> EvalPrimitive m'
liftEvalPrimitive f ep e = f $ ep e