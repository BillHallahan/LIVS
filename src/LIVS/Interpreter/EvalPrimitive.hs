{-# LANGUAGE RankNTypes #-}

module LIVS.Interpreter.EvalPrimitive ( EvalPrimitive
                                      , evalPrimitive
                                      , liftEvalPrimitive) where

import LIVS.Config.Config
import qualified LIVS.Language.Heap as H
import LIVS.Language.Syntax
import qualified LIVS.Language.TypeEnv as T
import LIVS.Language.Typing
import LIVS.Sygus.CVC4Interface
import LIVS.Sygus.Result
import LIVS.Sygus.ToSygus

import Control.Monad.IO.Class
import qualified Data.HashMap.Lazy as HM

type EvalPrimitive m = Expr -> m Expr

evalPrimitive :: MonadIO m => LIVSConfigNames -> H.Heap -> T.TypeEnv -> Expr -> m Expr
evalPrimitive con h tenv e = do
    let tspec = toSygusTypeEnv tenv

    let x = Name Ident "x" Nothing

    let s = toSygusExpr e
        set_x = tspec ++ "\n(declare-fun x () " ++ toSygusType (typeOf e) ++ ")\n" ++
                    "(assert (= x " ++ s ++ "))"

    m <- runSMT2WithGrammar con h tenv $ "(set-logic ALL_SUPPORTED)\n" ++ set_x ++ "\n(check-sat)\n(get-value (x))"

    case m of
        Sat m' -> case HM.lookup x m' of
                    Just r' -> return r'
                    Nothing -> error "evalPrimitive: No definition for x found."
        _ -> error "evalPrimitive: No definition for x found."

liftEvalPrimitive :: (forall a . m a -> m' a) -> EvalPrimitive m -> EvalPrimitive m'
liftEvalPrimitive f ep e = f $ ep e