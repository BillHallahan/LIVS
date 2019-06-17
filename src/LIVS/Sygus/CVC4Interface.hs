module LIVS.Sygus.CVC4Interface ( CVC4
                                , runSygus
                                , runSygusWithGrammar
                                , runCVC4OnString
                                , runSMT2WithGrammar
                                , runCVC4WithFile

                                , getCVC4
                                , runAndReadCVC4
                                , closeCVC4) where

import LIVS.Config.Config
import LIVS.Language.CallGraph
import qualified LIVS.Language.Heap as H
import qualified LIVS.Language.SubFunctions as Sub
import LIVS.Language.Syntax
import LIVS.Language.Expr
import LIVS.Language.Monad.Naming
import LIVS.Sygus.Result
import LIVS.Sygus.SMTLexer
import LIVS.Sygus.SMTParser
import LIVS.Sygus.ToSygus
import LIVS.Sygus.TypeValueRules
import qualified LIVS.Language.TypeEnv as T
import LIVS.Language.Typing
import LIVS.Target.General.Process

import Control.Exception
import Control.Monad.IO.Class
import qualified Data.HashMap.Lazy as M
import qualified Data.HashSet as HS
import System.IO
import System.IO.Temp

runSygus :: (NameGenMonad m, MonadIO m) => LIVSConfigNames -> CallGraph -> [Val] -> H.Heap -> Sub.SubFunctions -> T.TypeEnv -> [Example] -> m (Result, Sub.SubFunctions)
runSygus con cg const_vals h sub tenv = runSygusWithGrammar con cg const_vals h sub tenv (HS.fromList $ H.keys h)

runSygusWithGrammar :: (NameGenMonad m, MonadIO m) => LIVSConfigNames -> CallGraph -> [Val] -> H.Heap -> Sub.SubFunctions -> T.TypeEnv -> HS.HashSet Name -> [Example] -> m (Result, Sub.SubFunctions)
runSygusWithGrammar con cg const_vals h sub tenv hsr es
    | es == [] = return $ (Sat M.empty, sub)
    | otherwise = do
        let n = (funcName (head es))
        n' <- freshNameM n

        let rules = typeValueRules es

        -- Type value rules are ignored when synthesizing from complex constraints, because input type to output
        -- correspondence no longer holds when examples are entire expressions (and not just inputs and outputs)
        let es_filtered = filterNotTypeValueRuleCovered rules es
        let tvr_funcs = generateTypeValueRulesFuncs rules
        let (es', ty_val_rules_funcs) = case (head es) of
                                            Constraint _ _ _ _ -> if (simpleConstraint (head es)) then (es_filtered, tvr_funcs) else (es, [])
                                            Example _ _ _ -> (es_filtered, tvr_funcs)
                                        where
                                            simpleConstraint e = (stripLeadingLams (expr e) == EmptyExpr)

        let es'' = map (\e -> e { func = Id n' (idType $ func (head es))}) es'
        ty_val_rules_funcs' <- mapM (\e -> do
                                        ty_val_n <- freshNameM n
                                        return (n, ty_val_n, e)) ty_val_rules_funcs

        let sub' = foldr (\(n_orig, n_new, e) -> Sub.insert n_orig (typeOf e) n_new) sub ty_val_rules_funcs'
            ty_val_rules_funcs'' = map (\(_, x, y) -> (x, y)) ty_val_rules_funcs'

        let es''' = simplifyExamples es''
        (es4, sub'') <- reassignFuncNames sub' n es'''

        let es5 = map (\(dcmdc, ess) -> (dcmdc, map (\e -> case e of
                                                            Constraint _ _ _ _ -> e { expr = (reassignConstraintNames (expr e) sub') }
                                                            Example _ _ _ -> e) ess)) es4

        res <- mapM (runSygusWithGrammar' con cg const_vals h sub tenv hsr) $ map snd es5
        let res' = foldr mergeRes (Sat M.empty) res
            res'' = foldr (uncurry insertSat) res' ty_val_rules_funcs''
        return (res'', sub'')

runSygusWithGrammar' :: (NameGenMonad m, MonadIO m) => LIVSConfigNames -> CallGraph -> [Val] -> H.Heap -> Sub.SubFunctions -> T.TypeEnv -> HS.HashSet Name -> [Example] -> m Result
runSygusWithGrammar' con cg const_vals h sub tenv hsr es
    | (_:_) <- es = do
        let form = toSygusWithGrammar cg const_vals h sub tenv hsr es
        liftIO $ whenLoud $ putStrLn form

        m <- liftIO $ runCVC4WithFile form ".sl" ["--lang", "sygus"] (smt_timeout con)
        return . parseSMT (H.map' typeOf h) tenv sub . lexSMT $ m
    | otherwise = do
        liftIO $ putStrLn "No examples!"
        return $ Sat M.empty

runCVC4OnString :: MonadIO m =>  Sub.SubFunctions -> T.TypeEnv -> String -> m Result
runCVC4OnString sub tenv s = do
    liftIO $ putStrLn s
    m <- liftIO $ runCVC4WithFile s ".sl" ["--lang", "sygus"] 10
    return . parseSMT (M.empty) tenv sub . lexSMT $ m

runSMT2WithGrammar :: MonadIO m => LIVSConfigNames -> H.Heap -> Sub.SubFunctions -> T.TypeEnv -> String -> m Result
runSMT2WithGrammar con h sub tenv s = do
    -- withSystemTempFile (and hence runCVC4WithFile) does not work if the extension
    -- has a number in it, so we write the SMT to a text file, and use --lang to tell
    -- CVC4 that it is SMTLIB
    m <- liftIO $ runCVC4WithFile s ".txt" ["--lang", "smt2.6", "--produce-model"] (smt_timeout con)
    return . parseSMT (H.map' typeOf h) tenv sub . lexSMT $ m

runCVC4WithFile :: String -- SyGuS
                -> String
                -> [String]
                -> Int
                -> IO String
runCVC4WithFile sygus ext ars timeout = do
    out <- try (
        withSystemTempFile ("cvc4_input" ++ ext)
        (\fp h -> do
            hPutStr h sygus
            -- We call hFlush to prevent hPutStr from buffering
            hFlush h

            runProcessOnce "gtimeout" (show timeout:"cvc4":fp:ars))
        ) :: IO (Either SomeException String)

    case out of
        Right out' -> return out'
        Left _ -> return "unknown"

newtype CVC4 = CVC4 Process

getCVC4 :: IO CVC4
getCVC4 = return . CVC4 =<< getProcess "cvc4" ["--lang", "sygus", "--produce-models"]

runAndReadCVC4 :: CVC4 -> String -> IO String
runAndReadCVC4 (CVC4 cvc4) = runAndReadProcess cvc4

closeCVC4 :: CVC4 -> IO ()
closeCVC4 (CVC4 cvc4) = closeProcess cvc4 "(exit)\n"
