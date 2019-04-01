module LIVS.Sygus.CVC4Interface ( CVC4
                                , runSygus
                                , runSygusWithGrammar
                                , runCVC4OnString
                                , runSMT2WithGrammar
                                , runCVC4WithFile

                                , getCVC4
                                , runAndReadCVC4
                                , closeCVC4) where

import LIVS.Language.CallGraph
import qualified LIVS.Language.Heap as H
import LIVS.Language.Syntax
import LIVS.Language.Monad.Naming
import LIVS.Sygus.Result
import LIVS.Sygus.SMTLexer
import LIVS.Sygus.SMTParser
import LIVS.Sygus.ToSygus
import LIVS.Sygus.TypeValueRules
import qualified LIVS.Language.TypeEnv as T
import LIVS.Language.Typing
import LIVS.Target.General.Process

import Control.Monad.IO.Class
import qualified Data.HashMap.Lazy as M
import qualified Data.HashSet as HS
import System.IO
import System.IO.Temp

runSygus :: (NameGenMonad m, MonadIO m) => CallGraph -> [Val] -> H.Heap -> T.TypeEnv -> [Example] -> m Result
runSygus cg const_vals h tenv = runSygusWithGrammar cg const_vals h tenv (HS.fromList $ H.keys h)

runSygusWithGrammar :: (NameGenMonad m, MonadIO m) => CallGraph -> [Val] -> H.Heap -> T.TypeEnv -> HS.HashSet Name -> [Example] -> m Result
runSygusWithGrammar cg const_vals h tenv hsr es
    | (Example { func = Id n t }:_) <- es = do
        n' <- freshNameM n

        let rules = typeValueRules es
            es' = filterNotRuleCovered rules es
            es'' = map (\e -> e { func = Id n' t}) es' 

            rules_func = generateRulesFunc (Id n' t) rules

        let form = toSygusWithGrammar cg const_vals h tenv hsr es''
        liftIO $ putStrLn form

        m <- liftIO $ runCVC4WithFile form ".sl" ["--lang", "sygus", "--tlimit", "10000"]
        return . insertSat n rules_func . parseSMT (H.map' typeOf h) tenv . lexSMT $ m
    | otherwise = return $ Sat M.empty

runCVC4OnString :: MonadIO m => T.TypeEnv -> String -> m Result
runCVC4OnString tenv s = do
    liftIO $ putStrLn s
    m <- liftIO $ runCVC4WithFile s ".sl" ["--lang", "sygus", "--tlimit", "10000"]
    liftIO $ print m
    return . parseSMT (M.empty) tenv . lexSMT $ m

runSMT2WithGrammar :: MonadIO m => H.Heap -> T.TypeEnv -> String -> m Result
runSMT2WithGrammar h tenv s = do
    -- withSystemTempFile (and hence runCVC4WithFile) does not work if the extension
    -- has a number in it, so we write the SMT to a text file, and use --lang to tell
    -- CVC4 that it is SMTLIB
    m <- liftIO $ runCVC4WithFile s ".txt" ["--lang", "smt2.6", "--tlimit", "10000", "--produce-model"]
    return . parseSMT (H.map' typeOf h) tenv . lexSMT $ m

runCVC4WithFile :: String -- SyGuS
                -> String
                -> [String]
                -> IO String
runCVC4WithFile sygus ext ars = do
    withSystemTempFile ("cvc4_input" ++ ext)
        (\fp h -> do
            hPutStr h sygus
            -- We call hFlush to prevent hPutStr from buffering
            hFlush h

            runProcessOnce "cvc4" (fp:ars))

newtype CVC4 = CVC4 Process

getCVC4 :: IO CVC4
getCVC4 = return . CVC4 =<< getProcess "cvc4" ["--lang", "sygus", "--produce-models"]

runAndReadCVC4 :: CVC4 -> String -> IO String
runAndReadCVC4 (CVC4 cvc4) = runAndReadProcess cvc4

closeCVC4 :: CVC4 -> IO ()
closeCVC4 (CVC4 cvc4) = closeProcess cvc4 "(exit)\n"