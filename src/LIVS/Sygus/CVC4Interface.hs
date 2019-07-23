module LIVS.Sygus.CVC4Interface ( CVC4
                                , runSygusWithIteFallback
                                , runSygusWithFallback
                                , runSygus
                                , runSygusWithGrammar
                                , runSygusWithGrammarWithIteFallBack
                                , runSygusWithGrammarWithFallBack
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
import LIVS.Sygus.ExamplesToIte
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

runSygusWithIteFallback :: (NameGenMonad m, MonadIO m) => LIVSConfigNames -> CallGraph -> [Val] -> H.Heap -> Sub.SubFunctions -> T.TypeEnv -> [Example] -> m (Result, Sub.SubFunctions)
runSygusWithIteFallback con cg const_vals h sub tenv es =
    runSygusWithFallback con cg const_vals h sub tenv es examplesToIteResult

runSygusWithFallback :: (NameGenMonad m, MonadIO m) =>
                        LIVSConfigNames
                     -> CallGraph
                     -> [Val]
                     -> H.Heap
                     -> Sub.SubFunctions
                     -> T.TypeEnv
                     -> [Example]
                     -> ([Example] -> Result)
                     -> m (Result, Sub.SubFunctions)
runSygusWithFallback con cg const_vals h sub tenv =
    runSygusWithGrammarWithFallBack con cg const_vals h sub tenv (HS.fromList $ H.keys h)

runSygus :: (NameGenMonad m, MonadIO m) => LIVSConfigNames -> CallGraph -> [Val] -> H.Heap -> Sub.SubFunctions -> T.TypeEnv -> [Example] -> m (Result, Sub.SubFunctions)
runSygus con cg const_vals h sub tenv = runSygusWithGrammar con cg const_vals h sub tenv (HS.fromList $ H.keys h)

runSygusWithGrammarWithIteFallBack :: (NameGenMonad m, MonadIO m) =>
                                      LIVSConfigNames
                                   -> CallGraph
                                   -> [Val]
                                   -> H.Heap
                                   -> Sub.SubFunctions
                                   -> T.TypeEnv
                                   -> HS.HashSet Name
                                   -> [Example]
                                   -> m (Result, Sub.SubFunctions)
runSygusWithGrammarWithIteFallBack con cg const_vals h sub tenv hsr es =
    runSygusWithGrammarWithFallBack con cg const_vals h sub tenv hsr es examplesToIteResult

runSygusWithGrammarWithFallBack :: (NameGenMonad m, MonadIO m) =>
                                   LIVSConfigNames
                                -> CallGraph
                                -> [Val]
                                -> H.Heap
                                -> Sub.SubFunctions
                                -> T.TypeEnv
                                -> HS.HashSet Name
                                -> [Example]
                                -> ([Example] -> Result)
                                -> m (Result, Sub.SubFunctions)
runSygusWithGrammarWithFallBack con cg const_vals h sub tenv hsr es fallback
    | (_:_) <- es = do
        (es5, ty_val_rules_funcs'', sub'') <- simplifyRules sub es

        res <- mapM (runSygusWithGrammarWithFallBack' con cg const_vals h sub tenv hsr fallback) es5
        let res' = foldr mergeRes (Sat M.empty) res
            res'' = foldr (uncurry insertSat) res' ty_val_rules_funcs''
        return (res'', sub'')
    | otherwise = return $ (Sat M.empty, sub)

runSygusWithGrammarWithFallBack' :: (NameGenMonad m, MonadIO m) =>
                                    LIVSConfigNames
                                 -> CallGraph
                                 -> [Val]
                                 -> H.Heap
                                 -> Sub.SubFunctions
                                 -> T.TypeEnv
                                 -> HS.HashSet Name
                                 -> ([Example] -> Result)
                                 -> [Example]
                                 -> m Result
runSygusWithGrammarWithFallBack' con cg const_vals h sub tenv hsr fallback es
    | (_:_) <- es = do
        let form = toSygusWithGrammar cg const_vals h sub tenv hsr es
        liftIO $ whenLoud $ putStrLn form

        r <- liftIO $ tryVariousCVC4Options h sub tenv form ".sl" (smt_timeout con) cvc4Options
        liftIO $ whenLoud $ print r

        case r of
            Unknown -> return $ fallback es
            _ -> return r
    | otherwise = return $ Sat M.empty
    where
        cvc4Options = [ ["--lang", "sygus", "--no-sygus-pbe"]
                      , ["--lang", "sygus"] ]

runSygusWithGrammar :: (NameGenMonad m, MonadIO m) => LIVSConfigNames -> CallGraph -> [Val] -> H.Heap -> Sub.SubFunctions -> T.TypeEnv -> HS.HashSet Name -> [Example] -> m (Result, Sub.SubFunctions)
runSygusWithGrammar con cg const_vals h sub tenv hsr es =
    runSygusWithGrammarWithFallBack con cg const_vals h sub tenv hsr es (\_ -> Unknown)

-- | Tries running CVC4 with various set's of options, until one set returns an answer in the given amount of time
tryVariousCVC4Options :: H.Heap -> Sub.SubFunctions -> T.TypeEnv -> String -> String -> Int -> [[String]] -> IO Result
tryVariousCVC4Options _ _ _ _ _ _ [] = return Unknown
tryVariousCVC4Options h sub tenv form ext timeout (opt:opts) = do
    liftIO $ whenLoud $ putStrLn $ "Trying CVC4 with " ++ show opt

    m <- runCVC4WithFile form ext opt timeout
    let r = parseSMT (H.map' typeOf h) tenv sub . lexSMT $ m

    case r of
        Unknown -> tryVariousCVC4Options h sub tenv form ext timeout opts
        _ -> return r

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
