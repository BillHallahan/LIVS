module LIVS.Sygus.CVC4Interface ( CVC4
                                , runSygus
                                , runSygusWithGrammar
                                , runCVC4WithFile

                                , getCVC4
                                , runAndReadCVC4
                                , closeCVC4) where

import LIVS.Language.CallGraph
import qualified LIVS.Language.Heap as H
import LIVS.Language.Syntax
import LIVS.Sygus.Result
import LIVS.Sygus.SMTLexer
import LIVS.Sygus.SMTParser
import LIVS.Sygus.ToSygus
import qualified LIVS.Language.TypeEnv as T
import LIVS.Language.Typing
import LIVS.Target.General.Process

import Control.Monad.IO.Class
import qualified Data.HashSet as HS
import System.IO
import System.IO.Temp

runSygus :: MonadIO m => CallGraph -> H.Heap -> T.TypeEnv -> [Example] -> m Result
runSygus cg h tenv = runSygusWithGrammar cg h tenv (HS.fromList $ H.keys h)

runSygusWithGrammar :: MonadIO m => CallGraph -> H.Heap -> T.TypeEnv -> HS.HashSet Name -> [Example] -> m Result
runSygusWithGrammar cg h tenv hsr es = do
    let form = toSygusWithGrammar cg h tenv hsr es
    liftIO $ putStrLn form
    m <- liftIO $ runCVC4WithFile form
    return . parseSMT (H.map' typeOf h) . lexSMT $ m

runCVC4WithFile :: String -- SyGuS
                -> IO String
runCVC4WithFile sygus =
    withSystemTempFile "cvc4_sygus.sy"
        (\fp h -> do
            hPutStr h sygus
            -- We call hFlush to prevent hPutStr from buffering
            hFlush h

            runProcessOnce "cvc4" [fp, "--lang", "sygus", "--tlimit", "10000"])

newtype CVC4 = CVC4 Process

getCVC4 :: IO CVC4
getCVC4 = return . CVC4 =<< getProcess "cvc4" ["--lang", "sygus", "--produce-models"]

runAndReadCVC4 :: CVC4 -> String -> IO String
runAndReadCVC4 (CVC4 cvc4) = runAndReadProcess cvc4

closeCVC4 :: CVC4 -> IO ()
closeCVC4 (CVC4 cvc4) = closeProcess cvc4 "(exit)\n"