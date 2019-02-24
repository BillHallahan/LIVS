module LIVS.Sygus.CVC4Interface ( CVC4
                                , runCVC4WithFile

                                , getCVC4
                                , runAndReadCVC4
                                , closeCVC4) where

import qualified LIVS.Heap as H
import LIVS.Sygus.ToSygus
import LIVS.Target.General.Process

import System.IO
import System.IO.Temp

runSygus :: MonadIO m => H.Heap -> [Example] -> m (HM.HashMap Name Expr)
runSygus h es = do
    let form = toSygus h es
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

            runProcessOnce "cvc4" [fp, "--lang", "sygus"])

newtype CVC4 = CVC4 Process

getCVC4 :: IO CVC4
getCVC4 = return . CVC4 =<< getProcess "cvc4" ["--lang", "sygus", "--produce-models"]

runAndReadCVC4 :: CVC4 -> String -> IO String
runAndReadCVC4 (CVC4 cvc4) = runAndReadProcess cvc4

closeCVC4 :: CVC4 -> IO ()
closeCVC4 (CVC4 cvc4) = closeProcess cvc4 "(exit)\n"