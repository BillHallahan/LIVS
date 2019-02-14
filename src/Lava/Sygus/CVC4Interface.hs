module Lava.Sygus.CVC4Interface ( CVC4
                                , getCVC4
                                , runCVC4
                                , closeCVC4 ) where

import Control.Exception
import System.IO
import System.Process

newtype CVC4 = CVC4 (Handle, Handle, ProcessHandle)

getCVC4 :: IO CVC4
getCVC4 = return . CVC4 =<< getProcessHandles 
        (proc "cvc4" ["--lang", "sygus", "--produce-models"])

getProcessHandles :: CreateProcess -> IO (Handle, Handle, ProcessHandle)
getProcessHandles pr = do
    (m_h_in, m_h_out, h_err, p) <- createProcess (pr)
        { std_in = CreatePipe, std_out = CreatePipe }

    case h_err of
        Just h_err' -> hClose h_err'
        Nothing -> return ()

    let (h_in, h_out) =
            case (m_h_in, m_h_out) of
                (Just i, Just o) -> (i, o)
                _ -> error "Pipes to shell not successfully created."

    hSetBuffering h_in LineBuffering

    return (h_in, h_out, p)

runCVC4 :: CVC4 -> String -> IO String
runCVC4 cvc4 s = do
    writeCVC4 cvc4 s
    readCVC4 cvc4

writeCVC4 :: CVC4 -> String -> IO ()
writeCVC4 (CVC4 (h_in, _, _)) form = hPutStr h_in form

readCVC4 :: CVC4 -> IO String
readCVC4 cvc4@(CVC4 (_, h_out, _)) = do
    r <- hWaitForInput h_out (-1)
    if r then do
        out <- hGetContents h_out
        _ <- evaluate (length out)

        return out
    else error "readCVC4: wait failed"

closeCVC4 :: CVC4 -> IO ()
closeCVC4 (CVC4 (h_in, _, _)) = hPutStr h_in "(exit)"