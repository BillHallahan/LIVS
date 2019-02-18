module Lava.Target.General.Process ( Process
                                   , getProcess
                                   , runAndReadProcess
                                   , runProcess
                                   , readProcess
                                   , processReady
                                   , closeProcess
                                   , setOutBuffering
                                   , getOutBuffering
                                   , showProcess) where

import Control.Exception
import System.IO
import System.Process hiding (readProcess, runProcess)

newtype Process = Process (Handle, Handle, ProcessHandle)

getProcess :: String -- ^ Process Name
           -> [String] -- ^ Process Args
           -> IO Process
getProcess s as = return . Process =<< getProcessHandles 
        (proc s as)

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
    hSetBuffering h_out LineBuffering

    return (h_in, h_out, p)

runAndReadProcess :: Process -> String -> IO String
runAndReadProcess pr s = do
    runProcess pr s
    readProcess pr

runProcess :: Process -> String -> IO ()
runProcess (Process (h_in, _, _)) = hPutStr h_in

readProcess :: Process -> IO String
readProcess (Process (_, h_out, _)) = do
    r <- hWaitForInput h_out (-1)
    if r then do
        out <- getChars h_out
        _ <- evaluate (length out)

        return out
    else error "readProcess: wait failed"

getChars :: Handle -> IO String
getChars h =
    catch
        (do
            r <- hWaitForInput h 500
            b <- hReady h
            if b then do
                s <- hGetChar h
                r <- getChars h
                return $ s:r
            else return "")
         ((\_ -> return "") :: SomeException -> IO String)

-- Is there something to be read from the process?
processReady :: Process -> IO Bool
processReady (Process (_, h_out, _)) = hReady h_out

closeProcess :: Process -> String -> IO ()
closeProcess (Process (h_in, _, _)) = hPutStr h_in

setOutBuffering :: Process -> BufferMode -> IO ()
setOutBuffering (Process (_, h_out, _)) = hSetBuffering h_out

getOutBuffering :: Process -> IO BufferMode
getOutBuffering (Process (_, h_out, _)) = hGetBuffering h_out

showProcess :: Process -> IO ()
showProcess (Process (h_in, h_out, _)) = do
    putStrLn =<< hShow h_in
    putStrLn =<< hShow h_out
