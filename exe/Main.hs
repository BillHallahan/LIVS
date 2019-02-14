module Main where

import Lava.Language.Syntax

import Lava.Sygus.CVC4Interface
import Lava.Sygus.SMTParser
import Lava.Sygus.SMTLexer
import Lava.Sygus.ToSygus

import qualified Data.Map as M

main :: IO ()
main = do
    let form = toSygus examples

    putStrLn form

    putStrLn ""

    cvc4 <- getCVC4
    writeCVC4 cvc4 form
    r <- readCVC4 cvc4

    putStrLn r

    let l = lexer r
    putStrLn $ show l

    let p = parse M.empty l
    putStrLn $ show p

examples :: [Example]
examples = [ Example { func_name = "double"
                     , input = [LInt 1]
                     , output = LInt 2}
           , Example { func_name = "double"
                     , input = [LInt 2]
                     , output = LInt 4}
           ]