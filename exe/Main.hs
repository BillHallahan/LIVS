module Main where

import qualified Lava.Language.Heap as H
import Lava.Language.Syntax
import Lava.Language.Typing

import Lava.Sygus.CVC4Interface
import Lava.Sygus.SMTParser
import Lava.Sygus.SMTLexer
import Lava.Sygus.ToSygus

import qualified Data.Map as M

main :: IO ()
main = do
    let h = H.fromList [("add", Lam 
                                (Id "x" intType) 
                                (Lam 
                                    (Id "y" intType) 
                                    (App 
                                        (App 
                                            (Var (Id "+" (TyFun intType (TyFun intType intType))))
                                            (Var (Id "y" intType))
                                        )
                                        (Var (Id "x" intType))
                                    )
                                ))]

    let form = toSygus h examples

    putStrLn form

    putStrLn ""

    cvc4 <- getCVC4
    r <- runCVC4 cvc4 form

    putStrLn r

    let l = lexer r
    putStrLn $ show l

    let p = parse (M.fromList [("+", TyFun intType (TyFun intType intType))]) l
    putStrLn $ show p

examples :: [Example]
examples = [ Example { func_name = "double"
                     , input = [LInt 1]
                     , output = LInt 2 }
           , Example { func_name = "double"
                     , input = [LInt 2]
                     , output = LInt 4 }
           -- , Example { func_name = "doubleAndAdd"
           --           , input = [LInt 2, LInt 3]
           --           , output = LInt 10 }
           -- , Example { func_name = "doubleAndAdd"
           --           , input = [LInt 3, LInt 4]
           --           , output = LInt 14 }
           ]