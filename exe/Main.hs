module Main where

import Lava.Language.Syntax
import Lava.Sygus.ToSygus

main :: IO ()
main = do
    putStrLn $ toSygus examples

examples :: [Example]
examples = [ Example { func_name = "double"
                     , input = [LInt 1]
                     , output = LInt 2}
           , Example { func_name = "double"
                     , input = [LInt 2]
                     , output = LInt 4}
           ]