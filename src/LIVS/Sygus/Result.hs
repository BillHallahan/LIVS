module LIVS.Sygus.Result where

import LIVS.Language.Syntax

import qualified Data.HashMap.Lazy as HM

data Result = Sat (HM.HashMap Name Expr)
            | UnSat
            | Unknown
            deriving (Eq, Show, Read)