module LIVS.Sygus.Result where

import LIVS.Language.Syntax

import qualified Data.HashMap.Lazy as HM

data Result = Sat (HM.HashMap Name Expr)
            | UnSat
            | Unknown
            deriving (Eq, Show, Read)

mapSat :: (HM.HashMap Name Expr -> HM.HashMap Name Expr) -> Result -> Result
mapSat f (Sat m) = Sat (f m)
mapSat _ r = r 

insertSat :: Name -> Expr -> Result -> Result
insertSat n e = mapSat (HM.insert n e)