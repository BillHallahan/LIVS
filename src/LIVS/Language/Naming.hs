module LIVS.Language.Naming ( Name (..)
                            , nameToString
                            , stringToName ) where

import LIVS.Language.Syntax

import Data.Char

nameToString :: Name -> String
nameToString (Name n Nothing) = n
nameToString (Name n (Just i)) = n ++ show i

stringToName :: String -> Name
stringToName s =
    let
        (i, s') = span isDigit . reverse $ s
        s'' = reverse s'
    in
    case i of
        _:_ -> Name s'' (Just . read $ reverse i)
        [] -> Name s'' Nothing