module LIVS.UI.Parse (parseExample) where

import LIVS.Language.Syntax
import LIVS.Language.Typing

import Text.Regex

parseExample :: (String -> Val) -> String -> Maybe Example
parseExample stv s =
    let
        r = mkRegex "@pbe[ ]*\\(constraint[ ]\\(=[ ]*\\(([a-zA-Z0-9 ]*)\\)[ ]*([a-zA-Z0-9 ]*)\\)\\)"
    in
    case matchRegex r s of
        Just [call, out] -> parseExample' stv call out
        _ -> Nothing

parseExample' :: (String -> Val) -> String -> String -> Maybe Example
parseExample' stv call out
    | f:ars <- words call =
        let
            -- Aeson requires the newline to parse values
            arsV = map stv $ map (++ "\n") ars
            outV = stv (out ++ "\n")

            f_t = mkTyFun $ map typeOf arsV ++ [typeOf outV]
        in
        Just $ Example { func = Id (Name f Nothing) f_t
                       , input = arsV
                       , output = outV }
    | otherwise = Nothing