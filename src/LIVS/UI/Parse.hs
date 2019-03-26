module LIVS.UI.Parse ( examplesFromFile
                     , parseExamples
                     , parseExample) where

import LIVS.Language.Syntax
import LIVS.Language.Typing

import Text.Regex

-- | Parse all examples from somewhere in a file.
examplesFromFile :: (String -> Val) -> FilePath -> IO [Example]
examplesFromFile stv fp = do
    c <- readFile fp
    return $ parseExamples stv c

-- | Parse all examples from somewhere in a string.
parseExamples :: (String -> Val) -> String -> [Example]
parseExamples stv s =
    case matchRegexAll exampleRegex s of
        Just (_, _, after, [call, out]) ->
            case parseExample' stv call out of
                Just e -> e:parseExamples stv after
                Nothing -> parseExamples stv after
        _ -> []

-- | Parse an example from somewhere in a string.  An example has the form:
--  @pbe (constraint (= ([Func_Name] [Val_1] ... [Val_n]) [Val]))
-- where the parsing of Val's is based on the passed function.
parseExample :: (String -> Val) -> String -> Maybe Example
parseExample stv s =
    case matchRegex exampleRegex s of
        Just [call, out] -> parseExample' stv call out
        _ -> Nothing

exampleRegex :: Regex
exampleRegex = mkRegex "@pbe[ ]*\\(constraint[ ]\\(=[ ]*\\(([a-zA-Z0-9 ]*)\\)[ ]*([a-zA-Z0-9 ]*)\\)\\)"

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