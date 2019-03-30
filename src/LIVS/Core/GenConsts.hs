module LIVS.Core.GenConsts (genConsts) where

import LIVS.Language.Syntax

import Data.List

-- | Given a list of constants, generates a list of constants to be used in
-- the grammar and in example generation.
genConsts :: [Val] -> [Val]
genConsts vs = nub $ genInts vs ++ genStrings vs

genInts :: [Val] -> [Val]
genInts vs = concatMap ints vs
    where
        ints l@(LitVal (LInt i)) = [l]
        ints (AppVal v1 v2) = ints v1 ++ ints v2
        ints _ = []

genStrings :: [Val] -> [Val]
genStrings vs =
    let
        vs' = concatMap strs vs
    in
    concatMap singleChars vs'
    where
        strs (LitVal (LString s)) = [s]
        strs (AppVal v1 v2) = strs v1 ++ strs v2
        strs _ = []

        singleChars (x:xs) = (LitVal $ LString [x]):singleChars xs
        singleChars [] = []