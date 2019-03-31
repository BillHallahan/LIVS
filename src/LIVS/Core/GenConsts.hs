module LIVS.Core.GenConsts ( genConsts
                           , genIntsConsts
                           , genFuzzConsts
                           , expandVals) where

import LIVS.Language.Syntax
import qualified LIVS.Language.TypeEnv as T
import LIVS.Language.Typing

import Control.Monad
import Data.List

-- | Given a list of constants, generates a list of constants to be used in
-- the grammar and in example generation.
genConsts :: [Val] -> [Val]
genConsts vs = nub $ genIntsConsts vs ++ genStrings vs

genIntsConsts :: [Val] -> [Val]
genIntsConsts vs = concatMap ints vs ++ concatMap strLens vs
    where
        ints l@(LitVal (LInt i)) = [l]
        ints (AppVal v1 v2) = ints v1 ++ ints v2
        ints _ = []

        strLens (LitVal (LString s)) = map (LitVal . LInt) [0..length s]
        strLens (AppVal v1 v2) = strLens v1 ++ strLens v2
        strLens _ = []

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

genFuzzConsts :: [Val] -> [Val]
genFuzzConsts vs = nub $ genFuzzStringConsts vs ++ genConsts vs

genFuzzStringConsts :: [Val] -> [Val]
genFuzzStringConsts = concatMap subseqStr
    where
        subseqStr (LitVal (LString s)) =
            map (LitVal . LString) . concat . map inits . tails $ s
        subseqStr (AppVal v1 v2) = subseqStr v1 ++ subseqStr v2
        subseqStr _ = []


-- Generate all possible values from a non-recursive TypeEnv and a set of existing (typically primitive) types
expandVals :: [Val] -> T.TypeEnv -> [Val]
expandVals vs = concatMap (uncurry (expandVals' vs)) . T.typeNamesAndSelectorDCs

expandVals' :: [Val] -> Name -> T.SelectorDC -> [Val]
expandVals' vs n sdc@(T.SelectorDC _ ts) =
    let
        ts' = map T.namedTypeType ts
        vs' = map (\t -> [v | v <- vs, typeOf v == t]) ts'
    
        dc = T.selectorDCToDC n sdc
    in
    map (\vss -> mkAppVal $ DataVal dc:vss) $ sequence vs'
