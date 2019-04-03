module LIVS.Language.Naming ( Name (..)
                            , LanguageLevel (..)
                            , nameToString
                            , nameToStringNumbered
                            , nameToStringSMT
                            , stringToName

                            , NameGen
                            , mkNameGen
                            , freshName
                            , unseededFreshName
                            , freshId
                            , unseededFreshId ) where

import LIVS.Language.Syntax

import Data.Char
import qualified Data.HashMap.Lazy as HM

nameToString :: Name -> String
nameToString (Name _ n _) = n

nameToStringNumbered :: Name -> String
nameToStringNumbered (Name _ n (Just i)) = n ++ show i
nameToStringNumbered (Name _ n Nothing) = n

-- | Prints names for use in SMT formulas.
-- We NEVER print the unique number for SMT Language Level names, because those
-- names have some meaning in the SMT solver
nameToStringSMT :: Name -> String
nameToStringSMT (Name SMT n _) = n
nameToStringSMT n = nameToStringNumbered n

stringToName :: LanguageLevel -> String -> Name
stringToName ll s =
    let
        (i, s') = span isDigit . reverse $ s
        s'' = reverse s'
    in
    case i of
        _:_ -> Name ll s'' (Just . read $ reverse i)
        [] -> Name ll s'' Nothing

newtype NameGen = NameGen (HM.HashMap String Integer)

mkNameGen :: [Name] -> NameGen
mkNameGen =
    NameGen . HM.fromList . map (\(Name _ n i) -> (n, maybe 0 id $ fmap (+ 1) i))

freshName :: Name -> NameGen -> (Name, NameGen)
freshName (Name ll n _) (NameGen ng) = (Name ll n (Just i), NameGen ng')
    where
        i = HM.lookupDefault 0 n ng
        ng' = HM.insert n (i + 1) ng

unseededFreshName :: LanguageLevel -> NameGen -> (Name, NameGen)
unseededFreshName ll = freshName (Name ll "fresh" Nothing)

freshId :: Name -> Type -> NameGen -> (Id, NameGen)
freshId n t ng =
    let
        (n', ng') = freshName n ng
    in
    (Id n' t, ng')

unseededFreshId :: LanguageLevel -> Type -> NameGen -> (Id, NameGen)
unseededFreshId ll = freshId (Name ll "fresh" Nothing)