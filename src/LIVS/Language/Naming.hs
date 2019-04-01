module LIVS.Language.Naming ( Name (..)
                            , LanguageLevel (..)
                            , nameToString

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

newtype NameGen = NameGen (HM.HashMap String Integer)

mkNameGen :: [Name] -> NameGen
mkNameGen =
    NameGen . HM.fromList . map (\(Name ll n i) -> (n, maybe 0 id $ fmap (+ 1) i))

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