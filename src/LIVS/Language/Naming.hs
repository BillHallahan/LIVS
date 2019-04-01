module LIVS.Language.Naming ( Name (..)
                            , nameToString
                            , stringToInternalName

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
nameToString (IdentName n) = n
nameToString (SMTName n) = n
nameToString (InternalName n Nothing _) = n
nameToString (InternalName n (Just i) _) = n ++ show i

stringToInternalName :: String -> Name
stringToInternalName s =
    let
        (i, s') = span isDigit . reverse $ s
        s'' = reverse s'
    in
    case i of
        _:_ -> InternalName s'' (Just . read $ reverse i) Nothing
        [] -> InternalName s'' Nothing Nothing

newtype NameGen = NameGen (HM.HashMap String Integer)

mkNameGen :: [Name] -> NameGen
mkNameGen =
    NameGen . HM.fromList . map (\n -> (nameString n, maybe 0 (+ 1) $ unique n))

freshName :: Name -> NameGen -> (Name, NameGen)
freshName n (NameGen ng) 
    | InternalName _ _ mn <- n = (InternalName s (Just i) mn, NameGen ng')
    | otherwise = (InternalName s (Just i) Nothing, NameGen ng')
    where
        s = nameString n
        i = HM.lookupDefault 0 s ng
        ng' = HM.insert s (i + 1) ng

unseededFreshName :: NameGen -> (Name, NameGen)
unseededFreshName = freshName (InternalName "fresh" Nothing Nothing)

freshId :: Name -> Type -> NameGen -> (Id, NameGen)
freshId n t ng =
    let
        (n', ng') = freshName n ng
    in
    (Id n' t, ng')

unseededFreshId :: Type -> NameGen -> (Id, NameGen)
unseededFreshId = freshId (InternalName "fresh" Nothing Nothing)