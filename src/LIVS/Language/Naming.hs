module LIVS.Language.Naming ( Name (..)
                            , nameToString
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

newtype NameGen = NameGen (HM.HashMap String Integer)

mkNameGen :: [Name] -> NameGen
mkNameGen =
    NameGen . HM.fromList . map (\(Name n i) -> (n, maybe 0 id $ fmap (+ 1) i))

freshName :: Name -> NameGen -> (Name, NameGen)
freshName (Name n _) (NameGen ng) = (Name n (Just i), NameGen ng')
    where
        i = HM.lookupDefault 0 n ng
        ng' = HM.insert n (i + 1) ng

unseededFreshName :: NameGen -> (Name, NameGen)
unseededFreshName = freshName (Name "fresh" Nothing)

freshId :: Name -> Type -> NameGen -> (Id, NameGen)
freshId n t ng =
    let
        (n', ng') = freshName n ng
    in
    (Id n' t, ng')

unseededFreshId :: Type -> NameGen -> (Id, NameGen)
unseededFreshId = freshId (Name "fresh" Nothing)