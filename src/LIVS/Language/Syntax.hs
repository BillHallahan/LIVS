{-# LANGUAGE DeriveGeneric #-}

module LIVS.Language.Syntax ( Name (..)
                            , Id (..)
                            , Expr (..)
                            , Val (..)
                            , Lit (..)
                            , DC (..)
                            , Type (..)

                            , Example (..)
                            , SuspectExample (..)
                            , MarkedExample (..)
                            , IncorrectExample (..)

                            , exprToVal
                            , valToExpr
                            , isVal

                            , idName
                            , funcName
                            , examplesForFunc
                            , exampleFuncCall
                            , isCorrect
                            , isIncorrect
                            , mExample
                            , correct
                            , onlyCorrect
                            , onlyIncorrect
                            , iExample
                            , fixIncorrect ) where

import GHC.Generics (Generic)
import Data.Foldable
import Data.Hashable
import Data.Maybe

data Name = Name String (Maybe Integer)
            deriving (Eq, Ord, Show, Read, Generic)

instance Hashable Name

data Id = Id Name Type
          deriving (Eq, Show, Read, Generic)

instance Hashable Id

idName :: Id -> Name
idName (Id n _) = n

data Expr = Var Id
          | Data DC
          | Lit Lit
          | Lam Id Expr
          | App Expr Expr
          | Let Binding Expr
          deriving (Eq, Show, Read, Generic)

instance Hashable Expr

data Val = DataVal DC
         | LitVal Lit
         deriving (Eq, Show, Read, Generic)

instance Hashable Val

exprToVal :: Expr -> Maybe Val
exprToVal (Data dc) = Just $ DataVal dc
exprToVal (Lit l) = Just $ LitVal l
exprToVal _ = Nothing

valToExpr :: Val -> Expr
valToExpr (DataVal dc) = Data dc
valToExpr (LitVal l) = Lit l

isVal :: Expr -> Bool
isVal = isJust . exprToVal

type Binding = (Id, Expr)

data Lit = LInt Int
         | LFloat Float
           deriving (Eq, Show, Read, Generic)

instance Hashable Lit

data DC = DC Name Type
          deriving (Eq, Show, Read, Generic)

instance Hashable DC

data Type = TyCon Name Type
          | TyFun Type Type
          | TYPE
          deriving (Eq, Show, Read, Generic)

instance Hashable Type

data Example = Example { func :: Id
                       , input :: [Val]
                       , output :: Val }
                       deriving (Eq, Show, Read, Generic)

instance Hashable Example

funcName :: Example -> Name
funcName = idName . func

-- | Filter a list of examples to only those relevant to the given function
examplesForFunc :: Name -> [Example] -> [Example]
examplesForFunc n = filter (\e -> n == funcName e)

exampleFuncCall :: Example -> Expr
exampleFuncCall ex = foldl' App (Var (func ex)) $ map valToExpr (input ex)

-- | An "example" which may or may not be satisfied by the actual code.
-- Often produced by deriving the Example from interpreting the IR.
newtype SuspectExample = Suspect { sExample :: Example } deriving (Eq, Show, Read, Generic)

instance Hashable SuspectExample

-- | Used to split "Examples" between those known to be correct and thus known
-- to be incorrect.
data MarkedExample = MarkedCorrect Example
                   | MarkedIncorrect Example Val -- ^ An incorrect example, and the correct output
                   deriving (Eq, Show, Read, Generic)

instance Hashable MarkedExample

data IncorrectExample = Incorrect Example Val -- ^ An incorrect example, and the correct output
                        deriving (Eq, Show, Read, Generic)

instance Hashable IncorrectExample

isCorrect :: MarkedExample -> Bool
isCorrect (MarkedCorrect _) = True
isCorrect _ = False

isIncorrect :: MarkedExample -> Bool
isIncorrect = not . isCorrect

mExample :: MarkedExample -> Example
mExample (MarkedCorrect ex) = ex
mExample (MarkedIncorrect ex _) = ex

-- | Modifies the output of an Incorrect Example, to correct it
correct :: MarkedExample -> Example
correct (MarkedCorrect ex) = ex
correct (MarkedIncorrect ex r) = ex { output = r }

onlyCorrect :: [MarkedExample] -> [Example]
onlyCorrect = map mExample . filter (isCorrect)

onlyIncorrect :: [MarkedExample] -> [IncorrectExample]
onlyIncorrect [] = []
onlyIncorrect (MarkedCorrect _:xs) = onlyIncorrect xs
onlyIncorrect (MarkedIncorrect ex r:xs) = Incorrect ex r:onlyIncorrect xs

fixIncorrect :: IncorrectExample -> Example
fixIncorrect (Incorrect ex r) = ex { output = r}

iExample :: IncorrectExample -> Example
iExample (Incorrect ex _) = ex
