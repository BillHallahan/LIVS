module Language.Monad.Naming where

import LIVS.Language.Naming
import LIVS.Language.Monad.Naming

import Data.List

import Test.Tasty
import Test.Tasty.HUnit

monadNamingTests :: TestTree
monadNamingTests = testGroup "Monad Naming" [ freshNameM1 ]

freshNameM1 :: TestTree
freshNameM1 = testCase "freshNameM"
    $ assertBool "freshNameM returns unique names"
        (evalNameGenM freshNameM1' nameGen)

freshNameM1' :: NameGenM Bool
freshNameM1' = do
    let f = Name "f" Nothing
        g = Name "g" Nothing


    fList <- mapM freshNameM $ replicate 10 f
    gList <- mapM freshNameM $ replicate 10 g

    let lst = fList ++ gList

    return $ lst == nub lst

nameGen :: NameGen
nameGen = mkNameGen [Name "f" (Just 4), Name "g" (Just 7)]