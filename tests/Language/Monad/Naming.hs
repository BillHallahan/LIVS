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
    let f = InternalName "f" Nothing Nothing
        g = InternalName "g" Nothing Nothing


    fList <- mapM freshNameM $ replicate 10 f
    gList <- mapM freshNameM $ replicate 10 g

    let lst = fList ++ gList

    return $ lst == nub lst

nameGen :: NameGen
nameGen = mkNameGen [InternalName "f" (Just 4) Nothing, InternalName "g" (Just 7) Nothing]