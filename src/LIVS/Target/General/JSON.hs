{-# LANGUAGE LambdaCase #-}

module LIVS.Target.General.JSON where

import LIVS.Language.Expr
import LIVS.Language.Syntax
import LIVS.Target.JavaScript.JSIdentifier

import Data.Scientific

import Data.Attoparsec.ByteString
import Data.Aeson
import qualified Data.ByteString.Char8 as B
import qualified Data.Text as T
import Data.List (isInfixOf)

import Prelude as P

jsJSONToVal :: String -> Val
jsJSONToVal s =
    case parse json $ B.pack $ map repSnglWithDbl s of
      Fail _ _ _
        | 'N':'a':'N':_ <- s -> DataVal jsNaNDC
        | "Thrown:\nError" <- P.take 13 s -> DataVal jsErrorDC
        | "Thrown:\nTypeError" <- P.take 17 s -> DataVal jsErrorDC
        | True <- isInfixOf "TypeError" s -> DataVal jsErrorDC -- catch all type errors, @bill is there a reason you were more specific with the case above?
        | "Thrown:\nAssertionError" <- P.take 22 s -> DataVal jsErrorDC
        | "undefined" <- P.take 9 s -> DataVal jsUndefinedDC
      Fail i _ err -> error $ "Bad parse\ni = " ++ show i ++ "\nerr = " ++ err
      Partial _ -> error "Why does this happen?"
      Done _ v -> toValue v
    where
        -- | JavaScript outputs JSON with single quotes, but Aeson
        -- expects double quotes
        repSnglWithDbl '\'' = '\"'
        repSnglWithDbl c = c

-- | convert the JSON object to the homemade data type
toValue :: Value -> Val
toValue v = case v of
  Number n
      | Just n' <- toBoundedInteger n -> AppVal (DataVal jsIntDC) $ LitVal (LInt n')
      | otherwise -> case floatingOrInteger n of
          Right n' -> AppVal (DataVal jsIntDC) $ LitVal (LInt n')
          Left _ -> AppVal (DataVal undefined) $ LitVal (LFloat $ toRealFloat n)
  String t -> AppVal (DataVal jsStringDC) $ LitVal (LString $ T.unpack t)
  Object _ -> undefined
  Array _  -> AppVal (DataVal jsIntDC) $ LitVal (LInt (-123456789))
  Bool b -> AppVal (DataVal jsBoolDC) $ if b then DataVal trueDC else DataVal falseDC
  Null     -> undefined
