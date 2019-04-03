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

import Prelude as P

jsJSONToVal :: String -> Val
jsJSONToVal s =
    case parse json $ B.pack $ map repSnglWithDbl s of
      Fail _ _ _
        | 'N':'a':'N':_ <- s -> DataVal jsNaNDC
        | "TypeError" <- P.take 9 s -> DataVal jsErrorDC
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
toValue = \case
  Number n
      | Just n' <- toBoundedInteger n -> AppVal (DataVal jsIntDC) $ LitVal (LInt n')
      | otherwise -> AppVal (DataVal undefined) $ LitVal (LFloat $ toRealFloat n)
  String t -> AppVal (DataVal jsStringDC) $ LitVal (LString $ T.unpack t)
  Object _ -> undefined
  Array _  -> undefined
  Bool b -> if b then DataVal trueDC else DataVal falseDC
  Null     -> undefined