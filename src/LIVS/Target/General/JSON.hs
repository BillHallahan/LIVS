{-# LANGUAGE LambdaCase #-}

module LIVS.Target.General.JSON where

import Data.Maybe
import Data.Scientific
import Data.Aeson
import LIVS.Language.Syntax
import qualified Data.Text as T

-- | convert the JSON object to the homemade data type
toValue :: Value -> Val
toValue = \case
  Number n -> LitVal (fromMaybe (LFloat $ toRealFloat n) (LInt <$> toBoundedInteger n))
  String t -> LitVal (LString $ T.unpack t)
  Object o -> undefined
  Array a  -> undefined
  Bool b   -> undefined
  Null     -> undefined

