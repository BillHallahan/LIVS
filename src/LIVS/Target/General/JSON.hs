{-# LANGUAGE LambdaCase #-}

module LIVS.Target.General.JSON where

import Data.Maybe
import Data.Scientific
import Data.Aeson
import LIVS.Target.JavaScript.JSIdentifier
import LIVS.Language.Syntax
import qualified Data.Text as T

-- | convert the JSON object to the homemade data type
toValue :: Value -> Val
toValue = \case
  Number n
  	  | Just n' <- toBoundedInteger n -> AppVal (DataVal jsIntDC) $ LitVal (LInt n')
  	  | otherwise -> AppVal (DataVal undefined) $ LitVal (LFloat $ toRealFloat n)
  String t -> AppVal (DataVal jsStringDC) $ LitVal (LString $ T.unpack t)
  Object o -> undefined
  Array a  -> undefined
  Bool b   -> undefined
  Null     -> undefined