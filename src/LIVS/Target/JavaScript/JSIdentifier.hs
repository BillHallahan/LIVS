module LIVS.Target.JavaScript.JSIdentifier where

import LIVS.Language.Syntax
import qualified LIVS.Language.TypeEnv as T
import LIVS.Language.Typing

jsIdentName :: Name
jsIdentName = Name "JSIdentifier" Nothing

jsIdentType :: Type
jsIdentType = TyCon (jsIdentName) TYPE

jsIntDCName :: Name
jsIntDCName = Name "JSInt" Nothing

jsIntSelectorName :: Name
jsIntSelectorName = Name "jsInt" Nothing

jsTypeEnv :: T.TypeEnv
jsTypeEnv = T.fromList
    [ ( jsIdentName
      , T.ADTSpec
            [ T.SelectorDC jsIntDCName [ T.NamedType jsIntSelectorName intType ] ]
      )
    ]