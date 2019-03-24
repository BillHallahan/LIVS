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

jsIntDC :: DC
jsIntDC = DC jsIntDCName (TyFun intType jsIdentType)

jsIntSelectorName :: Name
jsIntSelectorName = Name "jsInt" Nothing

jsStringDCName :: Name
jsStringDCName = Name "JSString" Nothing

jsStringDC :: DC
jsStringDC = DC jsStringDCName (TyFun stringType jsIdentType)

jsStringSelectorName :: Name
jsStringSelectorName = Name "jsString" Nothing

jsBoolDCName :: Name
jsBoolDCName = Name "JSBool" Nothing

jsBoolDC :: DC
jsBoolDC = DC jsBoolDCName (TyFun boolType jsIdentType)

jsBoolSelectorName :: Name
jsBoolSelectorName = Name "jsBool" Nothing

jsNaNDCName :: Name
jsNaNDCName = Name "NaN2" Nothing

jsNaNDC :: DC
jsNaNDC = DC jsNaNDCName jsIdentType

jsTypeEnv :: T.TypeEnv
jsTypeEnv = T.fromList
    [ ( jsIdentName
      , T.ADTSpec
            [ T.SelectorDC jsIntDCName [ T.NamedType jsIntSelectorName intType ]
            , T.SelectorDC jsStringDCName
                [ T.NamedType jsStringSelectorName stringType ]
            , T.SelectorDC jsBoolDCName
                [ T.NamedType jsBoolSelectorName boolType ]
            , T.SelectorDC jsNaNDCName []
            ]
      )
    ]