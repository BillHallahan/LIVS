module LIVS.Target.JavaScript.JSIdentifier where

import LIVS.Language.Syntax
import qualified LIVS.Language.TypeEnv as T
import LIVS.Language.Typing

jsIdentName :: Name
jsIdentName = Name Ident "JSIdentifier" Nothing

jsIdentType :: Type
jsIdentType = TyCon (jsIdentName) TYPE

jsIntDCName :: Name
jsIntDCName = Name Ident "JSInt" Nothing

jsIntDC :: DC
jsIntDC = DC jsIntDCName (TyFun intType jsIdentType)

jsIntSelectorName :: Name
jsIntSelectorName = Name Ident "jsInt" Nothing

jsFloatDCName :: Name
jsFloatDCName = Name Ident "JSFloat" Nothing

jsFloatDC :: DC
jsFloatDC = DC jsFloatDCName (TyFun floatType jsIdentType)

jsFloatSelectorName :: Name
jsFloatSelectorName = Name Ident "jsFloat" Nothing

jsStringDCName :: Name
jsStringDCName = Name Ident "JSString" Nothing

jsStringDC :: DC
jsStringDC = DC jsStringDCName (TyFun stringType jsIdentType)

jsStringSelectorName :: Name
jsStringSelectorName = Name Ident "jsString" Nothing

jsBoolDCName :: Name
jsBoolDCName = Name Ident "JSBool" Nothing

jsBoolDC :: DC
jsBoolDC = DC jsBoolDCName (TyFun boolType jsIdentType)

jsBoolSelectorName :: Name
jsBoolSelectorName = Name Ident "jsBool" Nothing

jsNaNDCName :: Name
jsNaNDCName = Name Ident "NaN2" Nothing

jsNaNDC :: DC
jsNaNDC = DC jsNaNDCName jsIdentType

jsErrorDCName :: Name
jsErrorDCName = Name Ident "Error" Nothing

jsErrorDC :: DC
jsErrorDC = DC jsErrorDCName jsIdentType

jsUndefinedDCName :: Name
jsUndefinedDCName = Name Ident "Undefined" Nothing

jsUndefinedDC :: DC
jsUndefinedDC = DC jsUndefinedDCName jsIdentType


jsTypeEnv :: T.TypeEnv
jsTypeEnv = T.fromList
    [ ( jsIdentName
      , T.ADTSpec
            [ T.SelectorDC jsIntDCName
                [ T.NamedType jsIntSelectorName intType ]
            , T.SelectorDC jsStringDCName
                [ T.NamedType jsStringSelectorName stringType ]
            , T.SelectorDC jsBoolDCName
                [ T.NamedType jsBoolSelectorName boolType ]
            -- , T.SelectorDC jsFloatDCName
            --     [ T.NamedType jsFloatSelectorName floatType ]
            , T.SelectorDC jsNaNDCName []
            , T.SelectorDC jsErrorDCName []
            , T.SelectorDC jsUndefinedDCName []
            ]
      )
    ]
