module LIVS.Target.JavaScript.JSIdentifier where

import LIVS.Language.Syntax
import qualified LIVS.Language.TypeEnv as T
import LIVS.Language.Typing

jsIdentName :: Name
jsIdentName = SMTName "JSIdentifier"

jsIdentType :: Type
jsIdentType = TyCon (jsIdentName) TYPE

jsIntDCName :: Name
jsIntDCName = SMTName "JSInt"

jsIntDC :: DC
jsIntDC = DC jsIntDCName (TyFun intType jsIdentType)

jsIntSelectorName :: Name
jsIntSelectorName = SMTName "jsInt"

jsStringDCName :: Name
jsStringDCName = SMTName "JSString"

jsStringDC :: DC
jsStringDC = DC jsStringDCName (TyFun stringType jsIdentType)

jsStringSelectorName :: Name
jsStringSelectorName = SMTName "jsString"

jsBoolDCName :: Name
jsBoolDCName = SMTName "JSBool"

jsBoolDC :: DC
jsBoolDC = DC jsBoolDCName (TyFun boolType jsIdentType)

jsBoolSelectorName :: Name
jsBoolSelectorName = SMTName "jsBool"

jsNaNDCName :: Name
jsNaNDCName = SMTName "NaN2"

jsNaNDC :: DC
jsNaNDC = DC jsNaNDCName jsIdentType

jsErrorDCName :: Name
jsErrorDCName = SMTName "Error"

jsErrorDC :: DC
jsErrorDC = DC jsErrorDCName jsIdentType

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
            , T.SelectorDC jsErrorDCName []
            ]
      )
    ]