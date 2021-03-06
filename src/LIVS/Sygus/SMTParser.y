{

{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}

module LIVS.Sygus.SMTParser ( parseSMT ) where

import LIVS.Language.Expr
import LIVS.Language.Naming
import qualified LIVS.Language.SubFunctions as Sub
import LIVS.Language.Syntax
import qualified LIVS.Language.TypeEnv as T
import LIVS.Language.Typing
import LIVS.Sygus.Result
import LIVS.Sygus.SMTLexer

import Control.Monad.State.Lazy
import qualified Data.HashMap.Lazy as HM
import Data.List

import Debug.Trace
}

%name parse1
%tokentype { Token }
%error { parseError }

%token
    sat         { TokenSat }
    unsat       { TokenUnSat }
    unknown     { TokenUnknown }
    smtName     { TokenName $$ }
    string      { TokenString $$ }
    int         { TokenInt $$ }
    defineFun   { TokenDefineFun }
    '('         { TokenOpenParen }
    ')'         { TokenCloseParen }

%monad { ParserM }

%%

res :: { Result }
     : unsat defFuns { Sat $ HM.fromList $2 }
     | sat '(' model ')' { Sat $ HM.fromList $3 }
     | sat { UnSat }
     | unknown { Unknown }

defFuns :: { [(Name, Expr)] }
        : defFuns defFun { $2:$1 }
        | {- empty -} { [] }

defFun :: { (Name, Expr) }
       : '(' defineFun name '(' args ')' ret expr ')' { ($3 , mkLams $5 $8) }

args :: { [Id] }
     : args_rev { reverse $1 }

args_rev :: { [Id] }
         : args_rev arg { $2:$1 }
         | {- empty -}   { [] }

arg :: { Id }
    : '(' name name ')' {% do
                            let (Name _ n i) = $3 
                            let t = TyCon (Name SMT n i) TYPE
                            setType $2 t
                            return $ Id $2 t }

ret :: { Type }
    : name { TyCon $1 TYPE }

exprs :: { [Expr] }
      : exprs_rev { reverse $1 }

exprs_rev :: { [Expr] }
          : exprs_rev expr { $2:$1 }
          | {- empty -}   { [] }

expr :: { Expr }
     : '(' name exprs ')' {% do
                                e <- varOrData $2
                                case e of
                                    Var i -> do
                                        i'<- adjustSMTType i (mkTyFun $ map typeOf $3)
                                        return $ mkApp (Var i':$3) 
                                    _ -> return $ mkApp (e:$3) }
     | name {% varOrData $1 }
     | string { Lit (LString $1) }
     | int { Lit (LInt $1) }

name :: { Name }
     : smtName { stringToName Ident $1 }

model :: { [(Name, Expr)] }
      : model '(' modelVal ')' { $3:$1 }
      | {- empty -} { [] }

modelVal :: { (Name, Expr) }
         : name expr { ($1, $2) }

{
data Parser = Parser { types :: HM.HashMap Name Type
                     , type_env :: T.TypeEnv
                     , subfunctions :: Sub.SubFunctions }

newtype ParserM a = ParserM (State Parser a) deriving (Applicative, Functor, Monad)

instance MonadState Parser ParserM where
    state f = ParserM (state f)

parseSMT :: HM.HashMap Name Type -> T.TypeEnv -> Sub.SubFunctions -> [Token] -> Result
parseSMT m tenv sub t = fst $ runParserM m tenv sub (parse1 t)

parseError :: [Token] -> a
parseError _ = error "Parse error."

-- Helpers for the monad
runParserM :: HM.HashMap Name Type -> T.TypeEnv -> Sub.SubFunctions -> ParserM a -> (a, Parser)
runParserM m tenv sub (ParserM p) =
    runState p (Parser { types = m, type_env = tenv, subfunctions = sub })

setTypes :: HM.HashMap Name Type -> ParserM ()
setTypes m = do
    s <- get
    put $ s { types = m }

getTypes :: ParserM (HM.HashMap Name Type)
getTypes = return . types =<< get

setType :: Name -> Type -> ParserM ()
setType n t = do
    m <- getTypes
    setTypes (HM.insert n t m)

getType :: Name -> ParserM (Maybe Type)
getType n = return . HM.lookup n =<< getTypes

getTypeEnv :: ParserM (T.TypeEnv)
getTypeEnv = return . type_env =<< get

getTypeNamesAndSelectorDCs :: ParserM [(Name, T.SelectorDC)]
getTypeNamesAndSelectorDCs = return . T.typeNamesAndSelectorDCs =<< getTypeEnv

getSubFunctions :: ParserM (Sub.SubFunctions)
getSubFunctions = return . subfunctions =<< get

adjustSMTType :: Id -> Type -> ParserM Id
adjustSMTType i@(Id n _) t = do
    sub <- getSubFunctions
    case n of
        Name Ident _ _ -> return i
        Name SMT _ _
            | Just (n', t') <- Sub.lookupNameInputType n t sub -> return $ Id n' t'
            | otherwise -> return i

idM :: Name -> ParserM Id
idM n@(Name ll n' i) = do
    t <- getType n
    case t of
        Just t' -> return (Id n t')
        Nothing -> do
            let new_n = Name (flipLangLevel ll) n' i
            new_t <- getType new_n
            case new_t of
                Just new_t' -> return (Id new_n new_t')
                Nothing -> return (Id n TYPE)

flipLangLevel :: LanguageLevel -> LanguageLevel
flipLangLevel Ident = SMT
flipLangLevel SMT = Ident

varOrData :: Name -> ParserM Expr
varOrData n = do
    sdcs <- getTypeNamesAndSelectorDCs
    case find (\dc -> n == T.selectorDCName (snd dc)) sdcs of
        Just (tn, dc') -> return . Data $ T.selectorDCToDC tn dc'
        Nothing -> do
            i <- idM n
            return $ Var i
}
