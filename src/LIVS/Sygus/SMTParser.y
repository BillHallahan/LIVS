{
module LIVS.Sygus.SMTParser ( parseSMT ) where

import LIVS.Language.Expr
import LIVS.Language.Syntax
import LIVS.Sygus.SMTLexer

import Control.Monad.State.Lazy
import qualified Data.HashMap.Lazy as HM
}

%name parse1
%tokentype { Token }
%error { parseError }

%token
    name        { TokenName $$ }
    int         { TokenInt $$ }
    defineFun   { TokenDefineFun }
    '('         { TokenOpenParen }
    ')'         { TokenCloseParen }

%monad { ParserM }

%%

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
                            let t = TyCon $3 TYPE
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
                                i <- idM $2 
                                return $ mkApp (Var i:$3) }
     | name {% do
                i <-idM $1
                return $ Var i }
     | int { Lit (LInt $1) }

{
data Parser = Parser { types :: HM.HashMap Name Type}

newtype ParserM a = ParserM (State Parser a) deriving (Applicative, Functor, Monad)

instance MonadState Parser ParserM where
    state f = ParserM (state f)

parseSMT :: HM.HashMap Name Type -> [Token] -> HM.HashMap Name Expr
parseSMT m t = HM.fromList . fst $ runParserM m (parse1 t) 

parseError :: [Token] -> a
parseError _ = error "Parse error."

-- Helpers for the monad
runParserM :: HM.HashMap Name Type -> ParserM a -> (a, Parser)
runParserM m (ParserM p) = runState p (Parser { types = m })

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

idM :: Name -> ParserM Id
idM n = do
    t <- getType n
    case t of
        Just t' -> return (Id n t')
        Nothing -> return (Id n TYPE)
}