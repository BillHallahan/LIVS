{
module Lava.Sygus.SMTParser ( parse ) where

import Lava.Language.Expr
import Lava.Language.Syntax
import Lava.Sygus.SMTLexer

import Control.Monad.State.Lazy
import qualified Data.Map as M
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
data Parser = Parser { types :: M.Map Name Type}

newtype ParserM a = ParserM (State Parser a) deriving (Applicative, Functor, Monad)

instance MonadState Parser ParserM where
    state f = ParserM (state f)

parse :: M.Map Name Type -> [Token] -> M.Map Name Expr
parse m t = M.fromList . fst $ runParserM m (parse1 t) 

parseError :: [Token] -> a
parseError _ = error "Parse error."

-- Helpers for the monad
runParserM :: M.Map Name Type -> ParserM a -> (a, Parser)
runParserM m (ParserM p) = runState p (Parser { types = m })

setTypes :: M.Map Name Type -> ParserM ()
setTypes m = do
    s <- get
    put $ s { types = m }

getTypes :: ParserM (M.Map Name Type)
getTypes = return . types =<< get

setType :: Name -> Type -> ParserM ()
setType n t = do
    m <- getTypes
    setTypes (M.insert n t m)

getType :: Name -> ParserM (Maybe Type)
getType n = return . M.lookup n =<< getTypes

idM :: Name -> ParserM Id
idM n = do
    t <- getType n
    case t of
        Just t' -> return (Id n t')
        Nothing -> return (Id n TYPE)
}