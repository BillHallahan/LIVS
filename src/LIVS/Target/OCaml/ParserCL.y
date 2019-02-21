{
module LIVS.Target.OCaml.ParserCL ( parse ) where

import LIVS.Language.Syntax
import LIVS.Target.OCaml.LexerCL
}

%name parse
%tokentype { Token }
%error { parseError }

%token
    int         { TokenInt $$ }

%%

lit :: { Lit }
    : int { LInt $1 }

{
parseError :: [Token] -> a
parseError _ = error "Parse error."
}