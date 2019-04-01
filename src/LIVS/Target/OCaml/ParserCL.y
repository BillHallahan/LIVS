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
    tname        { TokenName $$ }
    '='         { TokenEq }

%%

response :: { Val }
         : name '=' val { $3 }

val :: { Val }
    : name { DataVal (DC $1 TYPE)}
    | int { LitVal (LInt $1) }

name :: { Name }
	  : tname { IdentName $1 }

{
parseError :: [Token] -> a
parseError _ = error "Parse error."
}