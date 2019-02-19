{
module Lava.Target.OCaml.LexerCL ( Token (..)
                                 , lexer ) where
}

%wrapper "basic"

$digit = 0-9
$alpha = [a-zA-Z]

tokens:-
    $white+                                             ;
    \#                                                  ;
    \-                                                  ;
    \:                                                  ;
    =                                                   ;
    int                                                 ;
    $digit+                                             { TokenInt . read }
{
data Token = TokenInt Int

lexer :: String -> [Token]
lexer = alexScanTokens
}