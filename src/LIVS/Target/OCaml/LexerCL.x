{
module LIVS.Target.OCaml.LexerCL ( Token (..)
                                 , lexer ) where
}

%wrapper "basic"

$digit = 0-9
$alpha = [a-zA-Z]

tokens:-
    \-$digit+                                           { TokenInt . read }
    $digit+                                             { TokenInt . read }
    $white+                                             ;
    \#                                                  ;
    \-                                                  ;
    \:                                                  ;
    =                                                   ;
    int                                                 ;
{
data Token = TokenInt Int

lexer :: String -> [Token]
lexer = alexScanTokens
}