{
module LIVS.Target.OCaml.LexerCL ( Token (..)
                                 , lexer ) where
}

%wrapper "monad"

$digit = 0-9
$alpha = [a-zA-Z]

tokens:-
    \-$digit+                                           { word (TokenInt . read) }
    $digit+                                             { word (TokenInt . read) }
    $white+                                             ;
    \#                                                  ;
    \-                                                  ;
    \:                                                  ;
    =                                                   ;
    int                                                 ;
{
data Token = TokenInt Int
           | TokenEOF

word wr (_,_,_,input) len = return $ wr (take len input)

lexer :: String -> Either String [Token]
lexer s = runAlex s lexer1

lexer1 :: Alex [Token]
lexer1 = do
    tok <- alexMonadScan
    case tok of
        TokenEOF -> return []
        _ -> return . (:) tok =<< lexer1


alexEOF = return TokenEOF
}