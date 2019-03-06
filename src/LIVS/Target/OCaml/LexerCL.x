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
    $alpha [$alpha $digit \_ \']*                       { word TokenName }
    $white+                                             ;
    \#                                                  ;
    \-                                                  ;
    \:                                                  ;
    =                                                   { \_ _ -> return TokenEq }
    int                                                 ;
{
data Token = TokenName String
           | TokenInt Int
           | TokenEq
           | TokenEOF

word wr (_,_,_,input) len = return $ wr (take len input)

lexer :: String -> Either String [Token]
lexer str = runAlex str lexer1

lexer1 :: Alex [Token]
lexer1 = do
    tok <- alexMonadScan
    case tok of
        TokenEOF -> return []
        _ -> return . (:) tok =<< lexer1

alexEOF = return TokenEOF
}