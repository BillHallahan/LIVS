{
module Lava.Sygus.SMTLexer ( Token (..) 
                           , lexer ) where
}

%wrapper "basic"

$digit = 0-9
$alpha = [a-zA-Z]
$symbs = [\+\-\*]

tokens:-
    $white+                                             ;
    unsat                                               ;
    define\-fun                                         { const TokenDefineFun }
    \(                                                  { const TokenOpenParen }
    \)                                                  { const TokenCloseParen }
    [$alpha $symbs] [$alpha $digit $symbs \_ \']*       { TokenName }

{
data Token = TokenName String
           | TokenDefineFun
           | TokenOpenParen
           | TokenCloseParen
           deriving Show

lexer :: String -> [Token]
lexer = alexScanTokens
}