{
module LIVS.Sygus.SMTLexer ( Token (..) 
                           , lexSMT ) where
}

%wrapper "basic"

$digit = 0-9
$alpha = [a-zA-Z]
$symbs = [\+ \- \* \> \=]

tokens:-
    $white+                                             ;
    unsat                                               ;
    define\-fun                                         { const TokenDefineFun }
    \(                                                  { const TokenOpenParen }
    \)                                                  { const TokenCloseParen }
    [$alpha $symbs] [$alpha $digit $symbs \_ \']*       { TokenName }
    $digit+                                             { TokenInt . read }

{
data Token = TokenName String
           | TokenInt Int
           | TokenDefineFun
           | TokenOpenParen
           | TokenCloseParen
           deriving Show

lexSMT :: String -> [Token]
lexSMT = alexScanTokens
}