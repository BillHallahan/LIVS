{
module LIVS.Sygus.SMTLexer ( Token (..) 
                           , lexSMT ) where
}

%wrapper "basic"

$digit = 0-9
$alpha = [a-zA-Z]
$symbs = [\+ \- \* \> \= \. \_ \']

tokens:-
    $white+                                             ;
    sat                                                 { const TokenSat }
    unsat                                               { const TokenUnSat }
    unknown                                             { const TokenUnknown}
    define\-fun                                         { const TokenDefineFun }
    \(                                                  { const TokenOpenParen }
    \)                                                  { const TokenCloseParen }
    [$alpha $symbs] [$alpha $digit $symbs ]*            { TokenName }
    \" [$alpha $digit $symbs ]* \"                      { TokenString }
    $digit+                                             { TokenInt . read }

{
data Token = TokenSat
           | TokenUnSat
           | TokenUnknown
           | TokenName String
           | TokenInt Int
           | TokenString String
           | TokenDefineFun
           | TokenOpenParen
           | TokenCloseParen
           deriving Show

lexSMT :: String -> [Token]
lexSMT = alexScanTokens
}