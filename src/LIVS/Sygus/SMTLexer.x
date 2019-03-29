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
    $digit+                                             { TokenInt . read }
    \(\-$white$digit+\)                                 { TokenInt . read . elimWhiteParens }
    \(                                                  { const TokenOpenParen }
    \)                                                  { const TokenCloseParen }
    [$alpha $symbs] [$alpha $digit $symbs ]*            { TokenName }
    \" [$alpha $digit $symbs ]* \"                      { TokenString . elimOpenCloseQuote }

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

elimWhiteParens :: String -> String
elimWhiteParens ('(':xs) = elimWhiteParens xs
elimWhiteParens (')':xs) = elimWhiteParens xs
elimWhiteParens (' ':xs) = elimWhiteParens xs
elimWhiteParens (x:xs) = x:elimWhiteParens xs
elimWhiteParens [] = []

elimOpenCloseQuote :: String -> String
elimOpenCloseQuote ('"':xs) = elimOpenCloseQuote' xs
elimOpenCloseQuote _ = error "elimOpenCloseQuote: Bad string"

elimOpenCloseQuote' :: String -> String
elimOpenCloseQuote' ('"':[]) = []
elimOpenCloseQuote' (x:xs) = elimOpenCloseQuote' xs
elimOpenCloseQuote' [] = error "elimOpenCloseQuote': Bad string"
}