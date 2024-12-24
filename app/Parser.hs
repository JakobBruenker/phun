module Parser where

import Text.Megaparsec
import Data.Text (Text)
import Data.Text qualified as T
import Data.Void
import TC (Parsed, UExpr (..))
import Numeric.Natural (Natural)
import Text.Megaparsec.Char
import qualified Text.Megaparsec.Char.Lexer as L
import Data.Char (chr, ord)
import Data.Functor (($>))

type Parser = Parsec Void Text

sc :: Parser ()
sc = L.space
 space1
 (L.skipLineComment "--")
 (L.skipBlockComment "{-" "-}")

lexeme :: Parser a -> Parser a
lexeme = L.lexeme sc

symbol :: Text -> Parser Text
symbol = L.symbol sc

parens :: Parser a -> Parser a
parens = between (symbol "(") (symbol ")")

identifier :: Parser Text
identifier = lexeme $ try $ do
  first <- letterChar <|> char '_'
  rest <- many (alphaNumChar <|> char '_' <|> char '\'')
  let ident = T.pack (first:rest)
  if ident `elem` reserved 
    then fail $ "keyword " <> show ident <> " cannot be used as identifier"
    else return ident

reserved :: [Text] 
reserved = ["Type", "forall", "let", "in", "Pi"]

pNatural :: Parser Natural
pNatural = lexeme L.decimal

subscriptDigitChar :: Parser Char
subscriptDigitChar = oneOf ['₀'..'₉']

pSubscriptNatural :: Parser Natural
pSubscriptNatural = lexeme $ do
 n <- some subscriptDigitChar
 return (read $ map subscriptToDigit n)
 where 
   subscriptToDigit c = chr (ord c - ord '₀' + ord '0')

pUniv :: Parser Parsed
pUniv = do
 _ <- symbol "Type"
 n <- pNatural <|> pSubscriptNatural
 return (Univ n)

pHole :: Parser Parsed
pHole = lexeme (char '?') $> Hole
