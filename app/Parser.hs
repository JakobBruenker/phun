module Parser where

import Text.Megaparsec
import Data.Text (Text)
import Data.Text qualified as T
import Data.Void
import TC (Parsed, UExpr (..), ParsedExpr, Expr (..), Id (..))
import Numeric.Natural (Natural)
import Text.Megaparsec.Char
import qualified Text.Megaparsec.Char.Lexer as L
import Data.Char (chr, ord)
import Data.Functor (($>), (<&>))
import Control.Comonad.Identity (Identity(..))

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
    else pure ident

reserved :: [Text] 
reserved = ["Pi", "∏", "Π", "λ"]

pNatural :: Parser Natural
pNatural = lexeme L.decimal

subscriptDigitChar :: Parser Char
subscriptDigitChar = oneOf ['₀'..'₉']

pSubscriptNatural :: Parser Natural
pSubscriptNatural = lexeme $ do
  n <- some subscriptDigitChar
  pure (read $ map subscriptToDigit n)
  where 
    subscriptToDigit c = chr (ord c - ord '₀' + ord '0')

pUExpr :: Parser Parsed
pUExpr = choice
  [ Expr . Identity <$> pExpr
  , pOtherUExpr
  ]


pUExprNoApp :: Parser Parsed
pUExprNoApp = choice
  [ Expr . Identity <$> pExprNoApp
  , pOtherUExpr
  ]

pOtherUExpr :: Parser Parsed
pOtherUExpr = choice
  [ pUniv
  , pHole
  , parens pUExpr
  ]

pUniv :: Parser Parsed
pUniv = do
  _ <- symbol "Type"
  n <- option 0 (pNatural <|> pSubscriptNatural)
  pure (Univ n)

pHole :: Parser Parsed
pHole = lexeme (char '_') $> Hole

pExpr :: Parser ParsedExpr
pExpr = choice
  [ try pApp
  , pExprNoApp
  ]

pExprNoApp :: Parser ParsedExpr
pExprNoApp = choice
  [ pPi
  , pLam
  , pVar
  ]

pApp :: Parser ParsedExpr
pApp = do
  (fun, lastArg, rest) <- some pUExprNoApp <&> reverse >>= \case
    (f:x0:rest) -> pure (f, x0, rest)
    _ -> fail "impossible: expected at least one argument"
  pure $ foldr (\x y -> App x (Expr (Identity y))) (App lastArg fun) $ reverse rest 

pPi :: Parser ParsedExpr
pPi = do
  _ <- symbol "Pi" <|> symbol "Π" <|> symbol "∏"
  x <- identifier
  _ <- symbol ":"
  a <- pUExpr
  _ <- symbol "."
  b <- pUExpr
  pure $ Pi (Name x) a b

pLam :: Parser ParsedExpr
pLam = do
  _ <- symbol "λ" <|> symbol "\\"
  x <- identifier
  _ <- symbol "."
  rhs <- pUExpr
  pure $ Lam (Name x) rhs

pVar :: Parser ParsedExpr
pVar = Var . Name <$> identifier
