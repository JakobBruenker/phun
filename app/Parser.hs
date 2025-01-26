module Parser where

import Text.Megaparsec hiding (Token)
import Data.Text (Text)
import Data.Void
import TC (Parsed, UExpr (..), ParsedExpr, Pass(..), Expr (..), Id (..), Decl (..), Module (..), IdOrWildcard (..))
import Control.Comonad.Identity (Identity(..))
import Lexer
import Data.Set qualified as Set
import Data.Foldable (find)
import Data.Char (ord, chr, isDigit)
import Data.Text qualified as T
import Numeric.Natural (Natural)
import Data.Functor ((<&>))
import Data.Functor (($>))

type Parser = Parsec Void [Token]

parseTokenMatching :: (Token -> Bool) -> Parser Token
parseTokenMatching p = token (find p . Just) Set.empty

parseToken :: Token -> Parser Token
parseToken = parseTokenMatching . (==)

parens :: Parser a -> Parser a
parens = between (parseToken TLParen) (parseToken TRParen)

pUExpr :: Parser Parsed
pUExpr = choice
  [ try pApp
  , pUExprNoApp
  ]

pUExprNoApp :: Parser Parsed
pUExprNoApp = choice
  [ Expr . Identity <$> pExprNoAppOrVar
  , pVarOrUnivOrHole
  , parens pUExpr
  ]

pExprNoAppOrVar :: Parser ParsedExpr
pExprNoAppOrVar = choice
  [ pPi
  , pLam
  , pId
  , pRefl
  , pJ
  , pBottom
  , pAbsurd
  , pTop
  , pTT
  , pBool
  , pTrue
  , pFalse
  , pIf
  ]

pVarOrUnivOrHole :: Parser Parsed
pVarOrUnivOrHole = identifier <&> \case
  IVar x -> Var $ Name x
  IUniv n -> Univ n
  IHole -> Hole

data Identifier = IUniv Natural | IHole | IVar Text
  deriving (Show, Eq, Ord)

identifier :: Parser Identifier
identifier = do
  TIdent i <- parseTokenMatching \case
    TIdent _ -> True
    _ -> False
  pure $ disambiguateIdentifier i
  where
    disambiguateIdentifier :: Text -> Identifier
    disambiguateIdentifier = \case
      "?" -> IHole
      "_" -> IHole
      t@(T.stripPrefix "Type" -> Just index) -> case T.unpack index of
        "" -> IUniv 0
        i | T.all isDigit index -> IUniv $ read i
          | T.all (`elem` ['₀'..'₉']) index -> IUniv $ read $ map subscriptToDigit $ T.unpack index
        _ -> IVar t
      t -> IVar t
    subscriptToDigit c = chr (ord c - ord '₀' + ord '0')

pat :: Parser (Maybe Text)
pat = identifier >>= \case
  IVar t -> pure (Just t)
  IHole -> pure Nothing -- A hole is treated as wildcard in pattern context
  IUniv _ -> fail $ "Expected variable name or wildcard, got a universe"

name :: Parser Text
name = identifier >>= \case
  IVar t -> pure t
  _ -> fail "Expected variable name"

pApp :: Parser Parsed
pApp = do
  f <- pUExprNoApp
  xs <- some pUExprNoApp
  pure $ foldl' (\a b -> Expr . Identity $ App a b) f xs

pPi :: Parser ParsedExpr
pPi = do
  _ <- parseToken TPi
  x <- pat
  _ <- parseToken TColon
  a <- pUExpr
  _ <- parseToken TDot
  b <- pUExpr
  pure $ Pi (maybe Wildcard (Id' . Name) x) a b

pLam :: Parser ParsedExpr
pLam = do
  _ <- parseToken TLambda
  x <- pat
  _ <- parseToken TDot
  rhs <- pUExpr
  pure $ Lam (maybe Wildcard (Id' . Name) x) rhs

pId :: Parser ParsedExpr
pId = do
  _ <- parseToken TId
  parens do
    x <- pUExpr
    _ <- parseToken TComma
    y <- pUExpr
    pure $ Id x y

pRefl :: Parser ParsedExpr
pRefl = do
  _ <- parseToken TRefl
  a <- parens pUExpr
  pure $ Refl a

pJ :: Parser ParsedExpr
pJ = do
  _ <- parseToken TJ
  parens do
    c <- pUExpr
    _ <- parseToken TComma
    t <- pUExpr
    _ <- parseToken TComma
    p <- pUExpr
    pure $ J c t p

pBottom :: Parser ParsedExpr
pBottom = parseToken TBottom $> Bottom

pAbsurd :: Parser ParsedExpr
pAbsurd = do
  _ <- parseToken TAbsurd
  a <- parens pUExpr
  pure $ Absurd a

pTop :: Parser ParsedExpr
pTop = parseToken TTop $> Top

pTT :: Parser ParsedExpr
pTT = parseToken TTT $> TT

pBool :: Parser ParsedExpr
pBool = parseToken TBool $> Bool

pTrue :: Parser ParsedExpr
pTrue = parseToken TTrue $> True'

pFalse :: Parser ParsedExpr
pFalse = parseToken TFalse $> False'

pIf :: Parser ParsedExpr
pIf = do
  _ <- parseToken TIf
  parens do
    m <- pUExpr
    _ <- parseToken TComma
    c <- pUExpr
    _ <- parseToken TComma
    t <- pUExpr
    _ <- parseToken TComma
    f <- pUExpr
    pure $ If m c t f

pDecl :: Parser (Decl PParsed)
pDecl = do
  _ <- parseToken SOL
  x <- name
  _ <- parseToken TColon
  ty <- pUExpr
  _ <- parseToken SOL
  term <- pUExpr
  pure $ Decl (Name x) ty term

pModule :: Parser (Module PParsed)
pModule = do
  decls <- many $ try pDecl
  expr <- optional (parseToken SOL *> pUExpr)
  eof
  pure $ Module decls expr

parseModule :: String -> [Token] -> Either (ParseErrorBundle [Token] Void) (Module PParsed)
parseModule = parse pModule
