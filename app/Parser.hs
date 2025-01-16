module Parser where

import Text.Megaparsec hiding (Token)
import Data.Text (Text)
import Data.Void
import TC (Parsed, UExpr (..), ParsedExpr, Pass(..), Expr (..), Id (..), Decl (..), Module (..))
import Control.Comonad.Identity (Identity(..))
import Lexer
import Data.Set qualified as Set
import Data.Foldable (find)
import Data.Char (ord, chr, isDigit)
import Data.Text qualified as T
import Numeric.Natural (Natural)
import Data.Functor ((<&>))

type Parser = Parsec Void [Token]

parseTokenMatching :: (Token -> Bool) -> Parser Token
parseTokenMatching p = token (find p . Just) Set.empty

parseToken :: Token -> Parser Token
parseToken = parseTokenMatching . (==)

parens :: Parser a -> Parser a
parens = between (parseToken TLParen) (parseToken TRParen)

pUExpr :: Parser Parsed
pUExpr = choice
  [ Expr . Identity <$> pExprNoVar
  , pOtherUExpr
  ]

pUExprNoApp :: Parser Parsed
pUExprNoApp = choice
  [ Expr . Identity <$> pExprNoAppOrVar
  , pOtherUExpr
  ]

pOtherUExpr :: Parser Parsed
pOtherUExpr = choice
  [ pVarOrUnivOrHole
  , parens pUExpr
  ]

pExprNoVar :: Parser ParsedExpr
pExprNoVar = choice
  [ try pApp
  , pExprNoAppOrVar
  ]

pExprNoAppOrVar :: Parser ParsedExpr
pExprNoAppOrVar = choice
  [ pPi
  , pLam
  ]

pVarOrUnivOrHole :: Parser Parsed
pVarOrUnivOrHole = identifier <&> \case
  IVar x -> Expr . Identity . Var $ Name x
  IUniv n -> Univ n
  IHole -> Hole

data Identifier = IUniv Natural | IHole | IVar Text
  deriving (Show, Eq, Ord)

identifier :: Parser Identifier
identifier = do
  TIdent name <- parseTokenMatching \case
    TIdent _ -> True
    _ -> False
  pure $ disambiguateIdentifier name
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

pat :: Parser Text
pat = identifier >>= \case
  IVar t -> pure t
  -- IHole -> pure Nothing -- A hole is treated as wildcard in pattern context -- TODO
  IHole -> error "not implemented"
  IUniv _ -> fail $ "Expected variable name or wildcard, got a universe"

pApp :: Parser ParsedExpr
pApp = App <$> pUExprNoApp <*> pUExpr

pPi :: Parser ParsedExpr
pPi = do
  _ <- parseToken TPi
  x <- pat
  _ <- parseToken TColon
  a <- pUExpr
  _ <- parseToken TDot
  b <- pUExpr
  pure $ Pi (Name x) a b

pLam :: Parser ParsedExpr
pLam = do
  _ <- parseToken TLambda
  x <- pat
  _ <- parseToken TDot
  rhs <- pUExpr
  pure $ Lam (Name x) rhs

pDecl :: Parser (Decl PParsed)
pDecl = do
  _ <- parseToken SOL
  x <- pat
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
