module Parser where

import Text.Megaparsec hiding (Token)
import Data.Text (Text)
import Data.Void
import TC (Parsed, UExpr (..), ParsedExpr, Pass(..), Expr (..), Id (..), Decl (..), Module (..))
import Control.Comonad.Identity (Identity(..))
import Lexer
import qualified Data.Set as Set
import Data.Foldable (find)

type Parser = Parsec Void [Token]

parseTokenMatching :: (Token -> Bool) -> Parser Token
parseTokenMatching p = token (find p . Just) Set.empty

parseToken :: Token -> Parser Token
parseToken = parseTokenMatching . (==)

parens :: Parser a -> Parser a
parens = between (parseToken TLParen) (parseToken TRParen)

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
  , Hole <$ parseToken THole
  , parens pUExpr
  ]

pUniv :: Parser Parsed
pUniv = do
  TType n <- parseTokenMatching \case TType _ -> True; _ -> False
  pure (Univ n)

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

identifier :: Parser Text
identifier = do
  TIdent name <- parseTokenMatching \case
    TIdent _ -> True
    _ -> False
  pure name

pApp :: Parser ParsedExpr
pApp = App <$> pUExprNoApp <*> pUExpr

pPi :: Parser ParsedExpr
pPi = do
  _ <- parseToken TPi
  x <- identifier
  _ <- parseToken TColon
  a <- pUExpr
  _ <- parseToken TDot
  b <- pUExpr
  pure $ Pi (Name x) a b

pLam :: Parser ParsedExpr
pLam = do
  _ <- parseToken TLambda
  x <- identifier
  _ <- parseToken TDot
  rhs <- pUExpr
  pure $ Lam (Name x) rhs

pVar :: Parser ParsedExpr
pVar = Var . Name <$> identifier

pDecl :: Parser (Decl PParsed)
pDecl = do
  _ <- parseToken SOL
  x <- identifier
  _ <- parseToken TColon
  ty <- pUExpr
  _ <- parseToken SOL
  term <- pUExpr
  pure $ Decl (Name x) ty term

pModule :: Parser (Module PParsed)
pModule = do
  decls <- many $ try pDecl
  _ <- parseToken SOL
  expr <- pUExpr
  eof
  pure $ Module decls $ Just expr

parseModule :: String -> [Token] -> Either (ParseErrorBundle [Token] Void) (Module PParsed)
parseModule = parse pModule
