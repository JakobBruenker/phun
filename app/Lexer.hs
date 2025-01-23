module Lexer where

import Data.Text (Text)
import Data.Text qualified as T
import Data.Foldable (toList)
import Data.Maybe (fromMaybe)
import Text.Megaparsec.Stream (VisualStream(..), TraversableStream(..))
import Data.List (intercalate)
import Data.Char (isSpace, isAlphaNum)

data Token
  = TLParen
  | TRParen
  | TIdent Text
  | TPi
  | TLambda
  | TColon
  | TDot
  | SOL -- start of line
  deriving (Eq, Ord)

instance Show Token where
  show = \case
    TLParen -> "("
    TRParen -> ")"
    TIdent t -> T.unpack t
    TPi -> "Pi"
    TLambda -> "\\"
    TColon -> ":"
    TDot -> "."
    SOL -> "\n<SOL>"

instance VisualStream [Token] where
  showTokens _ stream = intercalate " " $ map show $ toList stream

instance TraversableStream [Token] where
  reachOffset _ ps = (Nothing, ps) -- TODO

data LexerError = UnexpectedToken Text deriving Show

-- If the line is not a comment and begins with a non-space character, this counts as the "start of a line", and a SOL token is emitted.
-- This makes it so the current syntactical construct continues while the code is indented, or in other words, indentation escapes the preceding newline.
lexLine :: Text -> Either LexerError [Token]
lexLine t = (toList mSol <>) <$> go t
  where
    mSol :: Maybe Token
    mSol = [ SOL | not (isComment || beginsWithSpace) ]
      where isComment = "--" `T.isPrefixOf` t
            beginsWithSpace = fromMaybe True $ fmap (isSpace . fst) $ T.uncons t

    go :: Text -> Either LexerError [Token]
    go (T.stripStart -> t') = let (<:>) = (<$>) . (:) in case t' of
      _ | "--" `T.isPrefixOf` t' || T.null t' -> Right []
      (T.stripPrefix "(" -> Just rest) -> TLParen <:> go rest
      (T.stripPrefix ")" -> Just rest) -> TRParen <:> go rest
      (T.stripPrefix "Pi" -> Just rest) -> TPi <:> go rest
      (T.stripPrefix "Π" -> Just rest) -> TPi <:> go rest
      (T.stripPrefix "∏" -> Just rest) -> TPi <:> go rest
      (T.stripPrefix "\\" -> Just rest) -> TLambda <:> go rest
      (T.stripPrefix "λ" -> Just rest) -> TLambda <:> go rest
      (T.stripPrefix ":" -> Just rest) -> TColon <:> go rest
      (T.stripPrefix "." -> Just rest) -> TDot <:> go rest
      _ | let (ident, rest) = T.span (\c -> isAlphaNum c || T.elem c "?_'" ) t', T.length ident > 0 -> TIdent ident <:> go rest
        | otherwise -> Left $ UnexpectedToken t'

lexFile :: Text -> Either LexerError [Token]
lexFile = fmap concat . traverse lexLine . T.lines
