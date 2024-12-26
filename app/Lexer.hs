module Lexer where

import Data.Text (Text)
import Data.Text qualified as T
import Data.Char (isSpace, isDigit, chr, ord, isAlphaNum)
import Data.Foldable (toList, find)
import Numeric.Natural (Natural)
import Data.Maybe (fromMaybe)
import Text.Megaparsec.Stream (VisualStream(..), TraversableStream(..))
import Data.List (intercalate)

data Token
  = TLParen
  | TRParen
  | TIdent Text
  | TType Natural
  | TPi
  | TLambda
  | TColon
  | TDot
  | THole
  | SOL -- start of line
  deriving (Eq, Ord)

instance Show Token where
  show = \case
    TLParen -> "("
    TRParen -> ")"
    TIdent t -> T.unpack t
    TType n -> "Type" <> show n
    TPi -> "Pi"
    TLambda -> "\\"
    TColon -> ":"
    TDot -> "."
    THole -> "_"
    SOL -> "\n"

instance VisualStream [Token] where
  showTokens _ stream = intercalate " " $ map show $ toList stream

instance TraversableStream [Token] where
  reachOffset _ ps = (Nothing, ps) -- TODO

lexLine :: Text -> [Token]
lexLine t = toList mEol <> go t
  where
    mEol :: Maybe Token
    mEol = SOL <$ (find (not . isSpace) . fmap fst $ T.uncons t)
    go (T.stripStart -> t') = case t' of
      _ | "--" `T.isPrefixOf` t' || T.null t' -> []
      (T.stripPrefix "(" -> Just rest) -> TLParen : go rest
      (T.stripPrefix ")" -> Just rest) -> TRParen : go rest
      (T.stripPrefix "Pi" -> Just rest) -> TPi : go rest
      (T.stripPrefix "Π" -> Just rest) -> TPi : go rest
      (T.stripPrefix "∏" -> Just rest) -> TPi : go rest
      (T.stripPrefix "\\" -> Just rest) -> TLambda : go rest
      (T.stripPrefix "λ" -> Just rest) -> TLambda : go rest
      (T.stripPrefix ":" -> Just rest) -> TColon : go rest
      (T.stripPrefix "." -> Just rest) -> TDot : go rest
      (T.stripPrefix "_" -> Just rest) -> THole : go rest
      _ | otherwise -> case T.span isAlphaNum t' of
          (ident, rest) -> fromMaybe (TIdent ident) (getType ident) : go rest
    getType :: Text -> Maybe Token
    getType = \case
      (T.stripPrefix "Type" -> Just rest) | let index = T.takeWhile (not . isSpace) rest -> case T.unpack index of
        "" -> Just $ TType 0
        i | T.all isDigit index -> Just $ TType $ read i
          | T.all (`elem` ['₀'..'₉']) index -> Just $ TType $ read $ map subscriptToDigit $ T.unpack index
        _ -> Nothing
      _ -> Nothing
    subscriptToDigit c = chr (ord c - ord '₀' + ord '0')

lexFile :: Text -> [Token]
lexFile = concat . fmap lexLine . T.lines
