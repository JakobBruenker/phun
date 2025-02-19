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
  | TId
  | TRefl
  | TJ
  | TBottom
  | TAbsurd
  | TTop
  | TTT
  | TBool
  | TTrue
  | TFalse
  | TIf
  | TNat
  | TZero
  | TSucc
  | TNatInd
  | TColon
  | TDot
  | TComma
  | TArrow
  | SOL -- start of line
  deriving (Eq, Ord)

instance Show Token where
  show = \case
    TLParen -> "("
    TRParen -> ")"
    TIdent t -> T.unpack t
    TPi -> "Pi"
    TLambda -> "\\"
    TId -> "Id"
    TRefl -> "Refl"
    TJ -> "J"
    TBottom -> "⊥"
    TAbsurd -> "Absurd"
    TTop -> "⊤"
    TTT -> "TT"
    TBool -> "Bool"
    TTrue -> "True"
    TFalse -> "False"
    TIf -> "If"
    TNat -> "Nat"
    TZero -> "Zero"
    TSucc -> "Succ"
    TNatInd -> "NatInd"
    TColon -> ":"
    TDot -> "."
    TComma -> ","
    TArrow -> "→"
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
      (T.stripPrefix "Pi" -> Just rest) | endOfWord rest -> TPi <:> go rest
      (T.stripPrefix "Π" -> Just rest) -> TPi <:> go rest
      (T.stripPrefix "∏" -> Just rest) -> TPi <:> go rest
      (T.stripPrefix "\\" -> Just rest) -> TLambda <:> go rest
      (T.stripPrefix "λ" -> Just rest) -> TLambda <:> go rest
      (T.stripPrefix "Id" -> Just rest) | endOfWord rest -> TId <:> go rest
      (T.stripPrefix "Refl" -> Just rest) | endOfWord rest -> TRefl <:> go rest
      (T.stripPrefix "J" -> Just rest) | endOfWord rest -> TJ <:> go rest
      (T.stripPrefix "⊥" -> Just rest) -> TBottom <:> go rest
      (T.stripPrefix "Bottom" -> Just rest) | endOfWord rest -> TBottom <:> go rest
      (T.stripPrefix "Absurd" -> Just rest) | endOfWord rest -> TAbsurd <:> go rest
      (T.stripPrefix "⊤" -> Just rest) -> TTop <:> go rest
      (T.stripPrefix "Top" -> Just rest) | endOfWord rest -> TTop <:> go rest
      (T.stripPrefix "TT" -> Just rest) | endOfWord rest -> TTT <:> go rest
      (T.stripPrefix "Bool" -> Just rest) | endOfWord rest -> TBool <:> go rest
      (T.stripPrefix "True" -> Just rest) | endOfWord rest -> TTrue <:> go rest
      (T.stripPrefix "False" -> Just rest) | endOfWord rest -> TFalse <:> go rest
      (T.stripPrefix "If" -> Just rest) | endOfWord rest -> TIf <:> go rest
      (T.stripPrefix "Nat" -> Just rest) | endOfWord rest -> TNat <:> go rest
      (T.stripPrefix "Zero" -> Just rest) | endOfWord rest -> TZero <:> go rest
      (T.stripPrefix "Succ" -> Just rest) | endOfWord rest -> TSucc <:> go rest
      (T.stripPrefix "NatInd" -> Just rest) | endOfWord rest -> TNatInd <:> go rest
      (T.stripPrefix ":" -> Just rest) -> TColon <:> go rest
      (T.stripPrefix "." -> Just rest) -> TDot <:> go rest
      (T.stripPrefix "," -> Just rest) -> TComma <:> go rest
      (T.stripPrefix "->" -> Just rest) -> TArrow <:> go rest
      (T.stripPrefix "→" -> Just rest) -> TArrow <:> go rest
      _ | let (ident, rest) = T.span isIdentChar t', T.length ident > 0 -> TIdent ident <:> go rest
        | otherwise -> Left $ UnexpectedToken t'
      where
        isIdentChar c = isAlphaNum c || T.elem c "?_'"
        endOfWord = maybe True (not . isIdentChar . fst) . T.uncons

lexFile :: Text -> Either LexerError [Token]
lexFile = fmap concat . traverse lexLine . T.lines
