module Main where

import Parser
import TC
import System.Environment (getArgs)
import Data.Text.IO qualified as T
import Text.Megaparsec.Error (errorBundlePretty)
import qualified Data.List.NonEmpty as NE
import Data.Foldable (for_)
import Control.Monad.Trans.Writer.CPS (runWriter)

main :: IO ()
main = do
  filename <- getArgs >>= \case
    [filename] -> pure filename
    _ -> error "Usage: phun <filename>"
  input <- case filename of
    "-" -> T.getContents
    _ -> T.readFile filename
  md <- case parseModule filename input of
    Left err -> error $ errorBundlePretty err
    Right md -> pure md
  case runTcM $ checkModule md of
    (_, NE.nonEmpty -> Just errs) -> for_ errs print
    (Just expr, _) -> print . fst . runWriter $ eval expr
    _ -> putStrLn "ok"
