module Main where

import Lexer
import Parser
import TC
import System.Environment (getArgs)
import Data.Text.IO qualified as T
import Text.Megaparsec.Error (errorBundlePretty)
import Data.List.NonEmpty qualified as NE
import Data.Foldable (for_)
import Control.Monad.Trans.Writer.CPS (runWriterT)
import System.IO (hPrint, stderr, hPutStrLn)
import Control.Monad.Reader (runReader)

main :: IO ()
main = do
  filename <- getArgs >>= \case
    [filename] -> pure filename
    _ -> error "Usage: phun <filename>"
  input <- case filename of
    "-" -> T.getContents
    _ -> T.readFile filename
  case parseModule filename (lexFile input) of
    Left err -> hPutStrLn stderr $ errorBundlePretty err
    Right md -> do
      -- debugging
      T.putStrLn input
      print md
      case runTcM $ checkModule md of
        (_, NE.nonEmpty -> Just errs) -> for_ errs (hPrint stderr)
        (Just mod'@(Module _ (Just expr)), _) -> do
          -- debugging
          putStrLn "printing eval'd expr"
          print . fst . flip runReader (extractDecls mod') . runWriterT $ eval @PChecked expr -- TODO actually M.empty is not right here, we need the decls
        _foo -> do
          -- debugging
          print _foo
          putStrLn "ok"
