{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE UndecidableInstances #-}

module Main where

import Control.Monad (when)
import Control.Monad.RWS.CPS (RWS, tell, censor, gets, modify', asks)
import Data.Foldable (traverse_)
import Data.Functor ((<&>))
import Data.Functor.Identity (Identity (..))
import Data.IntMap.Strict (IntMap)
import Data.IntMap.Strict qualified as IM
import Data.List.NonEmpty (NonEmpty)
import Data.List.NonEmpty qualified as NE
import Data.Map.Strict (Map)
import Data.Map.Strict qualified as M
import Data.Maybe (isNothing)
import Data.Monoid (Endo(..))
import Data.Text (Text)
import GHC.Natural (Natural)
import Data.Kind (Type)

-- | LHS: Expr, RHS: Type
type Typed :: Pass -> Type -> Type
data Typed p e = e ::: UExpr (Typed p) p

type Parsed = UExpr Identity PParsed

type Inferring = UExpr (Typed PInferring) PInferring

type InferringExpr = Expr (Typed PInferring) PInferring

type Checked = UExpr (Typed PChecked) PChecked

-- | Unification Variables
newtype UVar = UVar {id :: Int} deriving Eq

instance Show UVar where
  show (UVar i) = "u" ++ show i

type Id = Text

data Pass = PParsed | PInferring | PChecked

type UExpr :: (Type -> Type) -> Pass -> Type
data UExpr f p where
  Univ :: Natural -> UExpr f p
  Expr :: (f (Expr f p)) -> UExpr f p
  UV :: UVar -> UExpr f PInferring
  Hole :: UExpr f PParsed

instance Show (f (Expr f p)) => Show (UExpr f p) where
  show (Univ n) = "Type" ++ show n
  show (Expr e) = show e
  show (UV u) = show u
  show Hole = "_"

type Expr :: (Type -> Type) -> Pass -> Type
data Expr f p where
  Nonsense :: Parsed -> Expr f PInferring -- ^ used to assign any type to any expression

  Var :: Id -> Expr f p
  App :: (f (UExpr f p)) -> (f (UExpr f p)) -> Expr f p -- ^ NB: This is x f, not f x

  -- Technically, anything below can be encoded with the above
  Void :: Expr f p
  Unit :: Expr f p
  TT :: Expr f p

instance Show (f (UExpr f p)) => Show (Expr f p) where
  show (Var i) = show i
  show (App x f) = show x ++ " " ++ show f
  show (Nonsense e) = show e
  show (Void) = "Void"
  show (Unit) = "Unit"
  show (TT) = "TT"

data Error
  -- TODO add source location
  = TypeMismatch Parsed Inferring Inferring (NonEmpty UnificationFailure)
  -- ^ source expr, expected type, actual type
  | VarOutOfScope Id

-- TODO add details
data UnificationFailure
  = Can'tUnifyTypes Inferring Inferring
  | Can'tUnifyExprs InferringExpr InferringExpr
  | Can'tUnifyVars Id Id
  | Can'tUnifyLevels Natural Natural
  | Can'tUnifyNonsense Parsed Parsed

data TcState = TcState
  { nextUVar :: Int
  , subst :: IntMap Inferring
  }

-- | Typechecker monad.
--
-- Reader: Map from variable names to their types
type TcM a = RWS (Map Id Inferring) (DList Error) TcState a

type DList a = Endo [a]

emptyDList :: DList a
emptyDList = Endo id

nullDList :: DList a -> Bool
nullDList (Endo f) = null (f [])

silence :: TcM a -> TcM a
silence = censor $ const emptyDList

raise :: Error -> TcM ()
raise e = tell $ Endo (e :)

lookupVar :: Id -> TcM Inferring
lookupVar i = do
  t <- asks (M.lookup i)
  when (isNothing t) . raise $ VarOutOfScope i
  case t of
    Nothing -> do
      raise $ VarOutOfScope i
      u <- freshUVar
      pure (UV u)
    Just t' -> pure t'

lookupUVar :: UVar -> TcM (Maybe Inferring)
lookupUVar u = IM.lookup u.id <$> gets (.subst)

-- | Get the most concrete type we have for a UVar
normalizeUVar :: UVar -> TcM Inferring
normalizeUVar v = do
  t <- lookupUVar v
  case t of
    Nothing -> pure (UV v)
    Just (UV v') -> normalizeUVar v' -- TODO maybe zonk in this case
    Just t' -> pure t'

class Normalize a where
  normalize :: a -> TcM a

instance Normalize InferringExpr where
  -- TODO we probably have to actually normalize the types here i.e. eval them, not just replace the UVars - Q: Can we ensure we only get normalizing terms here?
  normalize :: InferringExpr -> TcM InferringExpr
  normalize = \case
    Nonsense e -> pure (Nonsense e)

    Var a -> pure (Var a)
    App x f -> App <$> normalize x <*>  normalize f

    Void -> pure Void
    Unit -> pure Unit
    TT -> pure TT

instance Normalize u => Normalize (Typed PInferring u) where
  normalize :: Typed PInferring u -> TcM (Typed PInferring u)
  normalize (t ::: k) = do
    t' <- normalize t
    k' <- normalize k
    pure (t' ::: k')

instance Normalize Inferring where
  -- | Normalize all UVars in a type
  -- TODO maybe zonk here
  normalize :: Inferring -> TcM Inferring
  normalize = \case
    Univ n -> pure (Univ n)
    Expr e -> Expr <$> normalize e
    UV v -> normalizeUVar v

class Unify a where
  -- | Intended argument order: Expected, then actual (order is only relevant for error reporting)
  unify :: a -> a -> TcM [UnificationFailure]

instance Unify InferringExpr where
  unify :: InferringExpr -> InferringExpr -> TcM [UnificationFailure]
  unify = \cases
    (Nonsense e) (Nonsense e') -> pure [Can'tUnifyNonsense e e']

    (Var a) (Var a') -> pure [Can'tUnifyVars a a' | a /= a']
    (App x f) (App x' f') -> do
      xErrs <- unify x x'
      fErrs <- unify f f'
      pure $ xErrs <> fErrs

    Void Void -> pure []
    Unit Unit -> pure []
    TT TT -> pure []
    t t' -> pure [Can'tUnifyExprs t t']

instance Unify u => Unify (Typed PInferring u) where
  unify (t ::: k) (t' ::: k') = do
    kErrs <- unify k k'
    tErrs <- unify t t'
    pure $ kErrs <> tErrs

instance Unify Inferring where
-- TODO we might actually have to generate unification constraints and solve them when possible, because it might be that two types are equal but we don't know yet -- maybe not though 🤔
  unify :: Inferring -> Inferring -> TcM [UnificationFailure]
  unify = \cases
    (UV u) (UV u') | u == u' -> pure [] -- minor optimization: Only look up uvars if necessary
    u u' -> do
      t <- normalize u
      t' <- normalize u'
      go t t'
    where
      go :: Inferring -> Inferring -> TcM [UnificationFailure]
      go = \cases
        (Univ n) (Univ n') -> pure [Can'tUnifyLevels n n']
        (UV u) (UV u')
          | u == u' -> pure []
          | otherwise -> substUVar u' (UV u) >> pure [] -- order doesn't really matter, but it seems reasonable to take the expected as "ground truth"
        e (UV u') -> substUVar u' e >> pure []
        (UV u) e -> substUVar u e >> pure []
        (Expr t) (Expr t') -> unify t t'
        t t' -> pure [Can'tUnifyTypes t t']

-- TODO occurs check
substUVar :: UVar -> Inferring -> TcM ()
substUVar v t = modify' \s -> s{subst = IM.insert v.id t s.subst}

freshUVar :: TcM UVar
freshUVar = do
  i <- gets (.nextUVar)
  modify' \s -> s{nextUVar = i + 1}
  pure $ UVar i

-- TODO: termination checker
check :: Inferring -> Parsed -> TcM Inferring
check expected expr = case expr of
  Univ n -> do
    let uType = Univ (n + 1)
    errs <- unify expected uType
    case NE.nonEmpty errs of
      Nothing -> pure $ Univ n
      Just es -> do
        raise $ TypeMismatch expr expected uType es
        pure $ Expr (Nonsense expr ::: expected)
  Expr (Identity e) -> case e of
    Var a -> do
      varType <- lookupVar a
      tryUnify expr expected varType
      pure $ Expr (Var a ::: expected)
    App x f -> undefined -- TODO

    Void -> tryUnify expr expected (Univ 0) >> pure (Expr (Void ::: expected))
    Unit -> tryUnify expr expected (Univ 0) >> pure (Expr (Unit ::: expected))
    TT -> tryUnify expr expected (Expr (Unit ::: Univ 0)) >> pure (Expr (TT ::: expected))
  Hole -> UV <$> freshUVar -- XXX Is this right? It seems like we ignore the expected type. But maybe this will just always result in an unsolved uvar, which might be fine
  
tryUnify :: Parsed -> Inferring -> Inferring -> TcM ()
tryUnify expr expt act = unify expt act <&> NE.nonEmpty >>= traverse_ (raise . TypeMismatch expr expt act)

infer :: Parsed -> TcM Inferring
infer expr = case expr of
  Univ n -> pure $ Univ n
  Expr (Identity e) -> case e of
    Var a -> do
      varT <- lookupVar a
      pure (Expr $ Var a ::: varT)
    App x f -> undefined -- TODO

    Void -> pure (Expr $ Void ::: Univ 0)
    Unit -> pure (Expr $ Unit ::: Univ 0)
    TT -> pure (Expr $ TT ::: Expr (Unit ::: Univ 0))
  Hole -> UV <$> freshUVar

eval :: Checked -> Checked
eval = \case
  u@(Univ _) -> u
  Expr (e ::: t) -> Expr (e' ::: t)
    where
      e' = case e of
        Var a -> Var a
        App x f -> undefined -- TODO

        Void -> Void
        Unit -> Unit
        TT -> TT

main :: IO ()
main = putStrLn "Hello, Haskell!"
