{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE UndecidableInstances #-}

module Main where

import Control.Monad (when)
import Control.Monad.RWS.CPS (RWS, tell, censor, gets, modify', asks, MonadWriter (listen))
import Data.Foldable (traverse_)
import Data.Functor ((<&>))
import Data.Functor.Const (Const (..))
import Data.Functor.Identity (Identity)
import Data.IntMap.Strict (IntMap)
import Data.IntMap.Strict qualified as IM
import Data.Kind (Type)
import Data.List.NonEmpty (NonEmpty)
import Data.List.NonEmpty qualified as NE
import Data.Map.Strict (Map)
import Data.Map.Strict qualified as M
import Data.Maybe (isNothing)
import Data.Monoid (Endo(..))
import Data.Text (Text)
import GHC.Natural (Natural)

type Parsed = Expr (Const ())

type UVarOr = Either UVar

type Inferring = Expr UVarOr

type Unifiable = UVarOr Inferring

-- | Nonsense is an expression that didn't typecheck, but that has a certain type. Also carries the original expression.
data Nonsense f = Nonsense (f (Expr f)) Parsed

type Checked = Expr Identity

data SomeExpr
  = PExpr Parsed
  | IExpr Inferring
  | CExpr Checked

-- | Unification Variables
newtype UVar = UVar {id :: Int} deriving Eq

type Id = Text

type Expr :: (Type -> Type) -> Type
data Expr f
  = Univ Natural
  | Var (f (Expr f)) Id
  | XExpr (XXExpr f)

deriving instance (Show (f (Expr f)), Show (XXExpr f)) => Show (Expr f)

data DataConCan'tHappen deriving Show

type family XXExpr f where
  XXExpr (Const ()) = DataConCan'tHappen
  XXExpr (Either UVar) = Nonsense (Either UVar)
  XXExpr Identity = DataConCan'tHappen

data Error
  -- source expr, expected type, actual type
  -- TODO add source location
  = TypeMismatch Parsed Unifiable Unifiable (NonEmpty UnificationFailure)
  | VarOutOfScope Id

-- TODO add details
data UnificationFailure
  = Can'tUnifyTypes Inferring Inferring
  | Can'tUnifyVars Id Id
  | Can'tUnifyLevels Natural Natural

data TcState = TcState
  { nextUVar :: Int
  , subst :: IntMap Unifiable
  }

type TcM a = RWS (Map Id (UVarOr Inferring)) (DList Error) TcState a

type DList a = Endo [a]

emptyDList :: DList a
emptyDList = Endo id

nullDList :: DList a -> Bool
nullDList (Endo f) = null (f [])

silence :: TcM a -> TcM a
silence = censor $ const emptyDList

raise :: Error -> TcM ()
raise e = tell $ Endo (e :)

lookupVar :: Id -> TcM Unifiable
lookupVar i = do
  t <- asks (M.lookup i)
  when (isNothing t) . raise $ VarOutOfScope i
  case t of
    Nothing -> do
      raise $ VarOutOfScope i
      u <- freshUVar
      pure (Left u)
    Just t' -> pure t'

lookupUVar :: UVar -> TcM (Maybe Unifiable)
lookupUVar u = IM.lookup u.id <$> gets (.subst)

-- | Get the most concrete type we have for a UVar
normalizeUVar :: UVar -> TcM Unifiable
normalizeUVar v = do
  t <- lookupUVar v
  case t of
    Nothing -> pure (Left v)
    Just (Left v') -> normalizeUVar v' -- TODO maybe zonk in this case
    Just t' -> pure t'

normalizeUnifiable :: Unifiable -> TcM Unifiable
normalizeUnifiable = \case
  Left v -> normalizeUVar v
  Right t -> pure (Right t)

unifyInferring :: Inferring -> Inferring -> TcM [UnificationFailure]
unifyInferring = \cases
  (Univ n) (Univ n')
    | n == n' -> pure []
    | otherwise -> pure [Can'tUnifyLevels n n']
  (Var t a) (Var t' a') -> ([Can'tUnifyVars a a' | a /= a'] ++) <$> unify t t'
  -- If we have a nonsense expression, we must have already gotten a type error,
  -- so there's no point in reporting that we can't unify Nonsense with
  -- something. We still try to unify the kind, though
  (XExpr (Nonsense t _)) t' -> unify t (typeOf t')
  t (XExpr (Nonsense t' _)) -> unify (typeOf t) t'
  t t' -> pure [Can'tUnifyTypes t t']

-- TODO occurs check
substUVar :: UVar -> Unifiable -> TcM ()
substUVar v t = modify' \s -> s{subst = IM.insert v.id t s.subst}

-- | Intended argument order: Expected, then actual
unify :: Unifiable -> Unifiable -> TcM [UnificationFailure]
unify = \cases
  (Left u) (Left u') | u == u' -> pure [] -- minor optimization
  u u' -> do
    t <- normalizeUnifiable u
    t' <- normalizeUnifiable u'
    go t t'
  where
    go = \cases
      (Left u) (Left u')
        | u == u' -> pure []
        | otherwise -> substUVar u (Left u') >> pure []
      (Left u) (Right t') -> substUVar u (Right t') >> pure []
      (Right t) (Left u') -> substUVar u' (Right t) >> pure []
      (Right t) (Right t') -> unifyInferring t t'

freshUVar :: TcM UVar
freshUVar = do
  i <- gets (.nextUVar)
  modify' \s -> s{nextUVar = i + 1}
  pure $ UVar i

fillWithUVars :: Parsed -> TcM Inferring
fillWithUVars = \case
  Univ n -> pure (Univ n)
  Var _ a -> do
    u <- freshUVar
    pure (Var (Left u) a)

-- TODO: termination checker
check :: Inferring -> Parsed -> TcM Inferring
check expected expr = case expr of
  u@(Univ n) -> do
    (_, errs) <- listen $ tryUnifyInferring expr expected (Univ (n + 1))
    pure if nullDList errs
      then (Univ n)
      else XExpr (Nonsense (Right $ Univ (n + 1)) u)
  Var (Const ()) a -> do
    varType <- asks (M.lookup a)
    traverse_ (tryUnify expr (Right expected)) varType
    pure (Var (Right expected) a)
  
tryUnify :: Parsed -> Unifiable -> Unifiable -> TcM ()
tryUnify expr expt act = unify expt act <&> NE.nonEmpty >>= traverse_ (raise . TypeMismatch expr expt act)

tryUnifyInferring :: Parsed -> Inferring -> Inferring -> TcM ()
tryUnifyInferring expr expt act = unifyInferring expt act <&> NE.nonEmpty >>= traverse_ (raise . TypeMismatch expr (Right expt) (Right act))

infer :: Parsed -> TcM Inferring
infer expr = case expr of
  Univ n -> pure $ Univ n
  Var (Const ()) a -> do
    varT <- lookupVar a
    pure (Var varT a)
 
typeOf :: Inferring -> Unifiable
typeOf = \case
  Univ n -> Right $ Univ (n + 1)
  Var t _ -> t
  XExpr (Nonsense t _) -> t

eval :: Checked -> Checked
eval u@(Univ _) = u
eval v@(Var _ _) = v

main :: IO ()
main = putStrLn "Hello, Haskell!"
