{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE UndecidableInstances #-}

module Main where

import Control.Category ((>>>))
import Control.Monad.RWS.CPS (RWS, tell, censor, gets, modify', asks)
import Data.Functor.Identity (Identity)
import Data.IntMap.Strict (IntMap)
import Data.IntMap.Strict qualified as IM
import Data.Kind (Type)
import Data.List.NonEmpty (NonEmpty)
import Data.List.NonEmpty qualified as NE
import Data.Map.Strict (Map)
import Data.Map.Strict qualified as M
import Data.Monoid (Endo(..))
import Data.Text (Text)
import GHC.Natural (Natural)
import Data.Maybe (isNothing)
import Control.Monad (when)

type Parsed = Expr Maybe

type UVarOr = Either UVar

type Inferring = Expr UVarOr

type Unifiable = UVarOr Inferring

-- | Nonsense is an expression that didn't typecheck, but that has a certain type
newtype Nonsense = Nonsense Inferring

type Checked = Expr Identity

-- TODO remove?
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
  XXExpr Maybe = DataConCan'tHappen
  XXExpr (Either UVar) = Nonsense
  XXExpr Identity = DataConCan'tHappen

data Error
  -- source expr, expected type, actual type
  -- TODO add source location
  = TypeMismatch Parsed Inferring Inferring (NonEmpty UnificationFailure)
  | VarOutOfScope Id

-- TODO add details
data UnificationFailure = UnificationFailure

data TcState = TcState
  { nextUVar :: Int
  , subst :: IntMap Unifiable
  }

type TcM a = RWS (Map Id (UVarOr Inferring)) (DList Error) TcState a

type DList a = Endo [a]

emptyDList :: DList a
emptyDList = Endo id

silence :: TcM a -> TcM a
silence = censor $ const emptyDList

raise :: Error -> TcM ()
raise e = tell $ Endo (e :)

lookupVar :: Id -> TcM Unifiable
lookupVar i = do
  t <- asks (M.lookup i)
  when (isNothing t) . raise $ VarOutOfScope i
  -- pure $ fromMaybe (Left (UVar 0)) t
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
unifyInferring (Univ n) (Univ n')
  | n == n' = pure []
  | otherwise = pure [UnificationFailure]
-- Var t a == Var t' a' = t == t' && a == a'
-- a == b = raise $ UnificationError (IExpr a) (IExpr b)

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
  Var Nothing a -> do
    i <- gets (.nextUVar)
    pure (Var (Left (UVar i)) a)
  Var (Just t) a -> Var . Right <$> fillWithUVars t <*> pure a

-- TODO: termination checker
check :: Inferring -> Parsed -> TcM Inferring
check expected expr = case expr of
  Univ n -> unifyInferring expected (Univ (n + 1)) >>= failOrSucceedWith (Univ n)
  Var t a -> do
    varType <- asks (M.lookup a)
    case t of
      Just actual -> do
        tFilled <- fillWithUVars actual
        varErrors <- maybe (pure []) (unify (Right tFilled)) varType
        expectedErrors <- unifyInferring expected tFilled
        -- TODO possibly don't combine these into one error
        failOrSucceedWith (Var (Right expected) a) $ (varErrors ++ expectedErrors)
      Nothing -> failOrSucceedWith (Var (Right expected) a) =<< maybe (pure []) (unify (Right expected)) varType
  where 
    failOrSucceedWith :: Inferring -> [UnificationFailure] -> TcM Inferring
    failOrSucceedWith e = NE.nonEmpty >>> \case
      Nothing -> pure e
      Just f -> tcFail f

    tcFail f = do
      actual <- silence $ infer expr
      raise $ TypeMismatch expr expected actual f
      pure (XExpr $ Nonsense expected)

infer :: Parsed -> TcM Inferring
infer = \case
  Univ n -> pure (Univ n)

typeOf :: Inferring -> Inferring
typeOf = \case
  Univ n -> Univ (n + 1)

eval :: Checked -> Checked
eval u@(Univ _) = u

main :: IO ()
main = putStrLn "Hello, Haskell!"
