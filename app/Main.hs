{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE UndecidableInstances #-}

module Main where

import Control.Monad (when, (>=>))
import Control.Monad.RWS.CPS (RWS, tell, censor, gets, modify', asks, runRWS)
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
import Data.Function ((&))
import Data.Char (chr, ord)
import qualified Data.Text as T
import Control.Monad.Trans.Maybe (MaybeT(..))
import Control.Monad.Reader (Reader, MonadReader (..))

-- | LHS: Expr, RHS: Type
type Typed :: Pass -> Type -> Type
data Typed p e = e ::: UExpr (Typed p) p

deriving instance Show e => Show (Typed f e)

type Parsed = UExpr Identity PParsed

type Inferring = UExpr (Typed PInferring) PInferring

type InferringExpr = Expr (Typed PInferring) PInferring

type Checked = UExpr (Typed PChecked) PChecked

-- | Unification Variables
newtype UVar = UVar {id :: Int} deriving Eq

instance Show UVar where
  show (UVar i) = "υ" ++ ['₋' | i < 0] ++  showNaturalSubscript (fromIntegral (abs i))

showNaturalSubscript :: Natural -> String
showNaturalSubscript = map toSubscript . show
  where
    toSubscript c = chr (ord c - ord '0' + ord '₀')

data Id = Name Text | Uniq Unique deriving (Eq, Ord)

-- | Gets the user-defined name of an identifier, if it has one
userName :: Id -> Maybe Text
userName (Name n) = Just n
userName _ = Nothing

data Unique = Unique
  { id :: Natural
  , tag :: Maybe Text -- ^ Typically used if the unique replaces a user-defined name
  }

instance Eq Unique where
  Unique n _ == Unique n' _ = n == n'

instance Ord Unique where
  compare (Unique n _) (Unique n' _) = compare n n'

tagUnique :: Unique -> Text -> Unique
tagUnique (Unique n _) name = Unique n (Just name)

instance Show Id where
  show (Name name) = T.unpack name
  show (Uniq (Unique n name)) = maybe uniq (\n' -> T.unpack n' ++ "_" ++ uniq) name
    where
      uniq = "q" ++ showNaturalSubscript n

data Pass = PParsed | PInferring | PChecked

type UExpr :: (Type -> Type) -> Pass -> Type
data UExpr f p where
  Univ :: Natural -> UExpr f p
  -- TODO add a flag showing if the Expr has been reduced
  Expr :: (f (Expr f p)) -> UExpr f p -- ^ keeps track of free variables
  UV :: UVar -> UExpr f PInferring
  Hole :: UExpr f PParsed

instance Show (f (Expr f p)) => Show (UExpr f p) where
  show (Univ n) = "Type" ++ showNaturalSubscript n
  show (Expr e) = "(" ++ show e ++ ")"
  show (UV u) = show u
  show Hole = "_"

type Expr :: (Type -> Type) -> Pass -> Type
data Expr f p where
  Nonsense :: Parsed -> Expr f PInferring -- ^ used to assign any type to any expression

  Var :: Id -> Expr f p
  App :: (UExpr f p) -> (UExpr f p) -> Expr f p -- ^ NB: This is x f, not f x
  Pi :: Id -> (UExpr f p) -> (UExpr f p) -> Expr f p

  -- Technically, anything below can be encoded with the above
  Bottom :: Expr f p
  Top :: Expr f p
  TT :: Expr f p

instance Show (f (Expr f p)) => Show (Expr f p) where
  show (Nonsense e) = show e

  show (Var i) = show i
  show (App x f) = ("(" ++ show x ++ " " ++ show f ++ ")")
  show (Pi i t b) = "Π" ++ show i ++ ":" ++ show t ++ "." ++ show b

  show (Bottom) = "⊥"
  show (Top) = "⊤"
  show (TT) = "tt"

data Error
  -- TODO add source location
  = TypeMismatch Parsed Inferring Inferring (NonEmpty UnificationFailure)
  -- ^ source expr, expected type, actual type
  | VarOutOfScope Id
  deriving Show

-- TODO add details
data UnificationFailure
  = Can'tUnifyTypes Inferring Inferring
  | Can'tUnifyExprs InferringExpr InferringExpr
  | Can'tUnifyVars Id Id
  | Can'tUnifyLevels Natural Natural
  | Can'tUnifyNonsense Parsed Parsed
  deriving Show

data TcState = TcState
  { nextUVar :: Int
  , nextUnique :: Natural
  , subst :: IntMap Inferring
  }

type Vars a = Map Id a

-- | Typechecker monad.
--
-- Reader: Map from variable names to their types
type TcM a = RWS (Vars Inferring) (DList Error) TcState a

type DList a = Endo [a]

emptyDList :: DList a
emptyDList = Endo id

nullDList :: DList a -> Bool
nullDList (Endo f) = null (f [])

dListToList :: DList a -> [a]
dListToList (Endo f) = f []

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

-- | Get the most concrete representation we have for a UVar
normalizeUVar :: UVar -> TcM Inferring
normalizeUVar v = do
  t <- lookupUVar v
  case t of
    Nothing -> pure (UV v)
    Just (UV v') -> normalizeUVar v' -- TODO maybe zonk in this case
    Just t' -> pure t'

withBinding :: MonadReader (Vars v) m => Id -> v -> m a -> m a
withBinding i t = local (M.insert i t)

class Normalize a where
  normalize :: a -> TcM a

instance Normalize InferringExpr where
  -- TODO we probably have to actually normalize here i.e. eval the exprs, not just replace the UVars - Q: Can we ensure we only get strongly normalizing terms here?
  normalize :: InferringExpr -> TcM InferringExpr
  normalize = \case
    Nonsense e -> pure (Nonsense e)

    Var a -> pure (Var a)
    App x f -> App <$> normalize x <*>  normalize f
    Pi i t b -> Pi i <$> normalize t <*> normalize b

    Bottom -> pure Bottom
    Top -> pure Top
    TT -> pure TT

instance Normalize u => Normalize (Typed PInferring u) where
  normalize :: Typed PInferring u -> TcM (Typed PInferring u)
  normalize (t ::: k) = do
    t' <- normalize t
    k' <- normalize k
    pure (t' ::: k')

instance Normalize Inferring where
  -- | Normalize all UVars in a type
  -- TODO maybe zonk here - although I'm not sure it makes much sense because we don't always keep this result
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
    (Pi x t a) (Pi x' t' b) -> do
      v <- freshUnique Nothing
      tErrs <- unify t t'
      -- TODO do we need to add x, x' to the context?
      a' <- rename x (Uniq v{tag = userName x}) a
      b' <- rename x' (Uniq v{tag = userName x'}) b
      eErrs <- unify a' b'
      pure $ tErrs <> eErrs

    Bottom Bottom -> pure []
    Top Top -> pure []
    TT TT -> pure []
    t t' -> pure [Can'tUnifyExprs t t']

instance Unify u => Unify (Typed PInferring u) where
  unify (t ::: k) (t' ::: k') = do
    kErrs <- unify k k'
    tErrs <- unify t t'
    pure $ kErrs <> tErrs

-- TODO I feel like one issue is going to be that unify renames a var locally, assigns that renamed var to a uvar, and then we get confused once it's used outside. Maybe we need to keep track of the original name and use that for lookups, and the new name only for unification or something? but this might also require assigning a unique to *all* ids in the parsing step
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
        (Univ n) (Univ n') -> pure [Can'tUnifyLevels n n' | n /= n']
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

freshUnique :: Maybe Text -> TcM Unique
freshUnique name = do
  u <- gets (.nextUnique)
  modify' \s -> s{nextUnique = u + 1}
  pure $ Unique u name

class Zonk a where
  zonk :: a -> TcM a

instance Zonk Inferring where
  zonk = \case
    Univ n -> pure (Univ n)
    Expr e -> Expr <$> zonk e
    UV u -> normalizeUVar u

instance Zonk u => Zonk (Typed PInferring u) where
  zonk (t ::: k) = (:::) <$> zonk t <*> zonk k

instance Zonk InferringExpr where
  zonk = \case
    Nonsense e -> pure (Nonsense e)

    Var a -> pure (Var a)
    App x f -> App <$> zonk x <*> zonk f
    Pi i t b -> Pi i <$> zonk t <*> zonk b

    Bottom -> pure Bottom
    Top -> pure Top
    TT -> pure TT

class Rename a where
  rename' :: Id -> Id -> a -> TcM a

instance Rename InferringExpr where
  rename' orig new = \case
    Nonsense e -> pure (Nonsense e)

    Var a -> pure (Var (if a == orig then new else a))
    App x f -> App <$> rename' orig new x <*> rename' orig new f
    Pi i t b -> Pi i <$> rename' orig new t <*> rename' orig new b

    Bottom -> pure Bottom
    Top -> pure Top
    TT -> pure TT

instance Rename u => Rename (Typed PInferring u) where
  rename' orig new (t ::: k) = (:::) <$> rename' orig new t <*> rename' orig new k

instance Rename Inferring where
  rename' orig new = \case
    Univ n -> pure (Univ n)
    Expr e -> Expr <$> rename' orig new e
    UV u -> pure (UV u)

-- | Renames all occurrences of a variable in an expression, zonking first to make sure
-- that if the name occurs in a UVar, we can change it without having to change
-- the global UVar mapping (Not 100% sure this is necessary)
rename :: (Rename a, Zonk a) => Id -> Id -> a -> TcM a
rename orig new = zonk >=> rename' orig new

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

    Bottom -> tryUnify expr expected (Univ 0) >> pure (Expr (Bottom ::: expected))
    Top -> tryUnify expr expected (Univ 0) >> pure (Expr (Top ::: expected))
    TT -> tryUnify expr expected (Expr (Top ::: Univ 0)) >> pure (Expr (TT ::: expected))
  Hole -> UV <$> freshUVar -- XXX Is this right? It seems like we ignore the expected type. But maybe this will just always result in an unsolved uvar, which might be fine
  
tryUnify :: Parsed -> Inferring -> Inferring -> TcM ()
tryUnify expr expt act = unify expt act <&> NE.nonEmpty >>= traverse_ (raise . TypeMismatch expr expt act)

level :: Inferring -> TcM (Maybe Natural)
level = \case
  Univ n -> pure $ Just n
  Expr (_ ::: t) -> runMaybeT [ l - 1 | l <- MaybeT (level t), l > 0 ]
  UV u -> normalizeUVar u >>= \case
    UV _ -> pure Nothing -- Users might need to specify levels for universes if they're higher than 0
    t -> level t

infer :: Parsed -> TcM Inferring
infer expr = case expr of
  Univ n -> pure $ Univ n
  Expr (Identity e) -> case e of
    Var a -> do
      varT <- lookupVar a
      pure (Expr $ Var a ::: varT)
    App x f -> undefined -- TODO
    Pi x a b -> do
      a' <- infer a
      b' <- withBinding x a' $ infer b
      lvl <- maybe 0 (+1) <$> (max <$> level a' <*> level b')
      pure (Expr $ Pi x a' b' ::: Univ lvl)

    Bottom -> pure (Expr $ Bottom ::: Univ 0)
    Top -> pure (Expr $ Top ::: Univ 0)
    TT -> pure (Expr $ TT ::: Expr (Top ::: Univ 0))
  Hole -> UV <$> freshUVar

eval :: Checked -> Reader (Vars Checked) Checked
eval = \case
  u@(Univ _) -> pure u
  Expr (e ::: t) -> do
    e' <- case e of
      Var a -> pure $ Var a
      App x f -> undefined -- TODO
      Pi x a b -> do
        a' <- eval a
        b' <- withBinding x a' $ eval b
        pure (Pi x a' b')

      Bottom -> pure Bottom
      Top -> pure Top
      TT -> pure TT
    pure $ Expr (e' ::: t)
    where

runTcM :: TcM a -> (a, [Error])
runTcM action = runRWS action M.empty (TcState 0 0 IM.empty) & \case
  (a, _, w) -> (a, dListToList w)

main :: IO ()
main = putStrLn "Hello, Haskell!"
