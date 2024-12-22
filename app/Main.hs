{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE AllowAmbiguousTypes #-}

module Main where

import Control.Monad (when, (>=>), join)
import Control.Monad.Reader (Reader, MonadReader (..))
import Control.Monad.RWS.CPS (RWS, tell, censor, gets, modify', asks, runRWS)
import Control.Monad.Trans.Class (lift)
import Control.Monad.Trans.Maybe (MaybeT(..))
import Control.Monad.Trans.Writer.CPS (WriterT)
import Control.Monad.Trans.Writer.CPS qualified as W
import Data.Bifunctor (second)
import Data.Char (chr, ord)
import Data.Foldable (traverse_)
import Data.Function ((&))
import Data.Functor (($>))
import Data.Functor.Identity (Identity (..))
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
import Data.Type.Equality ((:~:) (..))
import Data.Void (Void, absurd)
import GHC.Natural (Natural)
import qualified Data.Text as T

-- | LHS: Expr, RHS: Type
type Typed :: Pass -> Type -> Type
data Typed p e = e ::: UExpr (Typed p) p

deriving instance Show e => Show (Typed f e)

type Parsed = UExpr Identity PParsed

type Inferring = UExpr (Typed PInferring) PInferring

type InferringExpr = Expr (Typed PInferring) PInferring

type Checked = UExpr (Typed PChecked) PChecked

-- | Unification Variables
type UVar' :: Pass -> Type
data UVar' p where
  UVar :: {id :: Int} -> UVar' PInferring

type UVar = UVar' PInferring

deriving instance Eq (UVar' p)

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
  | LevelMismatch Parsed Natural Natural
  -- ^ source expr, expected level, actual level
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
type TcM = RWS (Vars Inferring) (DList Error) TcState

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
raise = tell . Endo . (:)

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

raiseUnif :: UnificationFailure -> WriterT (DList UnificationFailure) TcM ()
raiseUnif = W.tell . Endo . (:)

class Unify a where
  -- | Intended argument order: Expected, then actual
  unify' :: a -> a -> WriterT (DList UnificationFailure) TcM a

-- TODO probably reduce here? To avoid trying to reduce on every recursive call of unify'
-- TODO Q: What happens if e.g. in App we unify left side first, but actually right side contains information we need to successfully unify left side?
unify :: Inferring -> Inferring -> TcM (Inferring, [UnificationFailure])
unify e e' = second dListToList <$> W.runWriterT (unify' e e')

instance Unify InferringExpr where
  unify' = \cases
    (Nonsense e) (Nonsense e') -> raiseUnif (Can'tUnifyNonsense e e') *> pure (Nonsense e)

    (Var a) (Var a') -> when (a /= a') (raiseUnif $ Can'tUnifyVars a a') *> pure (Var a)
    -- TODO: for app we might want to only try to unify f and x if one of the f's is fully reduced (no uvars) - keep has uvars flag in uexpr?
    (App x f) (App x' f') -> App <$> unify' x x' <*> unify' f f' -- XXX Does the order in which we unify x vs f matter? (probably not if ^ TODO is implemented)
    (Pi x a b) (Pi x' a' b') -> do
      a'' <- unify' a a'
      u <- lift $ freshUnique Nothing
      let uniq = Uniq u{tag = userName x}
      -- TODO do we need to add x, x' to the context?
      b'' <- join $ unify' <$> lift (rename x uniq b) <*> lift (rename x' uniq b')
      pure $ Pi uniq a'' b''

    Bottom Bottom -> pure Bottom
    Top Top -> pure Top
    TT TT -> pure TT
    t t' -> raiseUnif (Can'tUnifyExprs t t') *> pure t

instance Unify u => Unify (Typed PInferring u) where
  unify' (t ::: k) (t' ::: k') = do
    k'' <- unify' k k'
    t'' <- unify' t t'
    pure $ t'' ::: k''


instance Unify Inferring where
-- TODO we might actually have to generate unification constraints and solve them when possible, because it might be that two types are equal but we don't know yet -- maybe not though 🤔
  unify' = \cases
    (UV u) (UV u') | u == u' -> pure $ UV u -- minor optimization: Only look up uvars if necessary
    u u' -> join $ go <$> lift (normalize u) <*> lift (normalize u')
    where
      go :: Inferring -> Inferring -> WriterT (DList UnificationFailure) TcM Inferring
      go = \cases
        (Univ n) (Univ n') -> when (n /= n) (raiseUnif $ Can'tUnifyLevels n n') *> pure (Univ n)
        (UV u) (UV u')
          | u == u' -> pure (UV u)
          | otherwise -> lift (substUVar u' (UV u)) >> pure (UV u) -- order doesn't really matter, but it seems reasonable to take the expected as "ground truth"
        e (UV u') -> lift (substUVar u' e) >> pure e
        (UV u) e -> lift (substUVar u e) >> pure e
        (Expr t) (Expr t') -> Expr <$> unify' t t'
        t t' -> raiseUnif (Can'tUnifyTypes t t') *> pure t

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
    (ty, errs) <- unify expected $ Univ (n + 1)
    case NE.nonEmpty errs of
      Nothing -> pure $ Univ n
      Just es -> do
        raise $ TypeMismatch expr expected uType es
        pure $ Expr (Nonsense expr ::: ty)
  Expr (Identity e) -> case e of
    Var a -> do
      varType <- lookupVar a
      ty <- tryUnify expr expected varType
      pure $ Expr (Var a ::: ty)
    App x f -> undefined -- TODO
    Pi x a b -> do
      a' <- infer a
      b' <- withBinding x a' $ infer b
      lvl <- maybe 0 (+1) <$> (max <$> inferLevel a' <*> inferLevel b')
      case expected of
        Univ n -> do
          when (lvl /= n) $ raise $ LevelMismatch expr n lvl
          pure $ Expr (Pi x a' b' ::: Univ n)
        _ -> do
          raise $ TypeMismatch expr expected (Univ lvl) (Can'tUnifyTypes expected (Univ lvl) NE.:| [])
          pure $ Expr (Nonsense expr ::: expected)

    Bottom -> Expr . (Bottom :::) <$> tryUnify expr expected (Univ 0)
    Top -> Expr . (Top :::) <$> tryUnify expr expected (Univ 0)
    TT -> Expr . (TT :::) <$> tryUnify expr expected (Expr (Top ::: Univ 0))
  Hole -> UV <$> freshUVar -- XXX Is this right? It seems like we ignore the expected type. But maybe this will just always result in an unsolved uvar, which might be fine. Otherwise, possibly UVars need to be able to optionally have types
  
tryUnify :: Parsed -> Inferring -> Inferring -> TcM Inferring
tryUnify expr expt act = do
  (expr', errs) <- unify expt act
  traverse_ (raise . TypeMismatch expr expt act) (NE.nonEmpty errs) $> expr'

inferLevel :: Inferring -> TcM (Maybe Natural)
inferLevel = \case
  Univ n -> pure $ Just n
  Expr (_ ::: t) -> runMaybeT [ l - 1 | l <- MaybeT (inferLevel t), l > 0 ]
  UV u -> normalizeUVar u >>= \case
    -- XXX what actually happens though if this uvar is later filled with something that has a higher level? Seems problematic. We might need a max or exact level on uvars
    UV _ -> pure Nothing -- Users might need to specify levels for universes if they're higher than 0
    t -> inferLevel t

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
      lvl <- maybe 0 (+1) <$> (max <$> inferLevel a' <*> inferLevel b')
      pure (Expr $ Pi x a' b' ::: Univ lvl)

    Bottom -> pure (Expr $ Bottom ::: Univ 0)
    Top -> pure (Expr $ Top ::: Univ 0)
    TT -> pure (Expr $ TT ::: Expr (Top ::: Univ 0))
  Hole -> UV <$> freshUVar

class Eval p where
  type PassMonad p :: Type -> Type
  type UVarResult p :: Type
  eval :: (m ~ PassMonad p, MonadReader (Vars e) m, e ~ UExpr (Typed p) p) => e -> m e
  provideUVar :: UVar' p -> (PassMonad p) (UVarResult p)
  evalTypes :: Bool

instance Eval PInferring where
  type PassMonad PInferring = TcM
  type UVarResult PInferring = Inferring
  eval = eval' \case
  provideUVar = normalizeUVar
  evalTypes = True

instance Eval PChecked where
  type PassMonad PChecked = Reader (Vars Checked)
  type UVarResult PChecked = Checked
  eval = eval' \case
  provideUVar = \case
  evalTypes = False

{-# SPECIALIZE eval' :: (PInferring :~: PParsed -> Void) -> Inferring -> TcM Inferring #-}
{-# SPECIALIZE eval' :: (PChecked :~: PParsed -> Void) -> Checked -> Reader (Vars Checked) Checked #-}
eval' :: (Eval p, m ~ PassMonad p, MonadReader (Vars e) m, e ~ UExpr (Typed p) p) => (p :~: PParsed -> Void) -> e -> m e
eval' @p notParsed = \case
  u@(Univ _) -> pure u
  Expr (e ::: t) -> do
    t' <- if evalTypes @p then go t else pure t
    e' <- case e of
      Nonsense e' -> pure $ Nonsense e'

      Var a -> pure $ Var a
      App x f -> undefined -- TODO
      Pi x a b -> do
        a' <- go a
        b' <- withBinding x a' $ go b
        pure (Pi x a' b')

      Bottom -> pure Bottom
      Top -> pure Top
      TT -> pure TT
    pure $ Expr (e' ::: t')
  UV u -> provideUVar u
  Hole -> absurd $ notParsed Refl
  where
    go = eval' notParsed

runTcM :: TcM a -> (a, [Error])
runTcM action = runRWS action M.empty (TcState 0 0 IM.empty) & \case
  (a, _, w) -> (a, dListToList w)

main :: IO ()
main = putStrLn "Hello, Haskell!"
