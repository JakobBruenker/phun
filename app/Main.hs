{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE AllowAmbiguousTypes #-}

module Main where

import Control.Monad (when, (>=>), join)
import Control.Monad.Reader (MonadReader (..))
import Control.Monad.RWS.CPS (RWS, tell, censor, gets, modify', asks, runRWS)
import Control.Monad.Trans.Class (lift)
import Control.Monad.Trans.Maybe (MaybeT(..))
import Control.Monad.Trans.Writer.CPS (WriterT, Writer, listen, runWriterT)
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
import Data.Monoid (Endo(..))
import Data.Text (Text)
import Data.Type.Equality ((:~:) (..))
import Data.Void (Void, absurd)
import GHC.Natural (Natural)
import qualified Data.Text as T
import Control.Comonad (Comonad (..))
import Data.Maybe (isJust)

-- | LHS: Expr, RHS: Type
type Typed :: Pass -> Type -> Type
data Typed p e = e ::: UExpr (Typed p) p deriving Functor

instance Comonad (Typed p) where
  extract (e ::: _) = e
  duplicate (e ::: t) = ((e ::: t) ::: t)

instance Show e => Show (Typed p e) where
  show (e ::: t) = show e ++ " : " ++ show t

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
  show (Uniq (Unique n name)) = maybe uniq (\n' -> T.unpack n' ++ uniq) name
    where
      uniq = showNaturalSubscript n

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

-- TODO we probably need Fix or the ability to define inductive types -- although it seems like maybe a small fixed set of inductive types is enough (dep pair, dep prod, identity)
type Expr :: (Type -> Type) -> Pass -> Type
data Expr f p where
  Nonsense :: Parsed -> Expr f PInferring -- ^ used to assign any type to any expression

  Var :: Id -> Expr f p
  App :: UExpr f p -> UExpr f p -> Expr f p -- ^ NB: This is x f, not f x
  Pi :: Id -> UExpr f p -> UExpr f p -> Expr f p
  Lam :: Id -> UExpr f p -> Expr f p

  -- Technically, anything below can be encoded with the above
  -- TODO either remove or add eliminators
  Bottom :: Expr f p
  Top :: Expr f p
  TT :: Expr f p

instance (Show (f (Expr f p))) => Show (Expr f p) where
  show (Nonsense e) = show e

  show (Var i) = show i
  show (App x f) = ("(" ++ show x ++ " " ++ show f ++ ")")
  show (Pi i t b) = "Π " ++ show i ++ " : " ++ show t ++ " . " ++ show b
  show (Lam i b) = "λ " ++ show i ++ " . " ++ show b

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
  | NoTypeForUVar UVar
  | NoLevelForUVar UVar
  deriving Show

-- TODO add details
data UnificationFailure
  = Can'tUnifyTypes Inferring Inferring
  | Can'tUnifyExprs InferringExpr InferringExpr
  | Can'tUnifyVars Id Id
  | Can'tUnifyLevels Natural Natural
  | Can'tUnifyNonsense Parsed Parsed
  | Can'tUnifyUVarInApp Inferring
  deriving Show

data TcState = TcState
  { nextUVar :: Int
  , nextUnique :: Natural
  , subst :: IntMap Inferring
  }

type VarTypes a = Map Id a

-- | Typechecker monad.
--
-- Reader: Map from variable names to their types
type TcM = RWS (VarTypes Inferring) (DList Error) TcState

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

lookupVarType :: Id -> TcM Inferring
lookupVarType i = asks (M.lookup i) >>= \case
  Nothing -> do
    raise $ VarOutOfScope i
    UV <$> freshUVar
  Just t -> pure t

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

withBinding :: MonadReader (VarTypes v) m => Id -> v -> m a -> m a
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
    Lam i b -> Lam i <$> normalize b

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
raiseUnif = tell . Endo . (:)

class Unify a where
  -- | Intended argument order: Expected, then actual
  unify' :: a -> a -> WriterT (DList UnificationFailure) TcM a

-- TODO probably reduce here? To avoid trying to reduce on every recursive call of unify'
-- TODO Q: What happens if e.g. in App we unify left side first, but actually right side contains information we need to successfully unify left side?
unify :: Inferring -> Inferring -> TcM (Inferring, [UnificationFailure])
unify e e' = second dListToList <$> runWriterT (unify' e e')

hasUVars :: Inferring -> Bool
hasUVars = \case
  Univ _ -> False
  Expr (e ::: t) -> go e || hasUVars t 
  UV _ -> True
  where
    go = \case
      Nonsense _ -> False
      Var _ -> False
      App x f -> hasUVars x || hasUVars f
      Pi _ t b -> hasUVars t || hasUVars b
      Lam _ b -> hasUVars b
      Bottom -> False
      Top -> False
      TT -> False

instance Unify InferringExpr where
  unify' = \cases
    (Nonsense e) (Nonsense e') -> raiseUnif (Can'tUnifyNonsense e e') $> Nonsense e

    (Var a) (Var a') -> if (a /= a')
      then raiseUnif (Can'tUnifyVars a a') $> Var a
      else pure (Var $ combine a a')
      where
        -- We prefer to use vars with more information, or else the expected Var
        combine = \cases
          u@(Uniq (Unique _ (Just _))) _ -> u
          u@(Name _) _ -> u
          _ u'@(Uniq (Unique _ (Just _))) -> u'
          u _ -> u

    (App x f) (App y g) -> do
      ((f', g'), dListToList -> errs) <- listen $ (,) <$> ensureNoUVars f <*> ensureNoUVars g
      -- We only want to unify if neither f nor g have uvars, since e.g. `Top id` and `TT u1` might be unifiable if u1 is actually a function that gets the type of its arg
      -- TODO However, this makes us order dependent? Whether it contains a uvar might depend on what else we unify first
      case NE.nonEmpty errs of
        Just _ -> pure $ App x f
        Nothing -> do
          f'' <- unify' f' g'
          x' <- unify' x y
          pure $ App x' f''
      where
        ensureNoUVars :: Inferring -> WriterT (DList UnificationFailure) TcM Inferring
        ensureNoUVars e = do
          e' <- lift $ zonk e
          when (hasUVars e) $ raiseUnif $ Can'tUnifyUVarInApp e'
          pure e'
    (Pi x a b) (Pi x' a' b') -> do
      a'' <- unify' a a'
      u <- lift $ freshUnique Nothing
      let uniq = Uniq u{tag = userName x}
      b'' <- join $ unify' <$> lift (rename x uniq b) <*> lift (rename x' uniq b')
      pure $ Pi uniq a'' b''
    (Lam x b) (Lam x' b') -> do
      u <- lift $ freshUnique Nothing
      let uniq = Uniq u{tag = userName x}
      b'' <- join $ unify' <$> lift (rename x uniq b) <*> lift (rename x' uniq b')
      pure $ Lam uniq b''

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
-- TODO I think TcM actually needs to keep track of both Var terms and Var types (for Pi and Lam binders), since if we're evalling deep in a term we need to be able to access bindings from further out
    --  Wait that might not be true, because we only introduce new terms when evalling App, and then at the end of eval all vars should be replaced I think
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
    Lam i b -> Lam i <$> zonk b

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
    Pi i t b -> Pi i <$> rename' orig new t <*> if i == orig then pure b else rename' orig new b
    Lam i b -> Lam i <$> if i == orig then pure b else rename' orig new b

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

substVar :: Comonad f => Id -> UExpr f e -> UExpr f e -> UExpr f e
substVar x a = \case
  Univ n -> Univ n
  Expr (extract -> Var x') | x == x' -> a
  Expr e -> Expr $ substVarExpr <$> e
  UV u -> UV u
  Hole -> Hole
  where
    substVarExpr = \case
      Nonsense e -> Nonsense e

      Var v -> Var v
      App e f -> App (substVar x a e) (substVar x a f)
      Pi i t b -> Pi i (substVar x a t) if x == i then b else substVar x a b
      Lam x' b -> Lam x' if x == x' then b else substVar x a b

      Bottom -> Bottom
      Top -> Top
      TT -> TT

-- TODO: termination checker -- actually this is not necessary if we support inductive types
-- | Check takes a type and a parsed expression that is expected to have that type
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
      varType <- lookupVarType a
      ty <- tryUnify expr expected varType
      pure $ Expr (Var a ::: ty)
    App x f -> do
      i <- Uniq <$> freshUnique Nothing
      a <- UV <$> freshUVar
      b <- UV <$> freshUVar
      k <- UV <$> freshUVar
      f' <- check (Expr (Pi i a b ::: k)) f
      x' <- check a x
      b' <- tryUnify f expected $ substVar i x' b
      pure (Expr $ App x' f' ::: b')
    Pi x a b -> do
      a' <- infer a
      b' <- withBinding x a' $ infer b
      lvl <- maybe 0 (+1) <$> (max <$> inferLevel a' <*> inferLevel b')
      (ty, errs) <- unify expected (Univ lvl)
      case NE.nonEmpty errs of
        Nothing -> pure $ Expr (Pi x a' b' ::: ty)
        Just es -> do
          raise $ TypeMismatch expr expected (Univ lvl) es
          pure $ Expr (Nonsense expr ::: ty)
    Lam x rhs -> do
      a <- UV <$> freshUVar
      b <- UV <$> freshUVar
      k <- UV <$> freshUVar
      (ty, errs) <- unify expected $ Expr (Pi x a b ::: k)
      case NE.nonEmpty errs of
        Nothing -> do
          rhs' <- withBinding x a $ check b rhs
          pure $ Expr (Lam x rhs' ::: ty)
        Just es -> do
          raise $ TypeMismatch expr expected (Expr (Pi x a b ::: k)) es
          pure $ Expr (Nonsense expr ::: ty)

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
    -- TODO maybe we can get away with not throwing an error here if we store a min/max level in a UVar (...and maybe make it cumulative to play nice with Pi's max...)
    -- TODO could also say Univ can optionally take a set of UVars and has to have the max level of those + 1 (plus an optional min level)
    UV u' -> do
      raise $ NoLevelForUVar u'
      pure Nothing
    t -> inferLevel t

-- infer should not use unify, and instead call check.
infer :: Parsed -> TcM Inferring
infer expr = case expr of
  Univ n -> pure $ Univ n
  Expr (Identity e) -> case e of
    Var a -> do
      varT <- lookupVarType a
      pure (Expr $ Var a ::: varT)
    App x f -> do
      a <- UV <$> freshUVar
      b <- UV <$> freshUVar
      i <- Uniq <$> freshUnique Nothing
      k <- UV <$> freshUVar
      f' <- check (Expr (Pi i a b ::: k)) f
      x' <- check a x
      pure (Expr $ App x' f' ::: substVar i x' b)
    Pi x a b -> do
      a' <- infer a
      b' <- withBinding x a' $ infer b
      lvl <- maybe 0 (+1) <$> (max <$> inferLevel a' <*> inferLevel b')
      pure (Expr $ Pi x a' b' ::: Univ lvl)
    Lam x b -> do
      a <- UV <$> freshUVar
      b' <- withBinding x a $ infer b
      bt <- typeOf b'
      lvl <- maybe 0 (+1) <$> (max <$> inferLevel a <*> inferLevel bt)
      -- TODO Q: If we later substitute x in bt, does that mean inference has to be able to use x in bt? Maybe not, if we say dependent types can't be inferred
      pure (Expr $ Lam x b' ::: Expr (Pi x a bt ::: Univ lvl))

    Bottom -> pure (Expr $ Bottom ::: Univ 0)
    Top -> pure (Expr $ Top ::: Univ 0)
    TT -> pure (Expr $ TT ::: Expr (Top ::: Univ 0))
  Hole -> UV <$> freshUVar

typeOf :: Inferring -> TcM Inferring
typeOf = \case
  Univ n -> pure $ Univ (n + 1)
  Expr (_ ::: t) -> pure t
  UV u -> do
    raise $ NoTypeForUVar u -- TODO maybe it makes sense if uvars have an optional type, so we don't have to error here (but can return a uvar)?
    infer Hole -- TODO this is probably an issue - because we actually have no way to connect the uvar representing this type with u

class Monad (PassMonad p) => Eval p where
  type PassMonad p :: Type -> Type
  type UVarResult p :: Type
  -- NB: Instead of this, we could also just ensure it's zonked before it's evaled
  provideUVar :: UVar' p -> (PassMonad p) (UVarResult p)
  evalTypes :: Bool
  notParsed :: p :~: PParsed -> Void

data WasReduced = WasReduced

instance Semigroup WasReduced where _ <> _ = WasReduced

-- | Step through a single pass of the typechecker and return the new expression and whether it was reduced
step :: (Eval p, m ~ PassMonad p, e ~ UExpr (Typed p) p) => e -> WriterT (Maybe WasReduced) m e
step = step'

eval :: (Monad (PassMonad p), Eval p) => (e ~ UExpr (Typed p) p) => e -> WriterT (Maybe WasReduced) (PassMonad p) e
eval e = do
  (e', wasReduced) <- listen $ step e
  if isJust wasReduced then eval e' else pure e'

instance Eval PInferring where
  type PassMonad PInferring = TcM
  type UVarResult PInferring = Inferring
  provideUVar = normalizeUVar
  evalTypes = True
  notParsed = \case

instance Eval PChecked where
  type PassMonad PChecked = Identity
  type UVarResult PChecked = Checked
  provideUVar = \case
  evalTypes = False
  notParsed = \case

{-# SPECIALIZE step' :: Inferring -> WriterT (Maybe WasReduced) TcM Inferring #-}
{-# SPECIALIZE step' :: Checked -> Writer (Maybe WasReduced) Checked #-}
step' :: (Eval p, m ~ PassMonad p, e ~ UExpr (Typed p) p) => e -> WriterT (Maybe WasReduced) m e
step' @p = \case
  u@(Univ _) -> pure u
  Expr (e ::: t) -> do
    t' <- if evalTypes @p then step' t else pure t
    let withType x = Expr (x ::: t')
    e' :: UExpr (Typed p) p <- case e of
      Nonsense e' -> pure . withType $ Nonsense e'

      Var a -> pure . withType $ Var a
      App x f -> do
        f' <- eval f
        x' <- eval x
        case f' of
          Expr (extract -> Lam i rhs) -> do
            tellHasReduced
            step $ substVar i x' rhs
          _ -> pure . withType $ App x' f'
      Pi x a b -> do
        a' <- step' a
        b' <- step' b
        pure . withType $ Pi x a' b'
      Lam x b -> withType . Lam x <$> step' b

      Bottom -> pure . withType $ Bottom
      Top -> pure . withType $ Top
      TT -> pure . withType $ TT
    pure e'
  UV u -> lift (provideUVar u)
  Hole -> absurd $ notParsed Refl
  where
    tellHasReduced = tell (Just WasReduced)

runTcM :: TcM a -> (a, [Error])
runTcM action = runRWS action M.empty (TcState 0 0 IM.empty) & \case
  (a, _, w) -> (a, dListToList w)

main :: IO ()
main = putStrLn "Hello, Haskell!"
