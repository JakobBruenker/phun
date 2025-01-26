{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE CPP #-}

module TC where

import Control.Monad (when, (>=>), join)
import Control.Monad.Reader (MonadReader (..), Reader)
import Control.Monad.RWS.CPS (RWS, tell, censor, gets, modify', asks, runRWS, MonadWriter)
import Control.Monad.RWS qualified as RWS
import Control.Monad.Trans.Class (lift)
import Control.Monad.Trans.Maybe (MaybeT(..))
import Control.Monad.Trans.Writer.CPS (WriterT, listen, runWriterT)
import Data.Bifunctor (second)
import Data.Char (chr, ord)
import Data.Foldable (traverse_)
import Data.Function ((&))
import Data.Functor (($>), (<&>), void)
import Data.Functor.Identity (Identity (..))
import Data.IntMap.Strict (IntMap)
import Data.IntMap.Strict qualified as IM
import Data.Kind (Type, Constraint)
import Data.List.NonEmpty (NonEmpty)
import Data.List.NonEmpty qualified as NE
import Data.Map.Strict (Map)
import Data.Map.Strict qualified as M
import Data.Monoid (Endo(..))
import Data.Text (Text)
import Data.Type.Equality qualified as E
import Data.Void (Void, absurd)
import GHC.Natural (Natural)
import Data.Text qualified as T
import Control.Comonad (Comonad (..))
import Data.Maybe (isJust)
import GHC.Records (HasField (..))
import Data.List qualified as L
import Control.Applicative ((<|>))
import GHC.Stack (HasCallStack)

-- TODO if a function is used in different places, do we have to make sure to use different uvars so it's actually generalized? Test by using id at different types.
-- TODO This is probably only an issue if uvars remain in the declaration after inference, which maybe shouldn't be allowed to begin with

type Module :: Pass -> Type
data Module p = Module 
  { decls :: [Decl p]
  , mainExpr :: Maybe (PassUExpr p)
  }

deriving instance (Show (DeclType p), Show (PassUExpr p)) => Show (Module p)

type Decl :: Pass -> Type
data Decl p = Decl
  { defName :: Id
  , defType :: DeclType p
  , defTerm :: PassUExpr p
  }

instance (Show (DeclType p), Show (PassUExpr p)) => Show (Decl p) where
  show (Decl name ty term) = show name ++ " : " ++ show ty ++ "\n" ++ show term
  showList decls = ('\n' :) . (L.intercalate "\n\n" (map show decls) ++) . ('\n' :)

-- We only need to keep track of the type in Parsed, since otherwise it's included in the term
type DeclType :: Pass -> Type
type family DeclType p where
  DeclType PParsed = Parsed
  DeclType _ = ()

-- | LHS: Expr, RHS: Type
type Typed :: Pass -> Type -> Type
data Typed p e = e ::: UExpr (Typed p) p deriving Functor

instance Comonad (Typed p) where
  extract (e ::: _) = e
  duplicate (e ::: t) = ((e ::: t) ::: t)

instance Show e => Show (Typed p e) where
  show (e ::: _) = show e

instance {-# OVERLAPPING #-} Show (Expr f p) => Show (Identity (Expr f p)) where
  show (Identity e) = show e

type Parsed = UExpr Identity PParsed

type ParsedExpr = Expr Identity PParsed

type Inferring = UExpr (Typed PInferring) PInferring

type InferringExpr = Expr (Typed PInferring) PInferring

type Checked = UExpr (Typed PChecked) PChecked

type PassUExpr :: Pass -> Type
type family PassUExpr p where
  PassUExpr PParsed = Parsed
  PassUExpr PInferring = Inferring
  PassUExpr PChecked = Checked

-- | Unification Variables
data UVar = UVar {id :: Int} deriving Eq

instance Show UVar where
  show (UVar i) =
#ifdef UNICODE
    "υ"
#else
    "u"
#endif
    ++ ['₋' | i < 0] ++  showNaturalSubscript (fromIntegral (abs i))

showNaturalSubscript :: Natural -> String
showNaturalSubscript = map toSubscript . show
  where
    toSubscript c = chr (ord c - ord '0' + ord
#ifdef UNICODE
      '₀'
#else
      '0'
#endif
      )

data Id = Name Text | Uniq Unique deriving (Eq, Ord)

-- | Gets the user-defined name of an identifier, if it has one
userName :: Id -> Maybe Text
userName (Name n) = Just n
userName (Uniq (Unique _ (Just n))) = Just n
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
  show (Uniq (Unique n name)) = maybe "v" T.unpack name ++ showNaturalSubscript n

data Pass = PParsed | PInferring | PChecked

-- | Expression that we don't give a type to, either because they don't have one
-- or because it's determined in some other way
type UExpr :: (Type -> Type) -> Pass -> Type
data UExpr f p where
  Univ :: Natural -> UExpr f p
  -- TODO add a flag showing if the Expr has been reduced, for optimization
  Expr :: (f (Expr f p)) -> UExpr f p -- ^ keeps track of free variables
  Var :: Id -> UExpr f p
  UV :: UVar -> UExpr f PInferring
  Hole :: UExpr f PParsed

instance Show (f (Expr f p)) => Show (UExpr f p) where
  show = \case
    Univ n -> "Type" ++ if n > 0 then showNaturalSubscript n else ""
    Expr e -> show e
    Var i -> show i
    UV u -> show u
    Hole -> "?"

-- TODO we probably need Fix or the ability to define inductive types -- although it seems like maybe a small fixed set of inductive types is enough (dep pair, dep prod, identity)
type Expr :: (Type -> Type) -> Pass -> Type
data Expr f p where
  Nonsense :: Parsed -> Expr f PInferring -- ^ used to assign any type to any expression

  Pi :: IdOrWildcard p -> UExpr f p -> UExpr f p -> Expr f p
  Lam :: IdOrWildcard p -> UExpr f p -> Expr f p
  App :: UExpr f p -> UExpr f p -> Expr f p

  Id :: UExpr f p -> UExpr f p -> Expr f p
  -- ^ x:A, y:A
  Refl :: UExpr f p -> Expr f p
  J :: UExpr f p -> UExpr f p -> UExpr f p -> Expr f p
  -- ^ C:Πx.Πy.Π_:(Id x y).Type_n, t:Πx:A.C x x Refl(x), p:Id a b

  -- TODO dependent sum

  -- Technically, anything below can be encoded with the above
  -- TODO either remove or add eliminators
  -- TODO actually we might need it. Otherwise we'd have to e.g. implement natural numbers with functions - but we dont' have funext (unless we add it)
  -- TODO although.. consider you could use Id Type Type for Unit and Id Type Type2 for Void. But what about Boolean?
  Bottom :: Expr f p
  Top :: Expr f p
  TT :: Expr f p

type IdOrWildcard :: Pass -> Type
data IdOrWildcard p where
  Id' :: Id -> IdOrWildcard p
  Wildcard :: IdOrWildcard PParsed

instance Show (IdOrWildcard p) where
  show = \case
    Id' i -> show i
    Wildcard -> "_"

instance NotParsed p => HasField "id" (IdOrWildcard p) Id where
  getField = \case
    Id' i -> i
    Wildcard -> absurd $ notParsed E.Refl

getId :: IdOrWildcard p -> Maybe Id
getId = \case
  Id' i -> Just i
  Wildcard -> Nothing

idOrWildcardUnique :: IdOrWildcard PParsed -> TcM Id
idOrWildcardUnique i = Uniq <$> freshUnique case i of
  Id' i' -> userName i'
  Wildcard -> Nothing

instance (Show (f (Expr f p)), Comonad f) => Show (Expr f p) where
  show = \case
    Nonsense e -> show e

    (App f x) -> "(" ++ unwords (show <$> getApps [x] f) ++ ")"
      where
        getApps :: [UExpr f p] -> UExpr f p -> [UExpr f p]
        getApps acc = \case
          (Expr (extract -> App f' x')) -> getApps (x':acc) f'
          e -> e:acc
    Pi i t b -> sPi ++ " " ++ show i ++ " : " ++ show t ++ " . " ++ show b
    Lam i b -> sLam ++ " " ++ show i ++ " . " ++ show b

    Id a b -> constr "Id" [a, b]
    Refl a -> constr "Refl" [a]
    J c t p -> constr "J" [c, t, p]

    Bottom -> sBot
    Top -> sTop
    TT -> "tt"
    where
      constr name args = name ++ "(" ++ L.intercalate ", " (map show args) ++ ")"
#ifdef UNICODE
      sPi = "Π"
      sLam = "λ"
      sBot = "⊥"
      sTop = "⊤"
#else
      sPi = "Pi"
      sLam = "\\"
      sBot = "_|_"
      sTop = "T"
#endif

-- TODO pretty print
data Error
  -- TODO add source location (possibly just decl it appears in for simplicity)
  = TypeMismatch { msourceExpr :: Maybe Parsed, expected :: Inferring, actual :: Inferring, unifFails :: (NonEmpty UnificationFailure)}
  | VarOutOfScope Id
  | NoLevelForUVar UVar
  | HasNonsense Parsed
  | Occurs UVar Inferring
  | StillHasUnifs { declName :: Maybe Text, expr :: Inferring, uvar :: UVar, uvarType :: Inferring }
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
  , subst :: IntMap (TypeOrTerm Inferring) -- unification vars
  } deriving Show

data TypeOrTerm a = Type a | Term a deriving Show

type Vars a = Map Id (TypeOrTerm a)

-- | Typechecker monad.
type TcM = RWS (Vars Inferring) (DList Error) TcState

-- TODO actually since we're always adding single elements we probably don't need a DList
newtype DList a = DList (Endo [a]) deriving (Semigroup, Monoid) via (Endo [a])

emptyDList :: DList a
emptyDList = DList (Endo id)

nullDList :: DList a -> Bool
nullDList (DList (Endo f)) = null (f [])

dListToList :: DList a -> [a]
dListToList (DList (Endo f)) = f []

silence :: TcM a -> TcM a
silence = censor $ const emptyDList

raise :: MonadWriter (DList a) m => a -> m ()
raise = tell . DList . Endo . (:)

withBinding :: MonadReader (Vars v) m => Id -> (TypeOrTerm v) -> m a -> m a
withBinding i t = local (M.insert i t)

withoutBinding :: MonadReader (Vars v) m => Id -> m a -> m a
withoutBinding i = local (M.delete i)

withContext :: MonadReader (Vars v) m => Map Id (TypeOrTerm v) -> m a -> m a
withContext ctx = local (M.union ctx)

lookupVar :: MonadReader (Vars a) m => Id -> m (Maybe (TypeOrTerm a))
lookupVar = asks . M.lookup

lookupVarType :: Id -> TcM Inferring
lookupVarType i = lookupVar i >>= \case
  Nothing -> do
    raise $ VarOutOfScope i
    UV <$> freshUVar
  Just (Type t) -> pure t
  Just (Term t) -> typeOf t

lookupUVar :: UVar -> TcM (Maybe (TypeOrTerm Inferring))
lookupUVar u = IM.lookup u.id <$> gets (.subst)

-- | Get the most concrete representation we have for a UVar
normalizeUVar :: UVar -> TcM Inferring
normalizeUVar v = do
  t <- lookupUVar v
  case t of
    Nothing -> pure (UV v)
    Just (Type _) -> pure (UV v)
    Just (Term (UV v')) -> normalizeUVar v'
    Just (Term t') -> normalize t'

-- TODO maybe find a better name? normalize kind of sounds like we're reducing it (like zonk...)
-- | Replace any UVars and Vars with their most concrete representation
normalize :: Inferring -> TcM Inferring
normalize foo = do
  res <- case foo of
    Univ n -> pure (Univ n)
    Var i -> lookupVar i >>= \case
      Just (Term e') -> normalize e'
      _ -> pure $ Var i
    Expr (e ::: t) -> do
      e' <- normalizeExpr e
      t' <- normalize t
      pure $ Expr (e' ::: t')
    UV v -> normalizeUVar v
  pure res

normalizeExpr :: InferringExpr -> TcM InferringExpr
normalizeExpr = \case
  Nonsense e -> pure (Nonsense e)

  App f x -> App <$> normalize f <*> normalize x
  Pi i t b -> withoutBinding i.id do Pi i <$> normalize t <*> normalize b
  Lam i b -> withoutBinding i.id do Lam i <$> normalize b

  Id a b -> Id <$> normalize a <*> normalize b
  Refl a -> Refl <$> normalize a
  J c t p -> J <$> normalize c <*> normalize t <*> normalize p

  Bottom -> pure Bottom
  Top -> pure Top
  TT -> pure TT

class Unify a where
  -- | Intended argument order: Expected, then actual
  unify' :: a -> a -> WriterT (DList UnificationFailure) TcM a

-- TODO Q: What happens if e.g. in App we unify left side first, but actually right side contains information we need to successfully unify left side?
unify :: Inferring -> Inferring -> TcM (Inferring, [UnificationFailure])
unify e e' = do
  re <- eval_ e
  re' <- eval_ e'
  second dListToList <$> runWriterT (unify' re re')

hasUVars :: Inferring -> TcM Bool
hasUVars = fmap go . normalize
  where
    go :: Inferring -> Bool
    go = \case
      Univ _ -> False
      Expr (e ::: t) -> goExpr e || go t 
      UV _ -> True
      Var _ -> False
    goExpr = \case
      Nonsense _ -> False
      App f x -> go f || go x
      Pi _ t b -> go t || go b
      Lam _ b -> go b
      Id a b -> go a || go b
      Refl a -> go a
      J c t p -> go c || go t || go p
      Bottom -> False
      Top -> False
      TT -> False

instance Unify InferringExpr where
  unify' = \cases
    (Nonsense e) (Nonsense e') -> raise (Can'tUnifyNonsense e e') $> Nonsense e
    (App f x) (App g y) -> do
      -- We only want to unify if neither f nor g have uvars, since e.g. `id Top` and `u1 TT` might be unifiable if u1 is actually a function that gets the type of its arg
      (dListToList . snd -> errs) <- listen do ensureNoUVars f *> ensureNoUVars g
      case NE.nonEmpty errs of
        Just _ -> pure $ App f x
        Nothing -> do
          f'' <- unify' f g
          x' <- unify' x y
          pure $ App f'' x'
      where
        ensureNoUVars :: Inferring -> WriterT (DList UnificationFailure) TcM ()
        ensureNoUVars e = lift (hasUVars e) >>= flip when (raise $ Can'tUnifyUVarInApp e)
    (Pi x a b) (Pi x' a' b') -> do
      a'' <- unify' a a'
      u <- lift $ freshUnique Nothing
      let uniq = Uniq u{tag = userName x.id <|> userName x'.id}
      b'' <- join $ unify' <$> lift (rename x.id uniq b) <*> lift (rename x'.id uniq b')
      pure $ Pi (Id' uniq) a'' b''
    (Lam x b) (Lam x' b') -> do
      u <- lift $ freshUnique Nothing
      let uniq = Uniq u{tag = userName x.id <|> userName x'.id}
      b'' <- join $ unify' <$> lift (rename x.id uniq b) <*> lift (rename x'.id uniq b')
      pure $ Lam (Id' uniq) b''

    (Id a b) (Id a' b') -> do
      a'' <- unify' a a'
      b'' <- unify' b b'
      pure $ Id a'' b''
    (Refl a) (Refl a') -> Refl <$> unify' a a'
    (J c t p) (J c' t' p') -> do
      c'' <- unify' c c'
      t'' <- unify' t t'
      p'' <- unify' p p'
      pure $ J c'' t'' p''

    Bottom Bottom -> pure Bottom
    Top Top -> pure Top
    TT TT -> pure TT
    t t' -> raise (Can'tUnifyExprs t t') *> pure t

instance Unify u => Unify (Typed PInferring u) where
  unify' (t ::: k) (t' ::: k') = do
    k'' <- unify' k k'
    t'' <- unify' t t'
    pure $ t'' ::: k''


instance Unify Inferring where
-- TODO we might actually have to generate unification constraints and solve them when possible, because it might be that two types are equal but we don't know yet -- maybe not though 🤔
-- TODO once we have the Id type, we probably need given constraints, since in the eliminator, equalities can hold only locally (e.g. 1 = 2)
     -- possibly what you want to do is, in the last unification case, the failure one, go through each equality you have, normalize it, and check if it matches (possibly accounting for sym, probably not trans)
     -- Although is that really necessary? If we can choose not to account for trans, can we just choose to have the player transport everything manually? I think yes
  unify' = \cases
    (UV u) (UV u') | u == u' -> pure $ UV u -- minor optimization: Only look up uvars if necessary
    u u' -> join $ go <$> lift (normalize u) <*> lift (normalize u')
    where
      go :: Inferring -> Inferring -> WriterT (DList UnificationFailure) TcM Inferring
      go = \cases
        (Univ n) (Univ n') -> when (n /= n') (raise $ Can'tUnifyLevels n n') *> pure (Univ n)
        (UV u) (UV u')
          | u == u' -> pure (UV u)
          | otherwise -> lift (substUVar u' (Term $ UV u)) >> pure (UV u) -- order doesn't really matter, but it seems reasonable to take the expected as "ground truth"
        e (UV u') -> lift (substUVar u' $ Term e) >> pure e
        (UV u) e -> lift (substUVar u $ Term e) >> pure e
        (Var a) (Var a') -> if (a /= a')
          then raise (Can'tUnifyVars a a') $> Var a
          else pure (Var $ combine a a')
          where
            -- We prefer to use vars with more information, or else the expected Var
            combine = \cases
              u@(Uniq (Unique _ (Just _))) _ -> u
              u@(Name _) _ -> u
              _ u'@(Uniq (Unique _ (Just _))) -> u'
              _ u'@(Name _) -> u'
              u _ -> u
        (Expr t) (Expr t') -> Expr <$> unify' t t'
        t t' -> raise (Can'tUnifyTypes t t') *> pure t

substUVar :: UVar -> TypeOrTerm Inferring -> TcM ()
substUVar v t = do
  let unwrapped = case t of
        Type e -> e
        Term e -> e
  when (occurs unwrapped) do raise $ Occurs v unwrapped
  lookupUVar v >>= \case
    Nothing -> pure ()
    Just (Type existingType) -> case t of
      Term newTerm -> do
        newType <- typeOf newTerm
        tryUnif existingType newType
      Type newType -> do
        tryUnif existingType newType
    Just (Term existingTerm) -> case t of
      Type newType -> do
        existingType <- typeOf existingTerm
        tryUnif existingType newType
      Term newTerm -> do
        tryUnif existingTerm newTerm
  modify' \s -> s{subst = IM.insert v.id t s.subst}
        
  where
    tryUnif = (void .) . tryUnify Nothing

    occurs :: Inferring -> Bool
    occurs = \case
      Univ _ -> False
      Var _ -> False
      Expr (e ::: ty) -> occursExpr e || occurs ty
      UV v' -> v == v'
    
    occursExpr :: InferringExpr -> Bool
    occursExpr = \case
      Nonsense _ -> False
      App f x -> occurs f || occurs x
      Pi _ t' b -> occurs t' || occurs b
      Lam _ b -> occurs b
      Id a b -> occurs a || occurs b
      Refl a -> occurs a
      J c t' p -> occurs c || occurs t' || occurs p
      Bottom -> False
      Top -> False
      TT -> False

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

renameIdOrWildcard :: IdOrWildcard PParsed -> Id -> Parsed -> Parsed
renameIdOrWildcard orig new e = maybe e (\v -> rename' v new e) (getId orig)

class Rename a where
  rename' :: Id -> Id -> a -> a

instance Rename (UExpr f p) => Rename (Expr f p) where
  rename' orig new = \case
    Nonsense e -> Nonsense e

    App f x -> App (rename' orig new f) (rename' orig new x)
    Pi i t b -> Pi i (rename' orig new t) (if matchesOrig i then b else rename' orig new b)
    Lam i b -> Lam i (if matchesOrig i then b else rename' orig new b)

    Id a b -> Id (rename' orig new a) (rename' orig new b)
    Refl a -> Refl (rename' orig new a)
    J c t p -> J (rename' orig new c) (rename' orig new t) (rename' orig new p)

    Bottom -> Bottom
    Top -> Top
    TT -> TT
    where
      matchesOrig = any (orig ==) . getId

instance Rename u => Rename (Identity u) where
  rename' orig new = Identity . rename' orig new . runIdentity

instance Rename u => Rename (Typed PInferring u) where
  rename' orig new (t ::: k) = rename' orig new t ::: rename' orig new k

instance Rename (f (Expr f p)) => Rename (UExpr f p) where
  rename' orig new = \case
    Univ n -> (Univ n)
    Var a -> (Var (if a == orig then new else a))
    Expr e -> Expr (rename' orig new e)
    UV u -> (UV u)
    Hole -> Hole

-- | Renames all occurrences of a variable in an expression, zonking first to make sure
-- that if the name occurs in a UVar, we can change it without having to change
-- the global UVar mapping (Not 100% sure this is necessary)
rename :: Id -> Id -> Inferring -> TcM Inferring
rename orig new = fmap (rename' orig new) . normalize

toChecked :: Maybe Text -> Inferring -> TcM (Maybe Checked)
toChecked declName source = do
  reduced <- normalize source
  go reduced reduced
  where
    go :: Inferring -> Inferring -> TcM (Maybe Checked)
    go context = go'
      where
        -- We use Maybe instead of MaybeT to avoid short-circuiting on Nothing, we want to collect all errors
        go' :: Inferring -> TcM (Maybe Checked)
        go' = \case
          Univ n -> pure . Just $ Univ n
          Var a -> pure . Just $ Var a
          Expr (e ::: ty) -> do
            ty' <- go' ty
            e' <- case e of
              Nonsense p -> do
                raise $ HasNonsense p
                pure Nothing
              App f x -> do
                f' <- go' f
                x' <- go' x
                pure $ App <$> f' <*> x'
              Pi (Id' x) a b -> do
                a' <- go' a
                b' <- go' b
                pure $ Pi (Id' x) <$> a' <*> b'
              Lam (Id' x) b -> do
                b' <- go' b
                pure $ Lam (Id' x) <$> b'

              Id a b -> do
                a' <- go' a
                b' <- go' b
                pure $ Id <$> a' <*> b'
              Refl a -> do
                a' <- go' a
                pure $ Refl <$> a'
              J c t p -> do
                c' <- go' c
                t' <- go' t
                p' <- go' p
                pure $ J <$> c' <*> t' <*> p'

              Bottom -> pure $ Just Bottom
              Top -> pure $ Just Top
              TT -> pure $ Just TT
            pure $ Expr <$> liftA2 (:::) e' ty'
          UV u -> do
            raise . StillHasUnifs declName context u =<< eval_ =<< typeOf (UV u)
            pure Nothing

extractDecls :: Module p -> Map Id (TypeOrTerm (PassUExpr p))
extractDecls (Module decls _) = M.fromList $ map (\(Decl name _ term) -> (name, Term term)) decls

inferModule :: Module PParsed -> TcM (Module PInferring)
inferModule (Module declarations mainExpr) = case declarations of
  [] -> Module [] <$> traverse infer mainExpr
  decl:decls -> do
    decl'@(Decl name () term) <- inferDecl decl
    (Module decls' mainExpr') <- withBinding name (Term term) (inferModule (Module decls mainExpr))
    pure $ Module (decl':decls') mainExpr'
    where
      inferDecl :: Decl PParsed -> TcM (Decl PInferring)
      inferDecl (Decl name ty term) = do
        ty' <- infer ty
        term' <- check ty' term
        pure $ Decl name () term'

checkModule :: Module PParsed -> TcM (Maybe (Module PChecked))
checkModule mod' = do
  inferred@(Module decls mainExpr) <- inferModule mod'
  withContext (extractDecls inferred) do
    decls' <- sequence <$> traverse checkDecl decls
    mainExpr' <- traverse (toChecked Nothing) mainExpr
    pure $ Module <$> decls' <*> mainExpr'
  where
    checkDecl :: Decl PInferring -> TcM (Maybe (Decl PChecked))
    checkDecl (Decl name () term) = fmap (Decl name ()) <$> toChecked (Just . T.pack $ show name) term

-- | Check takes a type and a parsed expression that is expected to have that type
-- NB: `join $ typeOf <$> check ty term` is guaranteed to be unifiable with ty
-- TODO: We always return the unified type here instead of expected. Could that be an issue if the unified type has a different variable than expected? And that variable is currently in context?
-- TODO: I think the main reason for using the unification result is that it's already normalized and evaluated, and we don't want to repeat that work later
check :: Inferring -> Parsed -> TcM Inferring
check expected expr = case expr of
  Univ n -> do
    let uType = Univ (n + 1)
    (ty, errs) <- unify expected uType
    case NE.nonEmpty errs of
      Nothing -> pure $ Univ n
      Just es -> do
        raise $ TypeMismatch (Just expr) expected uType es
        pure $ Expr (Nonsense expr ::: ty)
  Var a -> do
    (_, null . dListToList -> success) <- RWS.listen do
      varType <- lookupVarType a
      tryUnif varType
    pure if success
      then Var a
      else Expr (Nonsense expr ::: expected)
  Expr (Identity e) -> case e of
    App f x -> do
      i <- Uniq <$> freshUnique Nothing
      a <- UV <$> freshUVar
      b <- UV <$> freshUVar
      k <- UV <$> freshUVar
      f' <- check (Expr (Pi (Id' i) a b ::: k)) f
      x' <- check a x
      b' <- tryUnify (Just f) expected =<< fillInArg x' =<< typeOf f'
      pure (Expr $ App f' x' ::: b')
    Pi x' a b -> do
      x <- idOrWildcardUnique x'
      a' <- infer a
      let withX :: TcM a -> TcM a
          withX = withBinding x (Type a')
      b' <- withX . infer $ renameIdOrWildcard x' x b
      lvl <- maybe 0 (+1) <$> (max <$> inferLevel a' <*> withX (inferLevel b'))
      (ty, errs) <- unify expected (Univ lvl)
      case NE.nonEmpty errs of
        Nothing -> pure $ Expr (Pi (Id' x) a' b' ::: ty)
        Just es -> do
          raise $ TypeMismatch (Just expr) expected (Univ lvl) es
          pure $ Expr (Nonsense expr ::: ty)
    Lam x' rhs -> do
      x <- idOrWildcardUnique x'
      a <- UV <$> freshUVar
      b <- UV <$> freshUVar
      k <- UV <$> freshUVar
      (ty, errs) <- unify expected $ Expr (Pi (Id' x) a b ::: k)
      let x'' = getPiVar ty
      case NE.nonEmpty errs of
        Nothing -> do
          let withX'' = withBinding x'' (Type a)
          rhs' <- withX'' $ check b $ renameIdOrWildcard x' x'' rhs
          -- If k is a uvar, e.g. because it was a hole, we can fill it by inferring the kind
          normalize k >>= \case
            UV u -> do
              rhsTy <- withX'' $ typeOf rhs'
              lvl <- maybe 0 (+1) <$> (max <$> inferLevel a <*> inferLevel rhsTy)
              substUVar u (Term $ Univ lvl)
            _ -> pure ()
          pure $ Expr (Lam (Id' x'') rhs' ::: ty)
        Just es -> do
          raise $ TypeMismatch (Just expr) expected (Expr (Pi (Id' x'') a b ::: k)) es
          pure $ Expr (Nonsense expr ::: ty)

    Id a b -> do
      a' <- infer a
      a'Ty <- typeOf a'
      b' <- check a'Ty b
      lvl <- maybe 0 (+1) <$> inferLevel a'Ty
      ty <- tryUnif (Univ lvl)
      pure (Expr $ Id a' b' ::: ty)
    Refl a -> do
      a' <- infer a
      a'Ty <- typeOf a'
      u <- UV <$> freshUVar
      ty <- tryUnif (Expr (Id a' a' ::: u))
      lvl <- maybe 0 (+1) <$> inferLevel a'Ty
      traverse_ (raise . TypeMismatch (Just expr) u (Univ lvl)) . NE.nonEmpty . snd =<< unify u (Univ lvl)
      pure (Expr $ Refl a' ::: ty)
    J c t p -> do
      x <- UV <$> freshUVar
      y <- UV <$> freshUVar
      xTy <- join $ tryUnify Nothing <$> typeOf x <*> typeOf y
      idK <- UV <$> freshUVar
      let idXY = Expr (Id x y ::: idK)
      p' <- check idXY p
      c' <- do
        k <- UV <$> freshUVar
        k' <- UV <$> freshUVar
        k'' <- UV <$> freshUVar
        pVar <- Id' . Uniq <$> freshUnique Nothing
        a <- Id' . Uniq <$> freshUnique Nothing
        b <- Id' . Uniq <$> freshUnique Nothing
        cabqTy <- UV <$> freshUVar -- Type of C a b q
        let idAB = Expr (Id (Var a.id) (Var b.id) ::: idK)
            cabTy = Expr (Pi pVar idAB cabqTy ::: k'')
            caTy = Expr (Pi b xTy cabTy ::: k')
            cTy = Expr (Pi a xTy caTy ::: k)
        check cTy c
      c'Ty <- typeOf c'

      v <- Id' . Uniq <$> freshUnique Nothing
      t' <- do 
        k <- UV <$> freshUVar
        let varV = Var v.id
        let idVV = Expr (Id varV varV ::: idK)
        let reflV = Expr (Refl varV ::: idVV)
        cvTy <- fillInArg varV c'Ty
        cvvTy <- fillInArg varV cvTy
        cvvRvTy <- fillInArg reflV cvvTy
        check (Expr (Pi v xTy (Expr (App (Expr (App (Expr (App c' varV ::: cvTy)) varV ::: cvvTy)) reflV ::: cvvRvTy)) ::: k)) t
      ty' <- do
        cxTy <- fillInArg x c'Ty
        cxyTy <- fillInArg y cxTy
        cxypTy <- fillInArg p' cxyTy
        tryUnif (Expr (App (Expr (App (Expr (App c' x ::: cxTy)) y ::: cxyTy)) p' ::: cxypTy))
      pure $ Expr $ J c' t' p' ::: ty'

    Bottom -> Expr . (Bottom :::) <$> tryUnif (Univ 0)
    Top -> Expr . (Top :::) <$> tryUnif (Univ 0)
    TT -> Expr . (TT :::) <$> tryUnif (Expr (Top ::: Univ 0))
  Hole -> do
    hole <- freshUVar
    substUVar hole (Type expected)
    pure $ UV hole
  where
    tryUnif = tryUnify (Just expr) expected
  
tryUnify :: Maybe Parsed -> Inferring -> Inferring -> TcM Inferring
tryUnify expr expt act = do
  (expr', errs) <- unify expt act
  traverse_ (\x -> raise (TypeMismatch expr expt act x)) (NE.nonEmpty errs) $> expr'

unifiable :: Inferring -> Inferring -> TcM Bool
unifiable e e' = do
  (_, errs) <- unify e e'
  pure $ null errs

-- | inferLevel gets the level of the universe, or else Nothing if the expression is not a universe
inferLevel :: Inferring -> TcM (Maybe Natural)
inferLevel = \case
  Univ n -> pure $ Just n
  Var a -> lookupVarType a >>= inferLowerLevel
  Expr (_ ::: t) -> inferLowerLevel t
  UV u -> normalizeUVar u >>= \case
    -- TODO maybe we can get away with not throwing an error here if we store a min/max level in a UVar (...and maybe make it cumulative to play nice with Pi's max...)
    -- TODO could also say Univ can optionally take a set of UVars and has to have the max level of those + 1 (plus an optional min level)
    UV u' -> do
      raise $ NoLevelForUVar u'
      pure Nothing
    t -> inferLevel t
  where
    inferLowerLevel t = runMaybeT [ l - 1 | l <- MaybeT (inferLevel t), l > 0 ]

-- | Must be called with an expression that is a Pi type. Fills in the argument
-- of that Pi type with the given expression, and returns the body.
fillInArg :: HasCallStack => Inferring -> Inferring -> TcM Inferring
fillInArg filler e = normalize e >>= \case 
  (Expr (Pi x _ b ::: _)) -> withBinding x.id (Term filler) $ normalize b
  e' -> error $ "fillInArg called with non-Pi expression: " <> show e'

-- | Must be called with an expression that is a Pi type. Returns the name of the bound variable.
getPiVar :: Inferring -> Id
getPiVar = \case
  (Expr (Pi x _ _ ::: _)) -> x.id
  e -> error $ "getPiVar called with non-Pi expression: " <> show e

-- TODO: Is infer just check with a fresh UVar as type?
infer :: Parsed -> TcM Inferring
infer expr = case expr of
  Univ n -> pure $ Univ n
  Var a -> pure $ Var a
  Expr (Identity e) -> case e of
    App f x -> do
      a <- UV <$> freshUVar
      b <- UV <$> freshUVar
      i <- Uniq <$> freshUnique Nothing
      k <- UV <$> freshUVar
      f' <- check (Expr (Pi (Id' i) a b ::: k)) f
      x' <- check a x
      b' <- fillInArg x' =<< typeOf f'
      pure (Expr $ App f' x' ::: b')
    Pi x' a b -> do
      x <- idOrWildcardUnique x'
      a' <- infer a
      let withX :: TcM a -> TcM a
          withX = withBinding x (Type a')
      b' <- withX . infer $ renameIdOrWildcard x' x b
      lvl <- maybe 0 (+1) <$> (max <$> inferLevel a' <*> withX (inferLevel b'))
      pure (Expr $ Pi (Id' x) a' b' ::: Univ lvl)
    Lam x' rhs -> do
      x <- idOrWildcardUnique x'
      a <- UV <$> freshUVar
      let withX = withBinding x (Type a)
      rhs' <- withX $ infer $ renameIdOrWildcard x' x rhs
      rhsTy <- withX $ typeOf rhs'
      lvl <- maybe 0 (+1) <$> (max <$> inferLevel a <*> inferLevel rhsTy)
      -- TODO Q: If we later substitute x in bt, does that mean inference has to be able to use x in bt? Maybe not, if we say dependent types can't be inferred
      -- TODO do we need this to be able to infer a type for e.g. \x.x?
      -- TODO idea for that: Wrap infer lambda with something that checks if the bound var is not subst'd, and then make a Pi if so
      -- TODO except it doesn't quite work like that, because we have no inferred arguments. So \x.x cannot be generalized. What about \t.\x.the t x?
      -- TODO we could decide to default to Type in a case like \x.x
      pure (Expr $ Lam (Id' x) rhs' ::: Expr (Pi (Id' x) a rhsTy ::: Univ lvl))

    Id a b -> do
      a' <- infer a
      a'Ty <- typeOf a'
      b' <- check a'Ty b
      lvl <- maybe 0 (+1) <$> inferLevel a'Ty
      pure (Expr $ Id a' b' ::: Univ lvl)
    Refl a -> do
      ty <- infer (Expr (Identity (Id a a)))
      a' <- infer a
      pure (Expr $ Refl a' ::: ty)
    j@(J _ _ _) -> do
      ty <- UV <$> freshUVar
      check ty (Expr (pure j))

    Bottom -> pure (Expr $ Bottom ::: Univ 0)
    Top -> pure (Expr $ Top ::: Univ 0)
    TT -> pure (Expr $ TT ::: Expr (Top ::: Univ 0))
  Hole -> UV <$> freshUVar

-- | Get the type of an expression.
-- If the expression is a UVar, this will return a UVar that is registered as type of the expression's UVar
typeOf :: Inferring -> TcM Inferring
typeOf = \case
  Univ n -> pure $ Univ (n + 1)
  Var a -> lookupVarType a
  Expr (_ ::: t) -> pure t
  UV u -> do
    lookupUVar u >>= \case
      Just (Type t) -> pure t
      Just (Term t) -> typeOf t
      Nothing -> do
        t <- UV <$> freshUVar
        substUVar u (Type t)
        pure t

class (NotParsed p, MonadReader (Vars (UExpr (Typed p) p)) (PassMonad p)) => Eval p where
  type PassMonad p :: Type -> Type
  normalizeUnchecked :: UExpr (Typed p) p -> PassMonad p (UExpr (Typed p) p)
  evalTypes :: Bool

class NotParsed p where notParsed :: p E.:~: PParsed -> Void
instance NotParsed PInferring where notParsed = \case
instance NotParsed PChecked where notParsed = \case

data WasReduced = WasReduced deriving Show

instance Semigroup WasReduced where _ <> _ = WasReduced

eval_ :: (Eval p, m ~ PassMonad p, e ~ UExpr (Typed p) p) => e -> m e
eval_ = fmap fst . runWriterT . eval

-- | Brings an expression to normal form
eval :: (Eval p, m ~ PassMonad p, e ~ UExpr (Typed p) p) => e -> WriterT (Maybe WasReduced) m e
eval = lift . normalizeUnchecked >=> go
  where
    go e = do
      (e', wasReduced) <- listen $ step e
      if isJust wasReduced then go e' else pure e'

instance Eval PInferring where
  type PassMonad PInferring = TcM
  evalTypes = True
  normalizeUnchecked = normalize

instance Eval PChecked where
  type PassMonad PChecked = Reader (Vars Checked)
  evalTypes = False
  normalizeUnchecked = pure

type HasVars :: (Type -> Type) -> Constraint
class HasVars m where
  type Var m :: Type

instance HasVars TcM where
  type Var TcM = Inferring

{-# SPECIALIZE step :: Inferring -> WriterT (Maybe WasReduced) TcM Inferring #-}
{-# SPECIALIZE step :: Checked -> WriterT (Maybe WasReduced) (Reader (Vars Checked)) Checked #-}
-- | Perform a reduction step and return the new expression and whether it was reduced
step :: (Eval p, m ~ PassMonad p, e ~ UExpr (Typed p) p) => e -> WriterT (Maybe WasReduced) m e
step @p = \case
  u@(Univ _) -> pure u
  Var a -> do
    lookupVar a <&> \case
      Just (Term term) -> term
      _ -> Var a -- We allow using vars that are out of scope here, it'll just not be reduced
  Expr (e ::: ty) -> do
    ty' <- if evalTypes @p then step ty else pure ty
    let withType x = Expr (x ::: ty')
    e' <- case e of
      Nonsense e' -> pure . withType $ Nonsense e'
      App f x -> do
        f' <- eval f
        x' <- eval x
        case f' of
          Expr (extract -> Lam i rhs) -> do
            tellHasReduced
            withBinding i.id (Term x') $ eval rhs
          _ -> pure . withType $ App f' x'
      Pi x a b -> do
        a' <- eval a
        b' <- eval b
        pure . withType $ Pi x a' b'
      Lam x b -> withType . Lam x <$> eval b

      Id a b -> do
        a' <- eval a
        b' <- eval b
        pure . withType $ Id a' b'
      Refl a -> withType . Refl <$> eval a
      J c t p -> do
        t' <- eval t
        p' <- eval p
        case p' of
          Expr (extract -> Refl x) -> do
              tellHasReduced
              pure . withType $ App t' x
          _ -> do
            c' <- eval c
            pure . withType $ J c' t' p'

      Bottom -> pure . withType $ Bottom
      Top -> pure . withType $ Top
      TT -> pure . withType $ TT
    pure e'
  UV u -> pure $ UV u
  Hole -> absurd $ notParsed E.Refl
  where
    tellHasReduced = tell (Just WasReduced)

runTcM :: TcM a -> (a, [Error])
runTcM @a action = runRWS withNormalizedErrors M.empty (TcState 0 0 IM.empty) &
  \((a, errs), _, _) -> (a, errs)
  where
    -- By normalizing at the very end, we can ensure the errors contain all useful data
    withNormalizedErrors :: TcM (a, [Error])
    withNormalizedErrors = do
      (a, errs) <- RWS.listen action
      traverse normalizeError (dListToList errs) >>= pure . (a,)

    normalizeError :: Error -> TcM Error
    normalizeError = \case
      TypeMismatch e expt act errs -> TypeMismatch e <$> normalize expt <*> normalize act <*> traverse normalizeUFails errs
      e -> pure e

    normalizeUFails :: UnificationFailure -> TcM UnificationFailure
    normalizeUFails = \case
      Can'tUnifyTypes expt act -> Can'tUnifyTypes <$> normalize act <*> normalize expt
      Can'tUnifyExprs expt act -> Can'tUnifyExprs <$> normalizeExpr act <*> normalizeExpr expt
      Can'tUnifyNonsense expt act -> pure $ Can'tUnifyNonsense expt act
      Can'tUnifyVars v v' -> pure $ Can'tUnifyVars v v'
      Can'tUnifyLevels l l' -> pure $ Can'tUnifyLevels l l'
      Can'tUnifyUVarInApp e -> Can'tUnifyUVarInApp <$> normalize e
