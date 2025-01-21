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
import Control.Monad.Trans.Maybe (MaybeT(..), hoistMaybe)
import Control.Monad.Trans.Writer.CPS (WriterT, listen, runWriterT)
import Data.Bifunctor (second)
import Data.Char (chr, ord)
import Data.Foldable (traverse_)
import Data.Function ((&))
import Data.Functor (($>), (<&>))
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
import Data.Type.Equality ((:~:) (..))
import Data.Void (Void, absurd)
import GHC.Natural (Natural)
import Data.Text qualified as T
import Control.Comonad (Comonad (..))
import Data.Maybe (isJust)
import GHC.Records (HasField (..))
import Data.List qualified as L
import Control.Applicative ((<|>))

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
  show (e ::: t) = show e ++ " : " ++ show t

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
type UVar' :: Pass -> Type
data UVar' p where
  UVar :: {id :: Int} -> UVar' PInferring

type UVar = UVar' PInferring

deriving instance Eq (UVar' p)

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

type UExpr :: (Type -> Type) -> Pass -> Type
data UExpr f p where
  Univ :: Natural -> UExpr f p
  -- TODO add a flag showing if the Expr has been reduced
  Expr :: (f (Expr f p)) -> UExpr f p -- ^ keeps track of free variables
  UV :: UVar -> UExpr f PInferring
  Hole :: UExpr f PParsed

instance Show (f (Expr f p)) => Show (UExpr f p) where
  show (Univ n) = "Type" ++ if n > 0 then showNaturalSubscript n else ""
  show (Expr e) = "(" ++ show e ++ ")"
  show (UV u) = show u
  show Hole = "?"

-- TODO we probably need Fix or the ability to define inductive types -- although it seems like maybe a small fixed set of inductive types is enough (dep pair, dep prod, identity)
type Expr :: (Type -> Type) -> Pass -> Type
data Expr f p where
  Nonsense :: Parsed -> Expr f PInferring -- ^ used to assign any type to any expression

  -- TODO I think Var can be a UExpr. The type is stored in the context.
  Var :: Id -> Expr f p

  Pi :: IdOrWildcard p -> UExpr f p -> UExpr f p -> Expr f p
  Lam :: IdOrWildcard p -> UExpr f p -> Expr f p
  App :: UExpr f p -> UExpr f p -> Expr f p
  -- TODO dependent sum

  -- Technically, anything below can be encoded with the above
  -- TODO either remove or add eliminators
  Bottom :: Expr f p
  Top :: Expr f p
  TT :: Expr f p

type IdOrWildcard :: Pass -> Type
data IdOrWildcard p where
  Id :: Id -> IdOrWildcard p
  Wildcard :: IdOrWildcard PParsed

instance Show (IdOrWildcard p) where
  show = \case
    Id i -> show i
    Wildcard -> "_"

instance NotParsed p => HasField "id" (IdOrWildcard p) Id where
  getField = \case
    Id i -> i
    Wildcard -> absurd $ notParsed Refl

instance Show (f (Expr f p)) => Show (Expr f p) where
  show = \case
    Nonsense e -> show e

    Var i -> show i
    App f x -> ("(" ++ show f ++ " " ++ show x ++ ")")
    Pi i t b -> sPi ++ " " ++ show i ++ " : " ++ show t ++ " . " ++ show b
    Lam i b -> sLam ++ " " ++ show i ++ " . " ++ show b

    Bottom -> sBot
    Top -> sTop
    TT -> "tt"
    where
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
  = TypeMismatch { sourceExpr :: Parsed, expected :: Inferring, actual :: Inferring, unifFails :: (NonEmpty UnificationFailure)}
  | LevelMismatch { sourceExpr :: Parsed, expectedLevel :: Natural, actualLevel :: Natural }
  | VarOutOfScope Id
  | NoTypeForUVar UVar
  | NoLevelForUVar UVar
  | HasNonsense Parsed
  | StillHasUnifs UVar
  | Bug Text -- ^ Unexpected error indicating a compiler bug
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
  , subst :: IntMap Inferring -- unification vars
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

lookupUVar :: UVar -> TcM (Maybe Inferring)
lookupUVar u = IM.lookup u.id <$> gets (.subst)

-- | Get the most concrete representation we have for a UVar
normalizeUVar :: UVar -> TcM Inferring
normalizeUVar v = do
  t <- lookupUVar v
  case t of
    Nothing -> pure (UV v)
    Just (UV v') -> normalizeUVar v'
    Just t' -> normalize t'

withBinding :: MonadReader (Vars v) m => Id -> (TypeOrTerm v) -> m a -> m a
withBinding i t = local (M.insert i t)

lookupVar :: MonadReader (Vars a) m => Id -> m (Maybe (TypeOrTerm a))
lookupVar = asks . M.lookup

lookupVarType :: Id -> TcM Inferring
lookupVarType i = lookupVar i >>= \case
  Nothing -> do
    raise $ VarOutOfScope i
    UV <$> freshUVar
  Just (Type t) -> pure t
  Just (Term t) -> typeOf t

lookupVarTerm :: MonadReader (Vars a) m => Id -> m (Maybe a)
lookupVarTerm i = lookupVar i <&> \case
  Just (Term t) -> Just t
  _ -> Nothing

-- | Replace any UVars and Vars with their most concrete representation
normalize :: Inferring -> TcM Inferring
normalize = \case
  Univ n -> pure (Univ n)
  Expr (Var i ::: t) -> do
    lookupVar i >>= \case
      Just (Term e') -> normalize e'
      _ -> do
        t' <- normalize t
        pure $ Expr (Var i ::: t')
  Expr (e ::: t) -> do
    e' <- normalizeExpr e
    t' <- normalize t
    pure $ Expr (e' ::: t')
  UV v -> normalizeUVar v
  where
    normalizeExpr :: InferringExpr -> TcM InferringExpr
    normalizeExpr = \case
      Nonsense e -> pure (Nonsense e)

      Var a -> pure (Var a) -- impossible
      App f x -> App <$> normalize f <*> normalize x
      Pi i t b -> Pi i <$> normalize t <*> normalize b
      Lam i b -> Lam i <$> normalize b

      Bottom -> pure Bottom
      Top -> pure Top
      TT -> pure TT


-- instance Normalize u => Normalize (Typed PInferring u) where
--   normalize :: Typed PInferring u -> TcM (Typed PInferring u)
--   normalize (t ::: k) = do
--     t' <- normalize t
--     k' <- normalize k
--     pure (t' ::: k')

-- instance Normalize Inferring where
--   -- | Normalize all UVars in a type
--   -- TODO maybe zonk here - although I'm not sure it makes much sense because we don't always keep this result

class Unify a where
  -- | Intended argument order: Expected, then actual
  unify' :: a -> a -> WriterT (DList UnificationFailure) TcM a

-- TODO Q: What happens if e.g. in App we unify left side first, but actually right side contains information we need to successfully unify left side?
unify :: Inferring -> Inferring -> TcM (Inferring, [UnificationFailure])
unify e e' = do
  re <- eval_ e
  re' <- eval_ e'
  second dListToList <$> runWriterT (unify' re re')

hasUVars :: Inferring -> Bool
hasUVars = \case
  Univ _ -> False
  Expr (e ::: t) -> go e || hasUVars t 
  UV _ -> True
  where
    go = \case
      Nonsense _ -> False
      Var _ -> False
      App f x -> hasUVars f || hasUVars x
      Pi _ t b -> hasUVars t || hasUVars b
      Lam _ b -> hasUVars b
      Bottom -> False
      Top -> False
      TT -> False

instance Unify InferringExpr where
  unify' = \cases
    (Nonsense e) (Nonsense e') -> raise (Can'tUnifyNonsense e e') $> Nonsense e

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

    (App f x) (App g y) -> do
      -- We only want to unify if neither f nor g have uvars, since e.g. `Top id` and `TT u1` might be unifiable if u1 is actually a function that gets the type of its arg
      -- TODO However, this makes us order dependent? Whether it contains a uvar might depend on what else we unify first
      ((f', g'), dListToList -> errs) <- listen $ (,) <$> ensureNoUVars f <*> ensureNoUVars g
      case NE.nonEmpty errs of
        Just _ -> pure $ App f x
        Nothing -> do
          f'' <- unify' f' g'
          x' <- unify' x y
          pure $ App f'' x'
      where
        ensureNoUVars :: Inferring -> WriterT (DList UnificationFailure) TcM Inferring
        ensureNoUVars e = do
          e' <- lift $ zonk e
          when (hasUVars e) $ raise $ Can'tUnifyUVarInApp e'
          pure e'
    (Pi x a b) (Pi x' a' b') -> do
      a'' <- unify' a a'
      u <- lift $ freshUnique Nothing
      let uniq = Uniq u{tag = userName x.id <|> userName x'.id}
      b'' <- join $ unify' <$> lift (rename x.id uniq b) <*> lift (rename x'.id uniq b')
      pure $ Pi (Id uniq) a'' b''
    (Lam x b) (Lam x' b') -> do
      u <- lift $ freshUnique Nothing
      let uniq = Uniq u{tag = userName x.id <|> userName x'.id}
      b'' <- join $ unify' <$> lift (rename x.id uniq b) <*> lift (rename x'.id uniq b')
      pure $ Lam (Id uniq) b''

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
     -- possibly what you want to do is, in the last unification case, the failure one, go through each equality you have, zonk it, and check if it matches (possibly accounting for sym, probably not trans)
     -- Although is that really necessary? If we can choose not to account for trans, can we just choose to have the player transport everything manually? I think yes
-- TODO I think TcM actually needs to keep track of both Var terms and Var types (for Pi and Lam binders), since if we're evalling deep in a term we need to be able to access bindings from further out
    --  Wait that might not be true, because we only introduce new terms when evalling App, and then at the end of eval all vars should be replaced I think
  unify' = \cases
    (UV u) (UV u') | u == u' -> pure $ UV u -- minor optimization: Only look up uvars if necessary
    u u' -> join $ go <$> lift (normalize u) <*> lift (normalize u')
    where
      go :: Inferring -> Inferring -> WriterT (DList UnificationFailure) TcM Inferring
      go = \cases
        (Univ n) (Univ n') -> when (n /= n') (raise $ Can'tUnifyLevels n n') *> pure (Univ n)
        (UV u) (UV u')
          | u == u' -> pure (UV u)
          | otherwise -> lift (substUVar u' (UV u)) >> pure (UV u) -- order doesn't really matter, but it seems reasonable to take the expected as "ground truth"
        e (UV u') -> lift (substUVar u' e) >> pure e
        (UV u) e -> lift (substUVar u e) >> pure e
        (Expr t) (Expr t') -> Expr <$> unify' t t'
        t t' -> raise (Can'tUnifyTypes t t') *> pure t

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

-- TODO wait a minute... Is zonk just normalize at this point
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
    App f x -> App <$> zonk f <*> zonk x
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
    App f x -> App <$> rename' orig new f <*> rename' orig new x
    Pi i t b -> Pi i <$> rename' orig new t <*> if i.id == orig then pure b else rename' orig new b
    Lam i b -> Lam i <$> if i.id == orig then pure b else rename' orig new b

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

toChecked :: Inferring -> MaybeT TcM Checked
toChecked = lift . zonk >=> \case
  Univ n -> pure $ Univ n
  Expr (e ::: t) -> do
    t' <- toChecked t
    e' <- case e of
      Nonsense p -> do
        lift . raise $ HasNonsense p
        hoistMaybe Nothing
      Var a -> pure $ Var a
      App f x -> App <$> toChecked f <*> toChecked x
      Pi (Id x) a b -> Pi (Id x) <$> toChecked a <*> toChecked b
      Lam (Id x) b -> Lam (Id x) <$> toChecked b

      Bottom -> pure Bottom
      Top -> pure Top
      TT -> pure TT
    pure $ Expr (e' ::: t')
  UV u -> do
    lift . raise $ StillHasUnifs u
    hoistMaybe Nothing

extractDecls :: Module PChecked -> Map Id (TypeOrTerm Checked)
extractDecls (Module decls _) = M.fromList $ map (\(Decl name _ term) -> (name, Term term)) decls

inferModule :: Module PParsed -> TcM (Module PInferring)
inferModule (Module declarations mainExpr) = case declarations of
  [] -> Module [] <$> traverse infer mainExpr
  decl:decls -> do
    decl'@(Decl name () term) <- inferDecl decl
    ty <- typeOf term
    (Module decls' mainExpr') <- withBinding name (Type ty) (inferModule (Module decls mainExpr))
    pure $ Module (decl':decls') mainExpr'
    where
      inferDecl :: Decl PParsed -> TcM (Decl PInferring)
      inferDecl (Decl name ty term) = do
        ty' <- infer ty
        term' <- check ty' term
        pure $ Decl name () term'

checkModule :: Module PParsed -> TcM (Maybe (Module PChecked))
checkModule mod' = do
  Module decls mainExpr <- inferModule mod'
  runMaybeT $ Module
    <$> traverse checkDecl decls
    <*> traverse toChecked mainExpr
  where
    checkDecl :: Decl PInferring -> MaybeT TcM (Decl PChecked)
    checkDecl (Decl name () term) = Decl name () <$> toChecked term

-- TODO: termination checker -- actually this is not necessary if we support inductive types
-- | Check takes a type and a parsed expression that is expected to have that type
check :: Inferring -> Parsed -> TcM Inferring
check expected expr = case expr of
  Univ n -> do
    let uType = Univ (n + 1)
    (ty, errs) <- unify expected uType
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
    App f x -> do
      i <- Uniq <$> freshUnique Nothing
      a <- UV <$> freshUVar
      b <- UV <$> freshUVar
      k <- UV <$> freshUVar
      f' <- check (Expr (Pi (Id i) a b ::: k)) f
      x' <- check a x
      b' <- tryUnify f expected =<< fillInArg x' =<< typeOf f'
      pure (Expr $ App f' x' ::: b')
    Pi x' a b -> do
      x <- case x' of
        Id i -> pure i
        Wildcard -> Uniq <$> freshUnique Nothing
      a' <- infer a
      b' <- withBinding x (Type a') $ infer b
      lvl <- maybe 0 (+1) <$> (max <$> inferLevel a' <*> inferLevel b')
      (ty, errs) <- unify expected (Univ lvl)
      case NE.nonEmpty errs of
        Nothing -> pure $ Expr (Pi (Id x) a' b' ::: ty)
        Just es -> do
          raise $ TypeMismatch expr expected (Univ lvl) es
          pure $ Expr (Nonsense expr ::: ty)
    Lam x' rhs -> do
      x <- case x' of
        Id i -> pure i
        Wildcard -> Uniq <$> freshUnique Nothing
      a <- UV <$> freshUVar
      b <- UV <$> freshUVar
      k <- UV <$> freshUVar
      (ty, errs) <- unify expected $ Expr (Pi (Id x) a b ::: k)
      case NE.nonEmpty errs of
        Nothing -> do
          rhs' <- withBinding x (Type a) $ check b rhs
          pure $ Expr (Lam (Id x) rhs' ::: ty)
        Just es -> do
          raise $ TypeMismatch expr expected (Expr (Pi (Id x) a b ::: k)) es
          pure $ Expr (Nonsense expr ::: ty)

    Bottom -> Expr . (Bottom :::) <$> tryUnify expr expected (Univ 0)
    Top -> Expr . (Top :::) <$> tryUnify expr expected (Univ 0)
    TT -> Expr . (TT :::) <$> tryUnify expr expected (Expr (Top ::: Univ 0))
  Hole -> UV <$> freshUVar -- XXX Is this right? It seems like we ignore the expected type. But maybe this will just always result in an unsolved uvar, which might be fine. Otherwise, possibly UVars need to be able to optionally have types. Or a substType that's queried if there is no substTerm for that uvar
  
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

-- | fills in the argument of a Pi type if the given expression is one,
-- returning the body. For other expressions, returns the expression unchanged,
-- but raises an error. Also fills in any other variables and uvars in the body
-- that can be filled in.
fillInArg :: Inferring -> Inferring -> TcM Inferring
fillInArg filler (Expr (Pi x _ b ::: _)) = withBinding x.id (Term filler) $ normalize b
fillInArg _ e = do
  raise $ Bug $ "fillInArg called with non-Pi/Lam expression: " <> T.pack (show e)
  pure e

-- infer should not use unify, and instead call check.
infer :: Parsed -> TcM Inferring
infer expr = case expr of
  Univ n -> pure $ Univ n
  Expr (Identity e) -> case e of
    Var a -> do
      varT <- lookupVarType a
      pure (Expr $ Var a ::: varT)
    App f x -> do
      a <- UV <$> freshUVar
      b <- UV <$> freshUVar
      i <- Uniq <$> freshUnique Nothing
      k <- UV <$> freshUVar
      f' <- check (Expr (Pi (Id i) a b ::: k)) f
      x' <- check a x
      b' <- fillInArg x' =<< typeOf f'
      pure (Expr $ App f' x' ::: b')
    Pi x' a b -> do
      x <- case x' of
        Id i -> pure i
        Wildcard -> Uniq <$> freshUnique Nothing
      a' <- infer a
      b' <- withBinding x (Type a') $ infer b
      lvl <- maybe 0 (+1) <$> (max <$> inferLevel a' <*> inferLevel b')
      pure (Expr $ Pi (Id x) a' b' ::: Univ lvl)
    Lam x' b -> do
      x <- case x' of
        Id i -> pure i
        Wildcard -> Uniq <$> freshUnique Nothing
      aUV <- freshUVar
      let a = UV aUV
      b' <- withBinding x (Type a) $ infer b
      bt <- typeOf b'
      lvl <- maybe 0 (+1) <$> (max <$> inferLevel a <*> inferLevel bt)
      -- TODO Q: If we later substitute x in bt, does that mean inference has to be able to use x in bt? Maybe not, if we say dependent types can't be inferred
      -- TODO do we need this to be able to infer a type for e.g. \x.x?
      -- TODO idea for that: Wrap infer lambda with something that checks if the bound var is not subst'd, and then make a Pi if so
      -- TODO except it doesn't quite work like that, because we have no inferred arguments. So \x.x cannot be generalized. What about \t.\x.the t x?
      -- TODO we could decide to default to Type in a case like \x.x
      pure (Expr $ Lam (Id x) b' ::: Expr (Pi (Id x) a bt ::: Univ lvl))

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

class (NotParsed p, MonadReader (Vars (UExpr (Typed p) p)) (PassMonad p)) => Eval p where
  type PassMonad p :: Type -> Type
  zonkUnchecked :: UExpr (Typed p) p -> PassMonad p (UExpr (Typed p) p)
  evalTypes :: Bool

class NotParsed p where notParsed :: p :~: PParsed -> Void
instance NotParsed PInferring where notParsed = \case
instance NotParsed PChecked where notParsed = \case

data WasReduced = WasReduced deriving Show

instance Semigroup WasReduced where _ <> _ = WasReduced

eval_ :: (Eval p, m ~ PassMonad p, e ~ UExpr (Typed p) p) => e -> m e
eval_ = fmap fst . runWriterT . eval

-- | Brings an expression to normal form
eval :: (Eval p, m ~ PassMonad p, e ~ UExpr (Typed p) p) => e -> WriterT (Maybe WasReduced) m e
eval = lift . zonkUnchecked >=> go
  where
    go e = do
      (e', wasReduced) <- listen $ step e
      if isJust wasReduced then go e' else pure e'

instance Eval PInferring where
  type PassMonad PInferring = TcM
  evalTypes = True
  zonkUnchecked = zonk

instance Eval PChecked where
  type PassMonad PChecked = Reader (Vars Checked)
  evalTypes = False
  zonkUnchecked = pure

type HasVars :: (Type -> Type) -> Constraint
class HasVars m where
  type Var m :: Type

instance HasVars TcM where
  type Var TcM = Inferring

-- TODO resolve variables
{-# SPECIALIZE step :: Inferring -> WriterT (Maybe WasReduced) TcM Inferring #-}
{-# SPECIALIZE step :: Checked -> WriterT (Maybe WasReduced) (Reader (Vars Checked)) Checked #-}
-- | Step through a single pass of the typechecker and return the new expression and whether it was reduced
step :: (Eval p, m ~ PassMonad p, e ~ UExpr (Typed p) p) => e -> WriterT (Maybe WasReduced) m e
step @p = \case
  u@(Univ _) -> pure u
  Expr (e ::: t) -> do
    t' <- if evalTypes @p then step t else pure t
    let withType x = Expr (x ::: t')
    e' <- case e of
      Nonsense e' -> pure . withType $ Nonsense e'

      Var a -> do
        lookupVar a <&> \case
          Just (Term term) -> term
          _ -> withType $ Var a -- We allow using vars that are out of scope here, it'll just not be reduced
      App f x -> do
        f' <- eval f
        x' <- eval x
        case f' of
          Expr (extract -> Lam i rhs) -> do
            tellHasReduced
            withBinding i.id (Term x') $ step rhs
          _ -> pure . withType $ App f' x'
      Pi x a b -> do
        a' <- step a
        b' <- step b
        pure . withType $ Pi x a' b'
      Lam x b -> withType . Lam x <$> step b

      Bottom -> pure . withType $ Bottom
      Top -> pure . withType $ Top
      TT -> pure . withType $ TT
    pure e'
  UV u -> pure $ UV u
  Hole -> absurd $ notParsed Refl
  where
    tellHasReduced = tell (Just WasReduced)

runTcM :: TcM a -> (a, [Error])
runTcM @a action = runRWS withZonkedErrors M.empty (TcState 0 0 IM.empty) &
  \((a, errs), _, _) -> (a, errs)
  where
    -- By zonking at the very end, we can ensure the errors contain all useful data
    withZonkedErrors :: TcM (a, [Error])
    withZonkedErrors = do
      (a, errs) <- RWS.listen action
      traverse zonkError (dListToList errs) >>= pure . (a,)

    zonkError :: Error -> TcM Error
    zonkError = \case
      TypeMismatch e expt act errs -> TypeMismatch e <$> zonk act <*> zonk expt <*> traverse zonkUFails errs
      e -> pure e

    zonkUFails :: UnificationFailure -> TcM UnificationFailure
    zonkUFails = \case
      Can'tUnifyTypes expt act -> Can'tUnifyTypes <$> zonk act <*> zonk expt
      Can'tUnifyExprs expt act -> Can'tUnifyExprs <$> zonk act <*> zonk expt
      Can'tUnifyNonsense expt act -> pure $ Can'tUnifyNonsense expt act
      Can'tUnifyVars v v' -> pure $ Can'tUnifyVars v v'
      Can'tUnifyLevels l l' -> pure $ Can'tUnifyLevels l l'
      Can'tUnifyUVarInApp e -> Can'tUnifyUVarInApp <$> zonk e
