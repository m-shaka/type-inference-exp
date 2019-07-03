{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE LambdaCase #-}
module Typing where

import qualified Assumption                    as As

import           Type

import           Control.Monad.Except
import           Control.Monad.State
import           Control.Monad.Reader
import           Control.Monad.Identity
import           Control.Monad.IO.Class
import           Data.List                      ( delete
                                                , find
                                                , nub
                                                )
import           Data.Maybe                     ( fromJust )
import qualified Data.Map                      as Map
import qualified Data.Set                      as Set
import qualified Data.List                     as List


data Expr =
  Var String
  | Int Int
  | Bool Bool
  | App Expr Expr
  | Lam String Expr
  deriving (Show, Eq)

-------------------------------------------------------------------------------
-- Classes
-------------------------------------------------------------------------------
data Constraint = EqConst Type Type
                | ExpInstConst Type ACT
                -- | ImpInstConst Type (Set.Set TVar) Type
                deriving (Show, Eq, Ord)


type Env = Map.Map String ACT

newtype ACT = ACT (As.Assumption, [Constraint], Type) deriving(Show, Eq, Ord)


-- | Inference monad
type Infer a
  = (ReaderT (Set.Set TVar) (StateT InferState (ExceptT TypeError IO)) a)

-- | Inference state
data InferState = InferState { count :: Int }

-- | Initial inference state
initInfer :: InferState
initInfer = InferState { count = 0 }

newtype Subst = Subst (Map.Map TVar Type)
  deriving (Eq, Ord, Show, Semigroup, Monoid)


class Substitutable a where
  apply :: Subst -> a -> a

instance Substitutable TVar where
  apply (Subst s) a = tv
   where
    t         = TVar a
    (TVar tv) = Map.findWithDefault t a s

instance Substitutable Type where
  apply _         (  TCon a      ) = TCon a
  apply (Subst s) t@(TVar a      ) = Map.findWithDefault t a s
  apply s         (  t1 `TArr` t2) = apply s t1 `TArr` apply s t2

instance Substitutable Scheme where
  apply (Subst s) (Forall as t) = Forall as $ apply s' t
    where s' = Subst $ foldr Map.delete s as

instance Substitutable Constraint where
  apply s (EqConst      t1 t2) = EqConst (apply s t1) (apply s t2)
  apply s (ExpInstConst t  sc) = ExpInstConst (apply s t) (apply s sc)
  -- apply s (ImpInstConst t1 ms t2) =
  --   ImpInstConst (apply s t1) (apply s ms) (apply s t2)

instance Substitutable a => Substitutable [a] where
  apply = map . apply

instance (Ord a, Substitutable a) => Substitutable (Set.Set a) where
  apply = Set.map . apply

instance Substitutable ACT where
  apply s (ACT (as, cs, t)) = ACT (as, apply s cs, apply s t)

class FreeTypeVars a where
  ftv :: a -> Set.Set TVar

instance FreeTypeVars Type where
  ftv TCon{}         = Set.empty
  ftv (TVar a      ) = Set.singleton a
  ftv (t1 `TArr` t2) = ftv t1 `Set.union` ftv t2

instance FreeTypeVars TVar where
  ftv = Set.singleton

instance FreeTypeVars Scheme where
  ftv (Forall as t) = ftv t `Set.difference` Set.fromList as

instance FreeTypeVars a => FreeTypeVars [a] where
  ftv = foldr (Set.union . ftv) Set.empty

instance (Ord a, FreeTypeVars a) => FreeTypeVars (Set.Set a) where
  ftv = foldr (Set.union . ftv) Set.empty

-- instance FreeTypeVars ACT where
--   ftv (ACT (as, _, _)) =
class ActiveTypeVars a where
  atv :: a -> Set.Set TVar

instance ActiveTypeVars Constraint where
  atv (EqConst      t1 t2              ) = ftv t1 `Set.union` ftv t2
-- atv (ImpInstConst t1 ms t2) =
--   ftv t1 `Set.union` (ftv ms `Set.intersection` ftv t2)
  atv (ExpInstConst t  (ACT (_, _, t'))) = ftv t `Set.union` ftv t'

instance ActiveTypeVars a => ActiveTypeVars [a] where
  atv = foldr (Set.union . atv) Set.empty


data TypeError
  = UnificationFail Type Type
  | InfiniteType TVar Type
  | UnboundVariable String
  | Ambigious [Constraint]
  | UnificationMismatch [Type] [Type]
  | MainNotDeclared
  deriving(Show)

-------------------------------------------------------------------------------
-- Inference
-------------------------------------------------------------------------------

-- | Run the inference monad
runInfer :: Infer a -> IO (Either TypeError a)
runInfer m = runExceptT $ evalStateT (runReaderT m Set.empty) initInfer

inferType :: Env -> ACT -> Infer (Subst, Scheme)
inferType env (ACT (as, cs, t)) = do
  liftIO $ print env
  let (_, assumptions) =
        unzip . Map.toList $ Map.map (\(ACT (as, _, _)) -> as) env
  let mergedAs = foldr As.merge as assumptions
  let unbounds = Set.fromList (As.keys mergedAs)
        `Set.difference` Set.fromList (Map.keys env)
  unless (Set.null unbounds) $ throwError $ UnboundVariable
    (Set.findMin unbounds)
  let cs' =
        [ ExpInstConst t' s
        | (x, s@(ACT (as', _, _))) <- Map.toList env
        , t'                       <- As.lookup x mergedAs
        ]
  subst <- solve (cs ++ cs')
  return (subst, closeOver $ apply subst t)

-- | Solve for the toplevel type of an expression in a given environment
-- inferExpr :: Env -> Expr -> Either TypeError Scheme
-- inferExpr env ex = case runInfer (inferType env ex) of
--   Left  err         -> Left err
--   Right (subst, ty) -> Right $ closeOver $ apply subst ty

-- | Canonicalize and return the polymorphic toplevel type.
closeOver :: Type -> Scheme
closeOver = normalize . generalize Set.empty

extendMSet :: TVar -> Infer a -> Infer a
extendMSet x = local (Set.insert x)

letters :: [String]
letters = [1 ..] >>= flip replicateM ['a' .. 'z']

fresh :: Infer TVar
fresh = do
  s <- get
  put s { count = count s + 1 }
  return $ TV (letters !! count s)

instantiate :: Scheme -> Infer Type
instantiate (Forall as t) = do
  as' <- mapM (const (TVar <$> fresh)) as
  let s = Subst $ Map.fromList $ zip as as'
  return $ apply s t

generalize :: Set.Set TVar -> Type -> Scheme
generalize free t = Forall as t
  where as = Set.toList $ ftv t `Set.difference` free

infer :: Expr -> Infer (As.Assumption, [Constraint], Type)
infer expr = case expr of
  Int  _ -> return (As.empty, [], typeInt)
  Bool _ -> return (As.empty, [], typeBool)

  Var  x -> do
    tv <- TVar <$> fresh
    return (As.singleton x tv, [], tv)

  Lam x e -> do
    a <- fresh
    let tv = TVar a
    (as, cs, t) <- extendMSet a (infer e)
    return
      ( as `As.remove` x
      , cs ++ [ EqConst t' tv | t' <- As.lookup x as ]
      , tv `TArr` t
      )

  App e1 e2 -> do
    (as1, cs1, t1) <- infer e1
    (as2, cs2, t2) <- infer e2
    tv             <- TVar <$> fresh
    return (as1 `As.merge` as2, cs1 ++ cs2 ++ [EqConst t1 (t2 `TArr` tv)], tv)


inferMain :: Env -> [(String, Expr)] -> IO (Either TypeError Type)
inferMain env []    = pure $ Left MainNotDeclared
inferMain env decls = runInfer (inferMain' env decls) >>= \case
  Right (subst, Forall _ t) -> pure $ Right t
  Left  e                   -> pure $ Left e
 where
  inferMain' env decls = do
    acts <- Map.fromList <$> traverse inferDecl decls
    -- liftIO $ print acts
    case Map.lookup "main" acts of
      Just act -> inferType (Map.union env acts) act
      Nothing  -> throwError MainNotDeclared
  inferDecl (n, expr) = do
    act <- infer expr
    return (n, ACT act)
-- inferTop env []                = Right env
-- inferTop env ((name, ex) : xs) = case inferExpr env ex of
--   Left  err -> Left err
--   Right ty  -> inferTop (extend env (name, ty)) xs

normalize :: Scheme -> Scheme
normalize (Forall _ body) = Forall (map snd ord) (normtype body)
 where
  ord = zip (nub $ fv body) (map TV letters)

  fv (TVar a  ) = [a]
  fv (TArr a b) = fv a ++ fv b
  fv (TCon _  ) = []

  normtype (TArr a b) = TArr (normtype a) (normtype b)
  normtype (TCon a  ) = TCon a
  normtype (TVar a  ) = case Prelude.lookup a ord of
    Just x  -> TVar x
    Nothing -> error "type variable not in signature"

-------------------------------------------------------------------------------
-- Constraint Solver
-------------------------------------------------------------------------------

-- | The empty substitution
emptySubst :: Subst
emptySubst = mempty

-- | Compose substitutions
compose :: Subst -> Subst -> Subst
(Subst s1) `compose` (Subst s2) =
  Subst $ Map.map (apply (Subst s1)) s2 `Map.union` s1

unifyMany :: [Type] -> [Type] -> Infer Subst
unifyMany []         []         = return emptySubst
unifyMany (t1 : ts1) (t2 : ts2) = do
  su1 <- unifies t1 t2
  su2 <- unifyMany (apply su1 ts1) (apply su1 ts2)
  return (su2 `compose` su1)
unifyMany t1 t2 = throwError $ UnificationMismatch t1 t2

unifies :: Type -> Type -> Infer Subst
unifies t1 t2 | t1 == t2          = return emptySubst
unifies (TVar v)     t            = v `bind` t
unifies t            (TVar v    ) = v `bind` t
unifies (TArr t1 t2) (TArr t3 t4) = unifyMany [t1, t2] [t3, t4]
unifies t1           t2           = throwError $ UnificationFail t1 t2

bind :: TVar -> Type -> Infer Subst
bind a t | t == TVar a     = return emptySubst
         | occursCheck a t = throwError $ InfiniteType a t
         | otherwise       = return (Subst $ Map.singleton a t)

occursCheck :: FreeTypeVars a => TVar -> a -> Bool
occursCheck a t = a `Set.member` ftv t

nextSolvable :: [Constraint] -> (Constraint, [Constraint])
nextSolvable xs = fromJust (find solvable (chooseOne xs))
 where
  chooseOne xs = [ (x, ys) | x <- xs, let ys = delete x xs ]
  solvable (EqConst{}     , _) = True
  solvable (ExpInstConst{}, _) = True
  -- solvable (ImpInstConst t1 ms t2, cs) =
  --   Set.null ((ftv t2 `Set.difference` ms) `Set.intersection` atv cs)

solve :: [Constraint] -> Infer Subst
solve [] = return emptySubst
solve cs = solve' (nextSolvable cs)

solve' :: (Constraint, [Constraint]) -> Infer Subst
solve' (EqConst t1 t2, cs) = do
  su1 <- unifies t1 t2
  su2 <- solve (apply su1 cs)
  return (su2 `compose` su1)
-- solve' (ImpInstConst t1 ms t2, cs) =
--   solve (ExpInstConst t1 (generalize ms t2) : cs)
solve' (ExpInstConst t (ACT (_, cs', t')), cs) =
  -- s' <- instantiate s
  solve (EqConst t t' : cs' ++ cs)
