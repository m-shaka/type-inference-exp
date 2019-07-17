{-# LANGUAGE LambdaCase #-}

module Infer where

import qualified BindGroup           as BG
import           Expr
import           Subst
import           Type

import           Control.Monad.State
import           Data.Foldable
import           Data.List           (union, (\\))
import           Data.Maybe          (fromJust)
type Infer a = StateT (Int, Subst) (Either String) a

type Env = [(String, Scheme)]

class FTV a where
  tvar :: a -> [TV]

instance FTV Type where
  tvar (TVar u    ) = [u]
  tvar (TApp t1 t2) = tvar t1 `union` tvar t2
  tvar t            = []

instance FTV Scheme where
  tvar (Forall _ t) = tvar t

freshTVar :: Infer Type
freshTVar = do
  (n, s) <- get
  put (n + 1, s)
  pure . TVar . TV $ letters !! n
  where
    letters = [1..] >>= flip replicateM ['a'..'z']

freshInst :: Scheme -> Infer Type
freshInst (Forall n t) = do
  ts <- mapM (const freshTVar) [1 .. n]
  pure $ inst ts t

inst :: [Type] -> Type -> Type
inst ts (TApp l r) = TApp (inst ts l) (inst ts r)
inst ts (TGen n )  = ts !! n
inst _  t          = t

toScheme :: Type -> Scheme
toScheme = Forall 0

unify :: Type -> Type -> Infer ()
unify t1 t2 = do
  s <- getSubst
  s' <- mgu (apply s t1) (apply s t2)
  extSubst s'

mgu :: Type -> Type -> Infer Subst
mgu (TVar tv)     t2            = bind tv t2
mgu t1            (TVar tv    ) = bind tv t1
mgu (TApp t1 t1') (TApp t2 t2') = do
  s1 <- mgu t1 t2
  s2 <- mgu (apply s1 t1') (apply s1 t2')
  pure $ mergeSubst s2 s1
mgu (TCon tc1) (TCon tc2) | tc1 == tc2 = pure []
mgu t1 t2               = lift . Left $ "types do not unify: " ++ show t1 ++ " and " ++ show t2

bind :: TV -> Type -> Infer Subst
bind u t | t == TVar u     = pure []
         | u `elem` tvar t = lift $ Left "infinite type. "
         | otherwise       = pure [(u, t)]

quantify      :: [TV] -> Type -> Scheme
quantify vs t = Forall (length s) (apply s t)
 where vs' = [ v | v <- tvar t, v `elem` vs ]
       s = zip vs' (map TGen [0..])

getSubst :: Infer Subst
getSubst = gets snd

extSubst :: Subst -> Infer ()
extSubst s = do
  s' <- mergeSubst s <$> getSubst
  modify $ \(n, _) -> (n, s')

inferExpr :: Env -> Expr -> Infer Type
inferExpr env = \case
  Var v -> freshInst . fromJust $ lookup v env
  Int i -> pure tInt
  Bool b -> pure tBool
  Lam x e -> do
    targ <- freshTVar
    t1 <- inferExpr ((x, toScheme targ) : env) e
    pure $ tFun targ t1
  App e1 e2 -> do
    t1 <- inferExpr env e1
    t2 <- inferExpr env e2
    tv <- freshTVar
    unify (tFun t2 tv) t1
    pure tv
  BinOp _ e1 e2 -> do
    t1 <- inferExpr env e1
    t2 <- inferExpr env e2
    unify tInt t1
    unify tInt t2
    pure tInt

inferBind :: Env -> Expr ->  Type -> Infer ()
inferBind env expr t = do
  t' <- inferExpr env expr
  unify t t'

inferBinds :: Env -> [BG.Bind] -> Infer Env
inferBinds env binds = do
  tempTs <- mapM (const freshTVar) binds
  let tempScs = map toScheme tempTs
      names = map fst binds
      tempEnv = zip names tempScs ++ env
      exprs = map snd binds
  zipWithM_ (inferBind tempEnv) exprs tempTs
  subst <- getSubst
  let ts = apply subst tempTs
      envFtvs = tvar =<< apply subst (fmap snd env)
      tsFtvs = join $ map tvar ts
      scs = map (quantify $ tsFtvs \\ envFtvs) ts
  pure $ zip names scs


inferSeq :: Env -> [a] -> (Env -> a -> Infer Env) -> Infer Env
inferSeq _ [] _ = pure []
inferSeq env (x:xs) inferf = do
  env' <- inferf env x
  env'' <- inferSeq (env' ++ env) xs inferf
  pure $ env'' ++ env'

inferBG :: Env -> BG.BindGroup -> Infer Env
inferBG env bg = inferSeq env bg inferBinds

infer :: Env -> BG.BindGroup -> Either String Env
infer env bg = evalStateT (inferBG env bg) (0, nullSubst)
