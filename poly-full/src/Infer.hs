{-# LANGUAGE LambdaCase #-}

module Infer where

import           Expr
import           Subst
import           Type

import           Control.Monad.State
import           Data.List           (union)
import           Data.Maybe          (fromJust)

type Infer a = StateT Int (Either String) a


type Env = [(String, Scheme)]

freshTVar :: Infer Type
freshTVar = do
  s <- get
  put $ s + 1
  pure . TVar . TV $ letters !! s
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

unify :: Type -> Type -> Infer Subst
unify (TVar tv)     t2            = bind tv t2
unify t1            (TVar tv    ) = bind tv t1
unify (TApp t1 t1') (TApp t2 t2') = do
  s1 <- unify t1 t2
  s2 <- unify (apply s1 t1') (apply s1 t2')
  pure $ mergeSubst s2 s1
unify (TCon tc1) (TCon tc2) | tc1 == tc2 = pure []
unify t1 t2               = lift . Left $ "types do not unify: " ++ show t1 ++ " and " ++ show t2

bind :: TV -> Type -> Infer Subst
bind u t | t == TVar u     = pure []
         | u `elem` tvar t = lift $ Left "infinite type. "
         | otherwise       = pure [(u, t)]

tvar :: Type -> [TV]
tvar (TVar u    ) = [u]
tvar (TApp t1 t2) = tvar t1 `union` tvar t2
tvar t@TCon{}     = []

inferExpr :: Env -> Expr -> Infer (Type, Subst)
inferExpr env = \case
  Var v -> do
    t <- freshInst . fromJust $ lookup v env
    pure (t, [])
  Int i -> pure (tInt, [])
  Bool b -> pure (tBool, [])
  Lam x e -> do
    targ <- freshTVar
    (t1, s1) <- inferExpr ((x, toScheme targ) : env) e
    pure (apply s1 $ tFun targ t1, s1)
  App e1 e2 -> do
    (t1, s1) <- inferExpr env e1
    (t2, s2) <- inferExpr env e2
    tv <- freshTVar
    tvSbst <- unify (tFun t2 tv) t1
    let sbst = mergeSubsts [tvSbst, s1, s2]
    pure (apply sbst tv, sbst)


infer :: Env -> Expr -> Either String Type
infer env expr = (\(t, s) -> apply s t) <$> evalStateT (inferExpr env expr) 0

infer' :: Env -> Expr -> Either String (Type, Subst)
infer' env expr = evalStateT (inferExpr env expr) 0

