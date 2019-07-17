module Subst where

import           Type

type Subst = [(TV, Type)]

class Substitutable a where
  apply :: Subst -> a -> a

instance Substitutable Type where
  apply s (TVar tv) = case lookup tv s of
    Just t -> t
    _      -> TVar tv
  apply s (TApp t1 t2) = TApp (apply s t1) (apply s t2)
  apply _ t = t

instance Substitutable Scheme where
  apply s (Forall n t) = Forall n $ apply s t

instance Substitutable a => Substitutable [a] where
  apply s = fmap (apply s)

nullSubst :: Subst
nullSubst = []

mergeSubst :: Subst -> Subst -> Subst
mergeSubst s1 s2 = [ (u, apply s1 t) | (u, t) <- s2 ] ++ s1

mergeSubsts :: [Subst] -> Subst
mergeSubsts = foldr mergeSubst nullSubst
