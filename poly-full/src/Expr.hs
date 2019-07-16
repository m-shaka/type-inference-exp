module Expr where

import           Control.Monad.Catch
import           Control.Monad.Except
import           Data.Foldable
import           Data.Functor.Identity (runIdentity)
import           Data.List             ((\\))
import qualified Data.Map              as Map
import           Data.Maybe            (fromJust)

type Name = String

type Index = Int

data Expr =
  Var Name
  | Int Int
  | Bool Bool
  | Lam Name Expr
  | App Expr Expr
  | BinOp BinOp Expr Expr
  deriving (Eq, Show)

data BinOp =
  Plus
  | Multi
  deriving (Eq, Show)

type Bind = (Name, Expr)

type BindGroup = [[Bind]]

newtype BindError =
  UndefinedVar Name
  deriving(Eq, Show)

instance Exception BindError

type WithBindError = Except BindError

fvars :: Expr -> [Name]
fvars (Var n)         = [n]
fvars (Lam x e)       = [n | n <- fvars e, n /= x]
fvars (App e1 e2)     = fvars e1 ++ fvars e2
fvars (BinOp _ e1 e2) = fvars e1 ++ fvars e2
fvars _               = []

findDeps :: [Bind] -> [Name] -> WithBindError [(Index, Index)]
findDeps binds tenvNames = foldrM foldFunc [] binds
  where
    bindNames = fmap fst binds
    nameToIndex = Map.fromList $ zip bindNames [0..]
    lookupFv :: Index -> Name -> WithBindError (Index, Index)
    lookupFv i varName = case Map.lookup varName nameToIndex of
      Just i' -> pure (i, i')
      _       -> throwError $ UndefinedVar varName
    find (name, expr) = do
      let fv = fvars expr \\ (bindNames ++ tenvNames)
          srcIndex = fromJust $ Map.lookup name nameToIndex
      traverse (lookupFv srcIndex) fv
    foldFunc bind acc = do
      indices <- find bind
      pure $ indices ++ acc

run :: [Bind] -> [Name] -> Either BindError [(Index, Index)]
run binds tenvNames = runIdentity . runExceptT $ findDeps binds tenvNames
