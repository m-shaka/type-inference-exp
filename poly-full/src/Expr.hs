module Expr where

type Name = String

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

fvars :: Expr -> [Name]
fvars (Var n)         = [n]
fvars (Lam x e)       = [n | n <- fvars e, n /= x]
fvars (App e1 e2)     = fvars e1 ++ fvars e2
fvars (BinOp _ e1 e2) = fvars e1 ++ fvars e2
fvars _               = []
