module Type where

newtype TV = TV String deriving(Eq, Show)

data Type =
  TVar TV
  | TCon String
  | TApp Type Type
  deriving (Eq, Show)

tInt = TCon "Int"
tBool = TCon "Bool"
tArrow = TCon "->"

tFun :: Type -> Type -> Type
tFun t1 = TApp (TApp tArrow t1)
