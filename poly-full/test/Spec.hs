import           Test.Hspec

import qualified BindGroup           as BG
import           Control.Monad.State
import           Expr
import           Infer
import           Subst
import           Type

main :: IO ()
main = hspec $ do
  let n = Int 0
      gx = App (Var "g") (Var "x")
      f = Lam "x" $ BinOp Multi (Int 2) gx
      yPlus1 = BinOp Plus (Var "y") (Int 1)
      g = Lam "y" $ App (Var "f") yPlus1
      h =  App (Var "f") (Int 1)
      binds = [("n", n), ("f", f), ("g", g), ("h", h)]
      env = []

  describe "infer expression" $ do
    let inferExpr' env expr =
          (\(t, (_, s)) -> apply s t) <$> runStateT (inferExpr env expr) (0, [])
        env =
          [("x", toScheme tBool)
          , ("toInt", toScheme $ tFun tBool tInt)
          , ("id", Forall 1 $ tFun (TGen 0) (TGen 0))]

    it "var" $ do
      let Right t = inferExpr' env (Var "x")
      t `shouldBe` tBool
    it "int" $ do
      let Right t = inferExpr' env (Int 0)
      t `shouldBe` tInt
    it "bool" $ do
      let Right t = inferExpr' env (Bool True)
      t `shouldBe` tBool
    it "lambda" $ do
      let Right t = inferExpr' env (Lam "x" (App (Var "toInt") (Var "x")))
      t `shouldBe` tFun tBool tInt
    it "app" $ do
      let Right t = inferExpr' env (App (Var "toInt") (Bool False))
      t `shouldBe` tInt
    it "poly" $ do
      let expr = App (App (Var "id") (Var "toInt")) (App (Var "id") (Var "x"))
          Right t = inferExpr' env expr
      t `shouldBe` tInt

  describe "build bindGroup" $
    it "mutual recursion" $ do
      let Right bg = BG.run binds env
      bg `shouldBe` [[("f", f), ("g", g)], [("h", h)], [("n", n)]]

  describe "infer bingGroup" $
    it "mutual recursion" $ do
      let Right bg = BG.run binds env
          Right env' = infer env bg
          int2int = tFun (TCon "Int") (TCon "Int")
      env' `shouldBe` [("n",Forall 0 (TCon "Int")),("h",Forall 0 (TCon "Int")),("f",Forall 0 int2int),("g",Forall 0 int2int)]
