import           Test.Hspec

import qualified BindGroup           as BG
import           Control.Monad.State
import           Expr
import           Infer
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

  describe "bindGroup" $
    it "mutual recursion" $ do
      let Right bg = BG.run binds env
      bg `shouldBe` [[("f", f), ("g", g)], [("h", h)], [("n", n)]]

  describe "infer" $
    it "mutual recursion" $ do
      let Right bg = BG.run binds env
          Right env' = infer env bg
      let int2int = tFun (TCon "Int") (TCon "Int")
      env' `shouldBe` [("n",Forall 0 (TCon "Int")),("h",Forall 0 (TCon "Int")),("f",Forall 0 int2int),("g",Forall 0 int2int)]
