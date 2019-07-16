import           Test.Hspec

import qualified BindGroup  as BG
import           Expr

main :: IO ()
main = hspec $ do
  describe "bindGroup" $ do
    it "mutual recursion" $ do
      let n = Int 0
          gx = App (Var "g") (Var "x")
          f = Lam "x" $ BinOp Multi (Int 2) gx
          yPlus1 = BinOp Plus (Var "y") (Int 1)
          g = Lam "y" $ App (Var "f") yPlus1
          h =  App (Var "f") (Int 1)
          binds = [("n", n), ("f", f), ("g", g), ("h", h)]
          env = []
          Right bg = BG.run binds env
      bg `shouldBe` [[("f", f), ("g", g)], [("h", h)], [("n", n)]]

