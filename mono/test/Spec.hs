import           Test.Hspec

import           Infer
import           Type

main :: IO ()
main = hspec $ do
  let env = [("x", tBool), ("toInt", tFun tBool tInt)]
  describe "infer" $ do
    it "var" $ do
      let Right t = infer env (Var "x")
      t `shouldBe` tBool
    it "int" $ do
      let Right t = infer env (Int 0)
      t `shouldBe` tInt
    it "bool" $ do
      let Right t = infer env (Bool True)
      t `shouldBe` tBool
    it "lambda" $ do
      let Right t = infer env (Lam "x" (App (Var "toInt") (Var "x")))
      t `shouldBe` tFun tBool tInt
    it "app" $ do
      let Right t = infer env (App (Var "toInt") (Bool False))
      t `shouldBe` tInt
