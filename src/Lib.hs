module Lib
  ( someFunc
  )
where

import           Typing

import qualified Data.Map                      as Map

someFunc :: IO ()
someFunc = do
  let decls  = [("main", Var "f"), ("f", Var "g"), ("g", Int 3)]
  let decls2 = [("main", Var "f"), ("f", Lam "g" (Var "g")), ("g", Bool True)]
  inferMain Map.empty decls2 >>= print
