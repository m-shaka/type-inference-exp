module BindGroup where

import qualified Expr                  as E

import           Control.Monad
import           Control.Monad.Catch
import           Control.Monad.Except
import           Data.Foldable
import           Data.Functor.Identity
import qualified Data.Graph            as Graph
import           Data.List             ((\\))
import qualified Data.Map              as Map
import           Data.Maybe            (fromJust)

type Index = Int

type Bind = (E.Name, E.Expr)

type BindGroup = [[Bind]]

newtype BindError =
  UndefinedVar E.Name
  deriving (Eq, Show)

instance Exception BindError

type WithBindError = Except BindError

depsEdge :: [Bind] -> [E.Name] -> WithBindError [(Bind, Index, [Index])]
depsEdge binds tenvNames = foldrM foldFunc [] binds
  where
    bindNames = fmap fst binds
    nameToIndex = Map.fromList $ zip bindNames [0..]
    lookupFv :: E.Name -> WithBindError Index
    lookupFv varName = case Map.lookup varName nameToIndex of
      Just i -> pure i
      _      -> throwError $ UndefinedVar varName
    find b@(name, expr) = do
      let fv = E.fvars expr \\ tenvNames
          srcIndex = fromJust $ Map.lookup name nameToIndex
      deps <- traverse lookupFv fv
      pure (b, srcIndex, deps)
    foldFunc bind acc = do
      indices <- find bind
      pure $ indices : acc

buildBindG :: [Bind] -> [E.Name] -> WithBindError BindGroup
buildBindG binds tenvNames = do
  edges <- depsEdge binds tenvNames
  pure . joinScc . Graph.stronglyConnComp $ edges
  where
    joinScc []                      = []
    joinScc (Graph.CyclicSCC vs:es) = vs : joinScc es
    joinScc (Graph.AcyclicSCC v:es) = [v] : joinScc es

run :: [Bind] -> [E.Name] -> Either BindError BindGroup
run binds tenvNames = runIdentity . runExceptT $ buildBindG binds tenvNames
