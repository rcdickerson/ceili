module Ceili.InvariantInference.LinearInequalities
  ( linearInequalities
  ) where

import Ceili.Assertion ( Arith(..), Assertion(..) )
import qualified Ceili.InvariantInference.CollectionUtil as Collection
import Ceili.Name ( TypedName, namesIn )
import Data.Maybe ( fromJust, isJust )
import Data.Set ( Set )
import qualified Data.Set as Set

-- Enumerate all inequalities of the form i + j*x + k*y + ... <= v,
-- where the left hand side has `size` terms, (i, j, k, ...) are drawn
-- from `lits` + {-1, 0, 1}, (x, y, ...) are drawn from `names`,
-- and v is drawn from `lits` union `names`. The same `lits` may
-- appear multiple places in the inequality, but each `name` will
-- appear at most once.
linearInequalities :: Set TypedName -> Set Integer -> Int -> Set Assertion
linearInequalities names lits size = let
  size' = if (Set.size names < size) then Set.size names else size
  arithLits   = Set.map Num $ Set.insert 0
                            $ Set.insert 1
                            $ Set.insert (-1)
                              lits
  varNames    = Set.map Var names
  varGroups   = Collection.subsetsOfSize size' varNames
  coeffGroups = Collection.chooseWithReplacement size' arithLits
  combos      = catMaybes $ Set.map (uncurry constructLC) $
                Set.cartesianProduct coeffGroups varGroups
  bounds      = Set.union arithLits varNames
  ineqPairs   = Set.filter (uncurry namesDisjoint) $
                Set.filter (uncurry atLeastOneVar) $
                Set.cartesianProduct combos bounds
  in Set.map (uncurry Lte) ineqPairs

constructLC :: [Arith] -> Set Arith -> Maybe Arith
constructLC coeffs vars = let
  terms = removeZeros $ map (\(c,v) -> Mul [c, v]) $ zip coeffs (Set.toList vars)
  in case terms of
       []     -> Nothing
       (t:[]) -> Just t
       _      -> Just $ Add terms

namesDisjoint :: Arith -> Arith -> Bool
namesDisjoint a b = Set.null $ Set.intersection (namesIn a) (namesIn b)

atLeastOneVar :: Arith -> Arith -> Bool
atLeastOneVar a b = not . Set.null $ Set.union (namesIn a) (namesIn b)

catMaybes :: Ord a => Set (Maybe a) -> Set a
catMaybes set = Set.map fromJust $ Set.filter isJust set

removeZeros :: [Arith] -> [Arith]
removeZeros as = case as of
  [] -> []
  (a:as') -> case a of
               Num 0  -> removeZeros as'
               Mul ms -> if any (== Num 0) ms
                         then removeZeros as'
                         else a:(removeZeros as')
               _        -> a:(removeZeros as')
