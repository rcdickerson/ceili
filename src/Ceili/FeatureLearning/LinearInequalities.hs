module Ceili.FeatureLearning.LinearInequalities
  ( linearInequalities
  ) where

import Ceili.Assertion ( Arith(..), Assertion(..) )
import qualified Ceili.InvariantInference.CollectionUtil as Collection
import Ceili.Name
import Data.Set ( Set )
import qualified Data.Set as Set

-- Enumerate all inequalities of the form i*x + j*y + k*z + ... <= m where:
-- + The left-hand sizde of each inequality has `size` terms.
-- + Each tuple of (i, j, k, ..., m) are drawn from `lits` union {-1, 0, 1}.
-- + Each (x, y, z, ...) are drawn from `names`.
-- + The same `lits` may appear multiple places in the inequality, but each
--   `name` will appear at most once.
-- + If `size` is larger than the set of available names, it is implicity
--   reduced to the largest value the given set of names accomodates.
linearInequalities :: (Num t, Ord t) => Set Name -> Set t -> Int -> Set (Assertion t)
linearInequalities names lits size = let
  size' = if (Set.size names < size) then Set.size names else size
  arithLits   = Set.map Num $ Set.insert 0
                            $ Set.insert 1
                            $ Set.insert (-1)
                              lits
  varNames    = Set.map Var names
  varGroups   = Collection.subsetsOfSize size' varNames
  in Set.unions $ Set.map (constructLCs arithLits) varGroups

constructLCs :: (Num t, Ord t) => Set (Arith t) -> Set (Arith t) -> Set (Assertion t)
constructLCs lits vars = let
  lhss = Set.map addOrSingle $
         Set.filter (not . null) $
         Set.map simplifyMults $
         constructLhss lits vars
  in Set.map (uncurry Lte) $ Set.cartesianProduct lhss lits

addOrSingle :: [Arith t] -> Arith t
addOrSingle as =
  case as of
    a:[] -> a
    _    -> Add as

constructLhss :: Ord t => Set (Arith t) -> Set (Arith t) -> Set [Arith t]
constructLhss lits vars =
  case Set.size vars of
    0 -> Set.empty
    1 -> let hd = Set.elemAt 0 vars
         in Set.map (\i -> [Mul[i, hd]]) lits
    _ -> let
      (hd, vars') = Set.deleteFindMin vars
      hds = Set.map (\i -> Mul[i, hd]) lits
      rests = constructLhss lits vars'
      in Set.map (uncurry (:)) $ Set.cartesianProduct hds rests

simplifyMult :: (Num t, Eq t) => Arith t -> Arith t
simplifyMult arith =
  case arith of
    Mul [] -> Num 0
    Mul as -> if any (== Num 0) as then Num 0
              else case filter (/= Num 1) as of
                     []   -> Num 1
                     a:[] -> a
                     as'  -> Mul as'
    _      -> arith

simplifyMults :: (Num t, Eq t) => [Arith t] -> [Arith t]
simplifyMults ariths = filter (/= Num 0) $ map simplifyMult ariths
