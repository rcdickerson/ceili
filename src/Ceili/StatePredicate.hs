module Ceili.StatePredicate
  ( StatePredicate(..)
  ) where

import Ceili.Assertion
import Ceili.Name
import Ceili.State
import qualified Data.Map as Map

class StatePredicate a where
  testState :: a -> State -> Bool

instance StatePredicate Assertion where
  testState assertion state = case assertion of
    ATrue     -> True
    AFalse    -> False
    Atom _    -> False -- This assumes states cannot store booleans.
    Not a     -> not $ testState a state
    And as    -> and $ map (\a -> testState a state) as
    Or  as    -> or  $ map (\a -> testState a state) as
    Imp a1 a2 -> not (testState a1 state) || testState a2 state
    Eq  a1 a2 -> (evalArith a1 state) == (evalArith a2 state)
    Lt  a1 a2 -> (evalArith a1 state) < (evalArith a2 state)
    Gt  a1 a2 -> (evalArith a1 state) > (evalArith a2 state)
    Lte a1 a2 -> (evalArith a1 state) <= (evalArith a2 state)
    Gte a1 a2 -> (evalArith a1 state) >= (evalArith a2 state)
    Forall _ _ -> error "Quantified formulas not supported."
    Exists _ _ -> error "Quantified formulas not supported."

evalArith :: Arith -> State -> Integer
evalArith arith state = case arith of
  Num i     -> i
  Var v     -> case Map.lookup (tn_name v) state of
                 Nothing -> 0
                 Just n  -> n
  Add as    -> foldr (+) 0 $ map (\a -> evalArith a state) as
  Sub as    -> case as of
                 []      -> 0
                 (a:as') -> foldl (-) (evalArith a state)
                           $ map (\a' -> evalArith a' state) as'
  Mul as    -> foldr (*) 1 $ map (\a -> evalArith a state) as
  Div a1 a2 -> (evalArith a1 state) `quot` (evalArith a2 state)
  Mod a1 a2 -> (evalArith a1 state) `mod` (evalArith a2 state)
  Pow a1 a2 -> (evalArith a1 state) ^ (evalArith a2 state)
