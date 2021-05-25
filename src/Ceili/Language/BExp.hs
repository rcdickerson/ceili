module Ceili.Language.BExp
  ( BExp(..)
  , State
  , bexpToAssertion
  , evalBExp
  ) where

import Ceili.Assertion.AssertionLanguage ( Assertion)
import qualified Ceili.Assertion.AssertionLanguage as A
import Ceili.Language.AExp ( AExp(..), State, aexpToArith, evalAExp )
import Ceili.Name ( CollectableNames(..)
                  , MappableNames(..) )
import qualified Data.Set  as Set

-------------------------
-- Boolean Expressions --
-------------------------

data BExp
  = BTrue
  | BFalse
  | BNot BExp
  | BAnd BExp BExp
  | BOr  BExp BExp
  | BEq  AExp AExp
  | BNe  AExp AExp
  | BLe  AExp AExp
  | BGe  AExp AExp
  | BLt  AExp AExp
  | BGt  AExp AExp
  deriving (Eq, Ord, Show)

instance CollectableNames BExp where
  namesIn bexp = case bexp of
    BTrue        -> Set.empty
    BFalse       -> Set.empty
    BNot b       -> namesIn b
    BAnd b1  b2  -> Set.union (namesIn b1)  (namesIn b2)
    BOr  b1  b2  -> Set.union (namesIn b1)  (namesIn b2)
    BEq  lhs rhs -> Set.union (namesIn lhs) (namesIn rhs)
    BNe  lhs rhs -> Set.union (namesIn lhs) (namesIn rhs)
    BLe  lhs rhs -> Set.union (namesIn lhs) (namesIn rhs)
    BGe  lhs rhs -> Set.union (namesIn lhs) (namesIn rhs)
    BLt  lhs rhs -> Set.union (namesIn lhs) (namesIn rhs)
    BGt  lhs rhs -> Set.union (namesIn lhs) (namesIn rhs)

instance MappableNames BExp where
  mapNames _ BTrue        = BTrue
  mapNames _ BFalse       = BFalse
  mapNames f (BNot b)     = BNot $ mapNames f b
  mapNames f (BAnd b1 b2) = BAnd (mapNames f b1) (mapNames f b2)
  mapNames f (BOr b1 b2)  = BOr (mapNames f b1) (mapNames f b2)
  mapNames f (BEq a1 a2)  = BEq (mapNames f a1) (mapNames f a2)
  mapNames f (BNe a1 a2)  = BNe (mapNames f a1) (mapNames f a2)
  mapNames f (BLe a1 a2)  = BLe (mapNames f a1) (mapNames f a2)
  mapNames f (BGe a1 a2)  = BGe (mapNames f a1) (mapNames f a2)
  mapNames f (BLt a1 a2)  = BLt (mapNames f a1) (mapNames f a2)
  mapNames f (BGt a1 a2)  = BGt (mapNames f a1) (mapNames f a2)

bexpToAssertion :: BExp -> Assertion
bexpToAssertion bexp = case bexp of
  BTrue      -> A.ATrue
  BFalse     -> A.AFalse
  BNot b     -> A.Not $ bexpToAssertion b
  BAnd b1 b2 -> A.And [bexpToAssertion b1, bexpToAssertion b2]
  BOr  b1 b2 -> A.Or  [bexpToAssertion b1, bexpToAssertion b2]
  BEq  a1 a2 -> A.Eq  (aexpToArith a1) (aexpToArith a2)
  BNe  a1 a2 -> A.Not $ A.Eq (aexpToArith a1) (aexpToArith a2)
  BLe  a1 a2 -> A.Lte (aexpToArith a1) (aexpToArith a2)
  BGe  a1 a2 -> A.Gte (aexpToArith a1) (aexpToArith a2)
  BGt  a1 a2 -> A.Gt  (aexpToArith a1) (aexpToArith a2)
  BLt  a1 a2 -> A.Lt  (aexpToArith a1) (aexpToArith a2)


-----------------
-- Interpreter --
-----------------

evalBExp :: State -> BExp -> Bool
evalBExp st bexp = case bexp of
  BTrue      -> True
  BFalse     -> False
  BNot b     -> not $ evalBExp st b
  BAnd b1 b2 -> (evalBExp st b1) && (evalBExp st b2)
  BOr  b1 b2 -> (evalBExp st b1) || (evalBExp st b2)
  BEq  b1 b2 -> (evalAExp st b1) == (evalAExp st b2)
  BNe  b1 b2 -> (evalAExp st b1) /= (evalAExp st b2)
  BLe  b1 b2 -> (evalAExp st b1) <= (evalAExp st b2)
  BGe  b1 b2 -> (evalAExp st b1) >= (evalAExp st b2)
  BGt  b1 b2 -> (evalAExp st b1) >  (evalAExp st b2)
  BLt  b1 b2 -> (evalAExp st b1) <  (evalAExp st b2)
