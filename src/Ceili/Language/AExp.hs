module Ceili.Language.AExp
  ( AExp(..)
  , State
  , aexpToArith
  , evalAExp
  ) where

import qualified Ceili.Assertion.AssertionLanguage as A
import Ceili.Name ( CollectableNames(..)
                  , MappableNames(..)
                  , Name(..)
                  , TypedName(..) )
import qualified Ceili.Name as Name
import Data.Map ( Map )
import qualified Data.Map as Map
import qualified Data.Set as Set

data AExp
  = ALit Integer
  | AVar Name
  | AAdd AExp AExp
  | ASub AExp AExp
  | AMul AExp AExp
  | ADiv AExp AExp
  | AMod AExp AExp
  | APow AExp AExp
  deriving (Eq, Ord, Show)

instance CollectableNames AExp where
  namesIn aexp = case aexp of
    ALit _ -> Set.empty
    AVar v -> Set.singleton v
    AAdd lhs rhs -> Set.union (namesIn lhs) (namesIn rhs)
    ASub lhs rhs -> Set.union (namesIn lhs) (namesIn rhs)
    AMul lhs rhs -> Set.union (namesIn lhs) (namesIn rhs)
    ADiv lhs rhs -> Set.union (namesIn lhs) (namesIn rhs)
    AMod lhs rhs -> Set.union (namesIn lhs) (namesIn rhs)
    APow lhs rhs -> Set.union (namesIn lhs) (namesIn rhs)

instance MappableNames AExp where
  mapNames _ (ALit i)       = ALit i
  mapNames f (AVar v)       = AVar (f v)
  mapNames f (AAdd lhs rhs) = AAdd (mapNames f lhs) (mapNames f rhs)
  mapNames f (ASub lhs rhs) = ASub (mapNames f lhs) (mapNames f rhs)
  mapNames f (AMul lhs rhs) = AMul (mapNames f lhs) (mapNames f rhs)
  mapNames f (ADiv lhs rhs) = ADiv (mapNames f lhs) (mapNames f rhs)
  mapNames f (AMod lhs rhs) = AMod (mapNames f lhs) (mapNames f rhs)
  mapNames f (APow lhs rhs) = APow (mapNames f lhs) (mapNames f rhs)

aexpToArith :: AExp -> A.Arith
aexpToArith aexp = case aexp of
  ALit i           -> A.Num i
  AVar var         -> A.Var (TypedName var Name.Int)
  AAdd aexp1 aexp2 -> A.Add [aexpToArith aexp1, aexpToArith aexp2]
  ASub aexp1 aexp2 -> A.Sub [aexpToArith aexp1, aexpToArith aexp2]
  AMul aexp1 aexp2 -> A.Mul [aexpToArith aexp1, aexpToArith aexp2]
  ADiv aexp1 aexp2 -> let
    dividend = aexpToArith aexp1
    divisor  = aexpToArith aexp2
    in A.Div dividend divisor
  AMod aexp1 aexp2 -> let
    dividend = aexpToArith aexp1
    divisor  = aexpToArith aexp2
    in A.Mod dividend divisor
  APow aexp1 aexp2 -> let
    base  = aexpToArith aexp1
    power = aexpToArith aexp2
    in A.Pow base power


-----------------
-- Interpreter --
-----------------

type State = Map Name Integer

evalAExp :: State -> AExp -> Integer
evalAExp st aexp = case aexp of
  ALit i       -> i
  AVar v       -> Map.findWithDefault 0 v st
  AAdd lhs rhs -> (evalAExp st lhs) + (evalAExp st rhs)
  ASub lhs rhs -> (evalAExp st lhs) - (evalAExp st rhs)
  AMul lhs rhs -> (evalAExp st lhs) * (evalAExp st rhs)
  ADiv lhs rhs -> (evalAExp st lhs) `quot` (evalAExp st rhs)
  AMod lhs rhs -> (evalAExp st lhs) `mod` (evalAExp st rhs)
  APow lhs rhs -> (evalAExp st lhs) ^ (evalAExp st rhs)
