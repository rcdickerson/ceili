module Ceili.Languages.Imp.ImpLanguage
    ( AExp(..)
    , BExp(..)
    , Name(..)
    , Program(..)
    , aexpToArith
    , bexpToAssertion
    ) where

import qualified Data.Set  as Set
import           Ceili.Assertion.AssertionLanguage  ( Assertion)
import qualified Ceili.Assertion.AssertionLanguage as A
import           Ceili.Name ( CollectableNames(..)
                            , MappableNames(..)
                            , Name(..)
                            , TypedName(..))
import qualified Ceili.Name as Name


----------------------------
-- Arithmetic Expressions --
----------------------------

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


----------------
-- Programs --
----------------

data Program
  = SSkip
  | SAsgn  Name AExp
  | SSeq   [Program]
  | SIf    BExp Program Program
  | SWhile BExp Program (Assertion, A.Arith)
  deriving (Eq, Ord, Show)

instance CollectableNames Program where
  namesIn prog = case prog of
    SSkip                   -> Set.empty
    SAsgn  var aexp         -> Set.insert var $ namesIn aexp
    SSeq   []               -> Set.empty
    SSeq   (s:ss)           -> Set.union (namesIn s) (namesIn $ SSeq ss)
    SIf    cond bThen bElse -> Set.unions [ (namesIn cond)
                                          , (namesIn bThen)
                                          , (namesIn bElse)]
    SWhile cond body _      -> Set.union (namesIn cond) (namesIn body)

instance MappableNames Program where
  mapNames f prog = case prog of
    SSkip        -> SSkip
    SAsgn v aexp -> SAsgn (f v) (mapNames f aexp)
    SSeq stmts   -> SSeq $ map (mapNames f) stmts
    SIf b t e    -> SIf (mapNames f b) (mapNames f t) (mapNames f e)
    SWhile cond body (inv, var)
                 -> SWhile (mapNames f cond) (mapNames f body) (inv, var)
