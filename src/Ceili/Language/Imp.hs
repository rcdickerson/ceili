{-# LANGUAGE DeriveFoldable #-}
{-# LANGUAGE ExistentialQuantification #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE StandaloneDeriving #-}

module Ceili.Language.Imp
  ( AExp(..)
  , BExp(..)
  , Invariant
  , Measure
  , Name(..)
  , ImpAsgn(..)
  , ImpIf(..)
  , ImpProgram
  , ImpSeq(..)
  , ImpSkip(..)
  , ImpWhile(..)
  , aexpToArith
  , bexpToAssertion
  , forwardPT
  , impAsgn
  , impIf
  , impSeq
  , impSkip
  , impWhile
  ) where

import Ceili.Assertion.AssertionLanguage ( Assertion)
import qualified Ceili.Assertion.AssertionLanguage as A
import qualified Ceili.CeiliEnv as Env
import qualified Ceili.InvariantInference.Houdini as Houdini
import Ceili.Name ( CollectableNames(..)
                  , MappableNames(..)
                  , Name(..)
                  , TypedName(..)
                  , Type(..) )
import qualified Ceili.Name as Name
import Ceili.PTS.ForwardPT ( ForwardPT(..) )
import Ceili.SMTString ( showSMT )
import Data.Set ( Set )
import qualified Data.Set  as Set
import Data.Typeable ( Typeable, cast )


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

type Invariant = Assertion
type Measure   = A.Arith

class ( CollectableNames p
      , MappableNames p
      , Eq p, Show p
      , Typeable p
      , ForwardPT p
      ) => ImpProgram_ p

data ImpProgram = forall p. ImpProgram_ p => ImpProgram p

instance Eq ImpProgram where
  (ImpProgram p1) == (ImpProgram p2) = Just p1 == cast p2
instance Show ImpProgram where
  show (ImpProgram p) = show p

pack :: ImpProgram_ p => p -> ImpProgram
pack = ImpProgram

data ImpSkip    = ImpSkip
data ImpAsgn    = ImpAsgn Name AExp
data ImpSeq p   = ImpSeq [p]
data ImpIf p    = ImpIf BExp p p
data ImpWhile p = ImpWhile BExp p (Maybe Invariant, Maybe Measure)

instance ImpProgram_ ImpSkip
instance ImpProgram_ ImpAsgn
instance ImpProgram_ (ImpSeq ImpProgram)
instance ImpProgram_ (ImpIf ImpProgram)
instance ImpProgram_ (ImpWhile ImpProgram)

instance Functor ImpSeq where
  fmap f (ImpSeq stmts) = ImpSeq $ map f stmts
deriving instance Foldable ImpSeq

impSkip :: ImpProgram
impSkip = pack ImpSkip

impAsgn :: Name -> AExp -> ImpProgram
impAsgn name aexp = pack $ ImpAsgn name aexp

impSeq :: [ImpProgram] -> ImpProgram
impSeq = pack . ImpSeq

impIf :: BExp -> ImpProgram -> ImpProgram -> ImpProgram
impIf bexp t e = pack $ ImpIf bexp t e

impWhile :: BExp -> ImpProgram -> (Maybe Invariant, Maybe Measure) -> ImpProgram
impWhile bexp body iv = pack $ ImpWhile bexp body iv

deriving instance Eq ImpSkip
deriving instance Eq ImpAsgn
deriving instance Eq p => Eq (ImpSeq p)
deriving instance Eq p => Eq (ImpIf p)
deriving instance Eq p => Eq (ImpWhile p)

deriving instance Show ImpSkip
deriving instance Show ImpAsgn
deriving instance Show p => Show (ImpSeq p)
deriving instance Show p => Show (ImpIf p)
deriving instance Show p => Show (ImpWhile p)

instance CollectableNames ImpProgram where
  namesIn (ImpProgram p) = namesIn p
instance CollectableNames ImpSkip where
  namesIn ImpSkip = Set.empty
instance CollectableNames ImpAsgn where
  namesIn (ImpAsgn var aexp) = Set.insert var $ namesIn aexp
instance {-# OVERLAPPING #-} CollectableNames p =>
  CollectableNames (ImpIf p) where
    namesIn (ImpIf cond bThen bElse) = Set.unions
      [ (namesIn cond), (namesIn bThen), (namesIn bElse)]
instance {-# OVERLAPPING #-} CollectableNames p =>
  CollectableNames (ImpWhile p) where
    namesIn (ImpWhile cond body _) = Set.union (namesIn cond) (namesIn body)
-- Note: Seq is a Foldable Functor, so gets this instance automatically.

instance MappableNames ImpProgram where
  mapNames f (ImpProgram p) = ImpProgram $ mapNames f p
instance MappableNames ImpSkip where
  mapNames _ ImpSkip = ImpSkip
instance MappableNames ImpAsgn where
  mapNames f (ImpAsgn var aexp) = ImpAsgn (f var) (mapNames f aexp)
instance {-# OVERLAPPING #-} MappableNames p =>
  MappableNames (ImpIf p) where
    mapNames f (ImpIf c t e) = ImpIf (mapNames f c) (mapNames f t) (mapNames f e)
instance {-# OVERLAPPING #-} MappableNames p =>
  MappableNames (ImpWhile p) where
    mapNames f (ImpWhile cond body (invar, meas)) =
      ImpWhile (mapNames f cond)
               (mapNames f body)
               (mapNames f invar, mapNames f meas)
-- Note: Seq is a Functor, so gets this instance automatically.

-- TODO: Instance overlap might make the Functor Collectable / Mappable
-- convenience instances not worthwhile. Maybe just remove them?

---------------------------------
-- Forward Predicate Transform --
---------------------------------

instance ForwardPT ImpProgram where
  forwardPT pre (ImpProgram p) = forwardPT pre p

instance ForwardPT ImpSkip where
  forwardPT pre ImpSkip = return pre

instance ForwardPT ImpAsgn where
  forwardPT pre (ImpAsgn lhs rhs) = let
    names     = Set.unions [ namesIn lhs, namesIn rhs, namesIn pre ]
    (lhs', _) = Name.nextFreshName lhs $ Name.buildNextFreshIds names
    subPre    = Name.substitute lhs lhs' pre
    rhsArith  = aexpToArith rhs
    ilhs      = TypedName lhs  Name.Int
    ilhs'     = TypedName lhs' Name.Int
    subRhs    = A.subArith ilhs (A.Var ilhs') rhsArith
    in return $ A.Exists [ilhs'] $ A.And [A.Eq (A.Var ilhs) subRhs, subPre]

instance ForwardPT (ImpSeq ImpProgram) where
  forwardPT pre (ImpSeq stmts) = case stmts of
    []     -> return pre
    (s:ss) -> do
      pre' <- forwardPT pre s
      forwardPT pre' (ImpSeq ss)

instance ForwardPT (ImpIf ImpProgram) where
  forwardPT pre (ImpIf b s1 s2) = do
    let cond = bexpToAssertion b
    postS1 <- forwardPT (A.And [pre, cond]) s1
    postS2 <- forwardPT (A.And [pre, A.Not cond]) s2
    return $ A.Or [postS1, postS2]

instance ForwardPT (ImpWhile ImpProgram) where
  forwardPT pre (ImpWhile b body (minv, _)) = do
    let cond = bexpToAssertion b
    let bodySP pre' = forwardPT pre' body
    inv <- case minv of
      Nothing  -> Houdini.infer (namesInToInt body) Set.empty 2 pre bodySP
      Just inv -> return inv
    bodyInvSP <- bodySP inv
    Env.log_d "Checking loop invariant verification conditions..."
    vcCheck <- Env.checkValid $ A.And [ A.Imp pre inv, A.Imp bodyInvSP inv ]
    if vcCheck
      then do Env.log_d "Loop invariant verification conditions passed."
              return $ A.And [A.Not cond, inv]
      else Env.throwError
           $ "Loop failed verification conditions. Invariant: " ++ showSMT inv

namesInToInt :: CollectableNames c => c -> Set TypedName
namesInToInt c = let
   names = namesIn c
   in Set.map (\n -> TypedName n Int) names
