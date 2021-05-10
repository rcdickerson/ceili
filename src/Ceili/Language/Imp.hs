{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE TypeSynonymInstances #-}
{-# LANGUAGE UndecidableInstances #-}

module Ceili.Language.Imp
  ( AExp(..)
  , BExp(..)
  , ImpAsgn(..)
  , ImpExpr(..)
  , ImpIf(..)
  , ImpProgram
  , ImpSeq(..)
  , ImpSkip(..)
  , ImpWhile(..)
  , Invariant
  , Measure
  , MVarInvar
  , Name(..)
  , backwardPT
  , forwardPT
  , impAsgn
  , impIf
  , impSeq
  , impSeqIfNeeded
  , impSkip
  , impWhile
  , inject
  ) where

import Ceili.Assertion.AssertionLanguage ( Assertion)
import qualified Ceili.Assertion.AssertionLanguage as A
import qualified Ceili.CeiliEnv as Env
import qualified Ceili.InvariantInference.Houdini as Houdini
import Ceili.Language.AExp ( AExp(..), aexpToArith )
import Ceili.Language.BExp ( BExp(..), bexpToAssertion )
import Ceili.Language.Compose
import Ceili.Name ( CollectableNames(..)
                  , MappableNames(..)
                  , Name(..)
                  , TypedName(..)
                  , Type(..) )
import qualified Ceili.Name as Name
import Ceili.PTS.ForwardPT ( ForwardPT(..) )
import Ceili.PTS.BackwardPT ( BackwardPT(..) )
import Ceili.SMTString ( showSMT )
import Data.Set ( Set )
import qualified Data.Set as Set
import qualified Data.Map as Map


data ImpExpr f = In (f (ImpExpr f))

instance Eq (f (ImpExpr f)) => Eq (ImpExpr f) where
  (In f1) == (In f2) = f1 == f2

instance Show (f (ImpExpr f)) => Show (ImpExpr f) where
  show (In f) = show f

data ImpSkip e = ImpSkip
  deriving (Eq, Ord, Show, Functor)

data ImpAsgn e = ImpAsgn Name AExp
  deriving (Eq, Ord, Show, Functor)

data ImpSeq e = ImpSeq [e]
  deriving (Eq, Ord, Show, Functor)

data ImpIf e = ImpIf BExp e e
  deriving (Eq, Ord, Show, Functor)

data ImpWhile e = ImpWhile BExp e MVarInvar
  deriving (Eq, Ord, Show, Functor)

type Invariant = Assertion
type Measure   = A.Arith
type MVarInvar = (Maybe Invariant, Maybe Measure)

type ImpProgram = ImpExpr ( ImpSkip
                        :+: ImpAsgn
                        :+: ImpSeq
                        :+: ImpIf
                        :+: ImpWhile )

inject :: (g :<: f) => g (ImpExpr f) -> ImpExpr f
inject = In . inj

impSkip :: (ImpSkip :<: f) => ImpExpr f
impSkip = inject ImpSkip

impAsgn :: (ImpAsgn :<: f) => Name -> AExp -> ImpExpr f
impAsgn lhs rhs = inject $ ImpAsgn lhs rhs

impSeq :: (ImpSeq :<: f) => [ImpExpr f] -> ImpExpr f
impSeq stmts = inject $ ImpSeq stmts

impSeqIfNeeded :: (ImpSkip :<: f, ImpSeq :<: f) => [ImpExpr f] -> ImpExpr f
impSeqIfNeeded stmts = case stmts of
  []   -> impSkip
  s:[] -> s
  ss   -> impSeq ss

impIf :: (ImpIf :<: f) => BExp -> ImpExpr f -> ImpExpr f -> ImpExpr f
impIf cond tBranch eBranch = inject $ ImpIf cond tBranch eBranch

impWhile :: (ImpWhile :<: f) => BExp -> ImpExpr f -> MVarInvar -> ImpExpr f
impWhile cond body mVarInvar = inject $ ImpWhile cond body mVarInvar


instance CollectableNames (ImpSkip e) where
  namesIn ImpSkip = Set.empty
instance CollectableNames (ImpAsgn e) where
  namesIn (ImpAsgn var aexp) = Set.insert var $ namesIn aexp
instance CollectableNames e => CollectableNames (ImpSeq e) where
  namesIn (ImpSeq stmts) = namesIn stmts
instance CollectableNames e => CollectableNames (ImpIf e) where
  namesIn (ImpIf cond bThen bElse) = Set.unions
    [ (namesIn cond), (namesIn bThen), (namesIn bElse)]
instance CollectableNames e => CollectableNames (ImpWhile e) where
  namesIn (ImpWhile cond body _) = Set.union (namesIn cond) (namesIn body)
instance CollectableNames ImpProgram
  where namesIn (In p) = namesIn p

instance MappableNames (ImpSkip e) where
  mapNames _ ImpSkip = ImpSkip
instance MappableNames (ImpAsgn e) where
  mapNames f (ImpAsgn var aexp) = ImpAsgn (f var) (mapNames f aexp)
instance MappableNames e => MappableNames (ImpSeq e) where
  mapNames f (ImpSeq stmts) = ImpSeq $ mapNames f stmts
instance MappableNames e => MappableNames (ImpIf e) where
  mapNames f (ImpIf c t e) = ImpIf (mapNames f c) (mapNames f t) (mapNames f e)
instance MappableNames e => MappableNames (ImpWhile  e) where
    mapNames f (ImpWhile cond body (invar, meas)) =
      ImpWhile (mapNames f cond)
                (mapNames f body)
                (mapNames f invar, mapNames f meas)
instance MappableNames ImpProgram
  where mapNames f (In p) = In $ mapNames f p


-------------------------------------------
-- Forward Predicate Transform (Partial) --
-------------------------------------------

instance ForwardPT (ImpSkip e) where
  forwardPT pre ImpSkip = return pre

instance ForwardPT (ImpAsgn e) where
  forwardPT pre (ImpAsgn lhs rhs) = let
    names     = Set.unions [ namesIn lhs, namesIn rhs, namesIn pre ]
    (lhs', _) = Name.nextFreshName lhs $ Name.buildNextFreshIds names
    subPre    = Name.substitute lhs lhs' pre
    rhsArith  = aexpToArith rhs
    ilhs      = TypedName lhs  Name.Int
    ilhs'     = TypedName lhs' Name.Int
    subRhs    = A.subArith ilhs (A.Var ilhs') rhsArith
    in return $ A.Exists [ilhs'] $ A.And [A.Eq (A.Var ilhs) subRhs, subPre]

instance ForwardPT e => ForwardPT (ImpSeq e) where
  forwardPT pre (ImpSeq stmts) = case stmts of
    []     -> return pre
    (s:ss) -> do
      pre' <- forwardPT pre s
      forwardPT pre' (ImpSeq ss)

instance ForwardPT e => ForwardPT (ImpIf e) where
  forwardPT pre (ImpIf b s1 s2) = do
    let cond = bexpToAssertion b
    postS1 <- forwardPT (A.And [pre, cond]) s1
    postS2 <- forwardPT (A.And [pre, A.Not cond]) s2
    return $ A.Or [postS1, postS2]

instance (CollectableNames e, ForwardPT e) => ForwardPT (ImpWhile e) where
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

instance ForwardPT ImpProgram where
  forwardPT pre (In f) = forwardPT pre f


--------------------------------------------
-- Backward Predicate Transform (Partial) --
--------------------------------------------

instance BackwardPT (ImpSkip e) where
  backwardPT post ImpSkip = return post

instance BackwardPT (ImpAsgn e) where
  backwardPT post (ImpAsgn lhs rhs) =
    return $ A.subArith (TypedName lhs Name.Int)
                        (aexpToArith rhs)
                        post

instance BackwardPT e => BackwardPT (ImpSeq e) where
  backwardPT post (ImpSeq stmts) = case stmts of
    [] -> return post
    (s:ss) -> do
      post' <- backwardPT post (ImpSeq ss)
      backwardPT post' s

instance BackwardPT e => BackwardPT (ImpIf e) where
  backwardPT post (ImpIf condB tBranch eBranch) = do
    wpT <- backwardPT post tBranch
    wpE <- backwardPT post eBranch
    let cond   = bexpToAssertion condB
        ncond  = A.Not $ cond
    return $ A.And [A.Imp cond wpT, A.Imp ncond wpE]

instance (CollectableNames e, BackwardPT e) => BackwardPT (ImpWhile e) where
  backwardPT post (ImpWhile condB body (minv, _)) = let
    cond          = bexpToAssertion condB
    varSet        = Set.unions [Name.namesIn condB, Name.namesIn body]
    vars          = Set.toList varSet
    freshMapping  = fst $ Name.freshNames vars $ Name.buildNextFreshIds vars
    (orig, fresh) = unzip $ Map.toList freshMapping
    freshen       = Name.substituteAll orig fresh
    qNames        = Set.toList $ namesInToInt fresh
    inv           = case minv of
                      Just i  -> i
                      Nothing -> error "Backward invariant inference unsupported"
    in do
      bodyWP <- backwardPT inv body
      let loopWP = A.Forall qNames
                   (freshen $ A.Imp (A.And [cond, inv]) bodyWP)
      let endWP  = A.Forall qNames
                   (freshen $ A.Imp (A.And [A.Not cond, inv]) post)
      return $ A.And [inv, loopWP, endWP]

instance BackwardPT ImpProgram where
  backwardPT post (In f) = backwardPT post f


-------------
-- Utility --
-------------

namesInToInt :: CollectableNames c => c -> Set TypedName
namesInToInt c = let
   names = namesIn c
   in Set.map (\n -> TypedName n Int) names
