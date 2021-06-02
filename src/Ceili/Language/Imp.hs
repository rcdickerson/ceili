{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE TypeSynonymInstances #-}
{-# LANGUAGE UndecidableInstances #-}

module Ceili.Language.Imp
  ( AExp(..)
  , BExp(..)
  , EvalImp(..)
  , Fuel(..)
  , ImpAsgn(..)
  , ImpBackwardPT(..)
  , ImpExpr(..)
  , ImpForwardPT(..)
  , ImpIf(..)
  , ImpProgram
  , ImpSeq(..)
  , ImpSkip(..)
  , ImpWhile(..)
  , ImpWhileMetadata(..)
  , Invariant
  , Measure
  , Name(..)
  , State
  , emptyWhileMetadata
  , impAsgn
  , impIf
  , impSeq
  , impSeqIfNeeded
  , impSkip
  , impWhile
  , impWhileWithMeta
  , inject
  , populateTestStates
  ) where

import Ceili.Assertion.AssertionLanguage ( Assertion)
import qualified Ceili.Assertion.AssertionLanguage as A
import Ceili.CeiliEnv
import qualified Ceili.InvariantInference.Houdini as Houdini
import qualified Ceili.InvariantInference.Pie as Pie
import Ceili.Language.AExp ( AExp(..), State, aexpToArith, evalAExp )
import Ceili.Language.BExp ( BExp(..), bexpToAssertion, evalBExp )
import Ceili.Language.Compose
import Ceili.Name ( CollectableNames(..)
                  , MappableNames(..)
                  , Name(..)
                  , TypedName(..)
                  , Type(..) )
import qualified Ceili.Name as Name
import Ceili.SMTString ( showSMT )
import Data.List ( partition )
import Data.Maybe ( catMaybes, fromMaybe )
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

type Invariant = Assertion
type Measure   = A.Arith
data ImpWhileMetadata =
  ImpWhileMetadata { iwm_invariant  :: Maybe Invariant
                   , iwm_measure    :: Maybe Measure
                   , iwm_testStates :: Maybe (Set Assertion)
                   } deriving (Eq, Ord, Show)

emptyWhileMetadata :: ImpWhileMetadata
emptyWhileMetadata = ImpWhileMetadata Nothing Nothing Nothing

instance MappableNames ImpWhileMetadata where
  mapNames f (ImpWhileMetadata mInvar mMeasure mTests) =
    let
      mInvar'   = do invar   <- mInvar;   return $ mapNames f invar
      mMeasure' = do measure <- mMeasure; return $ mapNames f measure
      mTests'   = do tests   <- mTests;   return $ mapNames f tests
    in ImpWhileMetadata mInvar' mMeasure' mTests'

data ImpWhile e = ImpWhile BExp e ImpWhileMetadata
  deriving (Eq, Ord, Show, Functor)

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

impWhile :: (ImpWhile :<: f) => BExp -> ImpExpr f -> ImpExpr f
impWhile cond body = inject $ ImpWhile cond body emptyWhileMetadata

impWhileWithMeta :: (ImpWhile :<: f) => BExp -> ImpExpr f -> ImpWhileMetadata -> ImpExpr f
impWhileWithMeta cond body meta = inject $ ImpWhile cond body meta


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

instance MappableNames e => MappableNames (ImpWhile e) where
    mapNames f (ImpWhile cond body meta) =
      ImpWhile (mapNames f cond) (mapNames f body) (mapNames f meta)

instance MappableNames ImpProgram
  where mapNames f (In p) = In $ mapNames f p


-----------------
-- Interpreter --
-----------------

data Fuel = Fuel Int
          | InfiniteFuel

class EvalImp f where
  evalImp :: State -> Fuel -> f -> Maybe State

instance (EvalImp (f e), EvalImp (g e)) => EvalImp ((f :+: g) e) where
  evalImp st fuel (Inl f) = evalImp st fuel f
  evalImp st fuel (Inr g) = evalImp st fuel g

instance EvalImp (ImpSkip e) where
  evalImp st _ _ = Just st

instance EvalImp (ImpAsgn e) where
  evalImp st _ (ImpAsgn var aexp) = Just $ Map.insert var (evalAExp st aexp) st

instance EvalImp e => EvalImp (ImpSeq e) where
  evalImp st fuel (ImpSeq stmts) = case stmts of
    [] -> Just st
    (stmt:rest) -> do
      st' <- evalImp st fuel stmt
      evalImp st' fuel (ImpSeq rest)

instance EvalImp e => EvalImp (ImpIf e) where
  evalImp st fuel (ImpIf c t f) = if (evalBExp st c)
                                  then (evalImp st fuel t)
                                  else (evalImp st fuel f)

instance EvalImp e => EvalImp (ImpWhile e) where
  evalImp st fuel (ImpWhile cond body meta) =
    case (evalBExp st cond) of
      False -> Just st
      True  -> case fuel of
        InfiniteFuel   -> step InfiniteFuel
        Fuel n | n > 0 -> step $ Fuel (n - 1)
        _              -> Nothing
    where
      step fuel' = do
        st' <- evalImp st fuel' body
        evalImp st' fuel' (ImpWhile cond body meta)

instance EvalImp ImpProgram where
  evalImp st fuel (In program) = evalImp st fuel program


-----------------
-- Test States --
-----------------

class EvalImp f => PopulateTestStates f where
  populateTestStates :: [State] -> Fuel -> f -> f

instance PopulateTestStates (ImpSkip e) where
  populateTestStates _ _ skip = skip

instance PopulateTestStates (ImpAsgn e) where
  populateTestStates _ _ asgn = asgn

instance PopulateTestStates e => PopulateTestStates (ImpSeq e) where
  populateTestStates sts fuel (ImpSeq stmts) =
    case stmts of
      [] -> ImpSeq stmts
      stmt:rest ->
        let
          stmt' = populateTestStates sts fuel stmt
          sts' = catMaybes $ map (\st -> evalImp st fuel stmt) sts
          ImpSeq rest' = populateTestStates sts' fuel (ImpSeq rest)
        in ImpSeq $ stmt':rest'

instance PopulateTestStates e => PopulateTestStates (ImpIf e) where
  populateTestStates sts fuel (ImpIf c t f) =
    let (tStates, fStates) = partition (\st -> evalBExp st c) sts
    in ImpIf c (populateTestStates tStates fuel t)
               (populateTestStates fStates fuel f)

instance PopulateTestStates e => PopulateTestStates (ImpWhile e) where
  populateTestStates sts fuel (ImpWhile cond body meta) =
    let
      ImpWhileMetadata inv meas tests = meta
      (trueSts, _) = partition (\st -> evalBExp st cond) sts
      body'        = populateTestStates trueSts fuel body
      -- Convert states to assertions.
      toEq (k, v)  = A.Eq (A.Var $ TypedName k Int) (A.Num v)
      toAssert st  = A.And $ map toEq (Map.toList st)
      newTests     = Set.fromList $ map toAssert sts
      tests'       = Just $ Set.union newTests (fromMaybe Set.empty tests)
    in ImpWhile cond body' $ ImpWhileMetadata inv meas tests'

instance (PopulateTestStates (f e), PopulateTestStates (g e)) =>
         PopulateTestStates ((f :+: g) e) where
  populateTestStates st fuel (Inl f) = Inl $ populateTestStates st fuel f
  populateTestStates st fuel (Inr f) = Inr $ populateTestStates st fuel f

instance PopulateTestStates ImpProgram where
  populateTestStates sts fuel (In f) = In $ populateTestStates sts fuel f


--------------------------------------------
-- Backward Predicate Transform (Partial) --
--------------------------------------------

class ImpBackwardPT e where
  impBackwardPT :: e -> Assertion -> Ceili Assertion

instance ImpBackwardPT (ImpSkip e) where
  impBackwardPT ImpSkip post = return post

instance ImpBackwardPT (ImpAsgn e) where
  impBackwardPT (ImpAsgn lhs rhs) post =
    return $ A.subArith (TypedName lhs Name.Int)
                        (aexpToArith rhs)
                        post

instance ImpBackwardPT e => ImpBackwardPT (ImpSeq e) where
  impBackwardPT (ImpSeq stmts) post =
    case stmts of
      [] -> return post
      (s:ss) -> do
        post' <- impBackwardPT (ImpSeq ss) post
        impBackwardPT s post'

instance ImpBackwardPT e => ImpBackwardPT (ImpIf e) where
  impBackwardPT (ImpIf condB tBranch eBranch) post = do
    wpT <- impBackwardPT tBranch post
    wpE <- impBackwardPT eBranch post
    let cond   = bexpToAssertion condB
        ncond  = A.Not $ cond
    return $ A.And [A.Imp cond wpT, A.Imp ncond wpE]

instance (CollectableNames e, ImpBackwardPT e, ImpForwardPT e) => ImpBackwardPT (ImpWhile e) where
  impBackwardPT (ImpWhile condB body meta) post = let
    cond          = bexpToAssertion condB
    varSet        = Set.unions [Name.namesIn condB, Name.namesIn body]
    vars          = Set.toList varSet
    freshMapping  = fst $ Name.freshNames vars $ Name.buildNextFreshIds vars
    (orig, fresh) = unzip $ Map.toList freshMapping
    freshen       = Name.substituteAll orig fresh
    qNames        = Set.toList $ namesInToInt fresh
    in do
      inv <- case (iwm_invariant meta) of
               Just i  -> return i
               Nothing -> case (iwm_testStates meta) of
                 Nothing -> throwError
                   "No test states for while loop, did you run populateTestStates?"
                 Just testStates -> do
                   let tests = Set.toList testStates
                   mInferredInv <- Pie.loopInvGen impBackwardPT impForwardPT cond body post tests
                   case mInferredInv of
                     Just inv -> return inv
                     Nothing  -> throwError "Unable to infer loop invariant."
      bodyWP <- impBackwardPT body inv
      let loopWP = A.Forall qNames
                   (freshen $ A.Imp (A.And [cond, inv]) bodyWP)
      let endWP  = A.Forall qNames
                    (freshen $ A.Imp (A.And [A.Not cond, inv]) post)
      return $ A.And [inv, loopWP, endWP]

instance (ImpBackwardPT (f e), ImpBackwardPT (g e)) =>
         ImpBackwardPT ((f :+: g) e) where
  impBackwardPT (Inl f) post = impBackwardPT f post
  impBackwardPT (Inr f) post = impBackwardPT f post

instance ImpBackwardPT ImpProgram where
  impBackwardPT (In f) post = impBackwardPT f post


-------------------------------------------
-- Forward Predicate Transform (Partial) --
-------------------------------------------

class ImpForwardPT e where
  impForwardPT :: e -> Assertion -> Ceili Assertion

instance ImpForwardPT (ImpSkip e) where
  impForwardPT ImpSkip pre = return pre

instance ImpForwardPT (ImpAsgn e) where
  impForwardPT (ImpAsgn lhs rhs) pre = let
    names     = Set.unions [ namesIn lhs, namesIn rhs, namesIn pre ]
    (lhs', _) = Name.nextFreshName lhs $ Name.buildNextFreshIds names
    subPre    = Name.substitute lhs lhs' pre
    rhsArith  = aexpToArith rhs
    ilhs      = TypedName lhs  Name.Int
    ilhs'     = TypedName lhs' Name.Int
    subRhs    = A.subArith ilhs (A.Var ilhs') rhsArith
    in return $ A.Exists [ilhs'] $ A.And [A.Eq (A.Var ilhs) subRhs, subPre]

instance ImpForwardPT e => ImpForwardPT (ImpSeq e) where
  impForwardPT (ImpSeq stmts) pre = case stmts of
    []     -> return pre
    (s:ss) -> do
      pre' <- impForwardPT s pre
      impForwardPT (ImpSeq ss) pre'

instance ImpForwardPT e => ImpForwardPT (ImpIf e) where
  impForwardPT (ImpIf b s1 s2) pre = do
    let cond = bexpToAssertion b
    postS1 <- impForwardPT s1 (A.And [pre, cond])
    postS2 <- impForwardPT s2 (A.And [pre, A.Not cond])
    return $ A.Or [postS1, postS2]

instance (CollectableNames e, ImpForwardPT e) => ImpForwardPT (ImpWhile e) where
  impForwardPT (ImpWhile b body meta) pre = do
    let cond = bexpToAssertion b
    inv <- case (iwm_invariant meta) of
      Nothing  -> Houdini.infer (namesInToInt body) Set.empty 2 pre (impForwardPT body) -- TODO: Lits
      Just inv -> return inv
    bodyInvSP <- impForwardPT body inv
    log_d "Checking loop invariant verification conditions..."
    vcCheck <- checkValid $ A.And [ A.Imp pre inv, A.Imp bodyInvSP inv ]
    if vcCheck
      then do log_d "Loop invariant verification conditions passed."
              return $ A.And [A.Not cond, inv]
      else throwError
           $ "Loop failed verification conditions. Invariant: " ++ showSMT inv

instance (ImpForwardPT (f e), ImpForwardPT (g e)) =>
         ImpForwardPT ((f :+: g) e) where
  impForwardPT (Inl f) pre = impForwardPT f pre
  impForwardPT (Inr f) pre = impForwardPT f pre

instance ImpForwardPT ImpProgram where
  impForwardPT (In f) pre = impForwardPT f pre


-------------
-- Utility --
-------------

namesInToInt :: CollectableNames c => c -> Set TypedName
namesInToInt c = let
   names = namesIn c
   in Set.map (\n -> TypedName n Int) names
