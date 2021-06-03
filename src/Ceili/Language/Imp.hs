{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE TypeSynonymInstances #-}
{-# LANGUAGE UndecidableInstances #-}

module Ceili.Language.Imp
  ( AExp(..)
  , BExp(..)
  , EvalImp(..)
  , Fuel(..)
  , FuelTank(..)
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

class FuelTank t where
  getFuel :: t -> Fuel
  setFuel :: t -> Fuel -> t

instance FuelTank Fuel where
  getFuel   = id
  setFuel _ = id

decrementFuel :: (FuelTank f) => f -> f
decrementFuel fuel =
  case getFuel fuel of
    Fuel n | n > 0 -> setFuel fuel $ Fuel (n - 1)
    _ -> fuel

class EvalImp c f where
  evalImp :: c -> State -> f -> Ceili (Maybe State)

instance (EvalImp c (f e), EvalImp c (g e)) => EvalImp c ((f :+: g) e) where
  evalImp c st (Inl f) = evalImp c st f
  evalImp c st (Inr g) = evalImp c st g

instance EvalImp c (ImpSkip e) where
  evalImp c st _ = return $ Just st

instance EvalImp c (ImpAsgn e) where
  evalImp _ st (ImpAsgn var aexp) = return $ Just $ Map.insert var (evalAExp st aexp) st

instance EvalImp c e => EvalImp c (ImpSeq e) where
  evalImp ctx st (ImpSeq stmts) =
    case stmts of
      [] -> return $ Just st
      (stmt:rest) -> do
        mSt' <- evalImp ctx st stmt
        case mSt' of
          Nothing  -> return Nothing
          Just st' -> evalImp ctx st' (ImpSeq rest)

instance EvalImp c e => EvalImp c (ImpIf e) where
  evalImp ctx st (ImpIf c t f) = if (evalBExp st c)
                                 then (evalImp ctx st t)
                                 else (evalImp ctx st f)

instance (FuelTank f, EvalImp f e) => EvalImp f (ImpWhile e) where
  evalImp fuel st (ImpWhile cond body meta) =
    case (evalBExp st cond) of
      False -> return $ Just st
      True  ->
        let fuel' = decrementFuel fuel
        in case (getFuel fuel') of
          Fuel n | n <= 0 -> do log_e "Evaluation ran out of fuel"
                                return Nothing
          _ -> do
            mSt' <- evalImp fuel' st body
            case mSt' of
              Nothing  -> return Nothing
              Just st' -> evalImp fuel' st' (ImpWhile cond body meta)

instance (FuelTank f) => EvalImp f ImpProgram where
  evalImp st fuel (In program) = evalImp st fuel program


-----------------
-- Test States --
-----------------

class EvalImp c f => PopulateTestStates c f where
  populateTestStates :: c -> [State] -> f -> Ceili f

instance PopulateTestStates c (ImpSkip e) where
  populateTestStates _ _ skip = return skip

instance PopulateTestStates c (ImpAsgn e) where
  populateTestStates _ _ asgn = return asgn

instance PopulateTestStates c e => PopulateTestStates c (ImpSeq e) where
  populateTestStates ctx sts (ImpSeq stmts) =
    case stmts of
      [] -> return $ ImpSeq stmts
      stmt:rest -> do
        stmt' <- populateTestStates ctx sts stmt
        mSts' <- sequence $ map (\st -> evalImp ctx st stmt) sts
        let sts' = catMaybes mSts'
        ImpSeq rest' <- populateTestStates ctx sts' (ImpSeq rest)
        return $ ImpSeq $ stmt':rest'

instance PopulateTestStates c e => PopulateTestStates c (ImpIf e) where
  populateTestStates ctx sts (ImpIf c t f) =
    let (tStates, fStates) = partition (\st -> evalBExp st c) sts
    in do
      t' <- populateTestStates ctx tStates t
      f' <- populateTestStates ctx fStates f
      return $ ImpIf c t' f'

instance PopulateTestStates Fuel e => PopulateTestStates Fuel (ImpWhile e) where
  populateTestStates fuel sts (ImpWhile cond body meta) = do
    let ImpWhileMetadata inv meas tests = meta
    let (trueSts, _) = partition (\st -> evalBExp st cond) sts
    body' <- populateTestStates fuel trueSts body
    -- Convert states to assertions.
    let
      toEq (k, v)  = A.Eq (A.Var $ TypedName k Int) (A.Num v)
      toAssert st  = A.And $ map toEq (Map.toList st)
      newTests     = Set.fromList $ map toAssert sts
      tests'       = Just $ Set.union newTests (fromMaybe Set.empty tests)
    return $ ImpWhile cond body' $ ImpWhileMetadata inv meas tests'

instance (PopulateTestStates c (f e), PopulateTestStates c (g e)) =>
         PopulateTestStates c ((f :+: g) e) where
  populateTestStates ctx st (Inl f) = populateTestStates ctx st f >>= return . Inl
  populateTestStates ctx st (Inr f) = populateTestStates ctx st f >>= return . Inr

instance PopulateTestStates Fuel ImpProgram where
  populateTestStates fuel sts (In f) = populateTestStates fuel sts f >>= return . In


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
