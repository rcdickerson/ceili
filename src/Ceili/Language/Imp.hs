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
  , PopulateTestStates(..)
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
                  , FreshableNames(..)
                  , MappableNames(..)
                  , Name(..)
                  , TypedName(..)
                  , Type(..)
                  , freshen )
import qualified Ceili.Name as Name
import Ceili.SMTString ( showSMT )
import Data.List ( partition )
import Data.Maybe ( catMaybes, fromMaybe )
import Data.Set ( Set )
import qualified Data.Set as Set
import qualified Data.Map as Map
import Prettyprinter


--------------
-- Language --
--------------

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

data ImpWhile e = ImpWhile BExp e ImpWhileMetadata
  deriving (Eq, Ord, Show, Functor)

type ImpProgram = ImpExpr ( ImpSkip
                        :+: ImpAsgn
                        :+: ImpSeq
                        :+: ImpIf
                        :+: ImpWhile )

-----------------------
-- ImpWhile Metadata --
-----------------------

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

instance FreshableNames ImpWhileMetadata where
  freshen (ImpWhileMetadata invar measure tests) = do
    invar'   <- freshen invar
    measure' <- freshen measure
    tests'   <- case tests of
                  Nothing -> return Nothing
                  Just s  -> do
                    let testList = Set.toList s
                    testList' <- freshen testList
                    return $ Just (Set.fromList testList')
    return $ ImpWhileMetadata invar' measure' tests'


------------------------
-- Smart Constructors --
------------------------

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


----------------------
-- CollectableNames --
----------------------

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


-------------------
-- MappableNames --
-------------------

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


--------------------
-- FreshableNames --
--------------------

instance FreshableNames (ImpSkip e) where
  freshen ImpSkip = return ImpSkip

instance FreshableNames (ImpAsgn e) where
  freshen (ImpAsgn var aexp) = do
    var'  <- freshen var
    aexp' <- freshen aexp
    return $ ImpAsgn var' aexp'

instance FreshableNames e => FreshableNames (ImpSeq e) where
  freshen (ImpSeq stmts) = return . ImpSeq =<< freshen stmts

instance FreshableNames e => FreshableNames (ImpIf e) where
  freshen (ImpIf c t e) = do
    c' <- freshen c
    t' <- freshen t
    e' <- freshen e
    return $ ImpIf c' t' e'

instance FreshableNames e => FreshableNames (ImpWhile e) where
  freshen (ImpWhile cond body meta) = do
    cond' <- freshen cond
    body' <- freshen body
    meta' <- freshen meta
    return $ ImpWhile cond' body' meta'

instance FreshableNames ImpProgram where
  freshen (In p) = return . In =<< freshen p


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
  evalImp _ st _ = return $ Just st

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

instance (FuelTank f, PopulateTestStates f e) => PopulateTestStates f (ImpWhile e) where
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

instance (FuelTank f) => PopulateTestStates f ImpProgram where
  populateTestStates fuel sts (In f) = populateTestStates fuel sts f >>= return . In


--------------------
-- Pretty Printer --
--------------------

instance Pretty (ImpSkip e) where
  pretty _ = pretty "skip"

instance Pretty (ImpAsgn e) where
  pretty (ImpAsgn lhs rhs) = pretty lhs <+> pretty ":=" <+> pretty rhs

instance Pretty e => Pretty (ImpSeq e) where
  pretty (ImpSeq stmts) = vsep $ map (\stmt -> pretty stmt <> semi) stmts

instance Pretty e => Pretty (ImpIf e) where
  pretty (ImpIf cond tBranch eBranch) =
    pretty "if" <> softline <> pretty cond
    <> line <> pretty "then"
    <> softline <> (indent 2 $ pretty tBranch)
    <> line <> pretty "else"
    <> softline <> (indent 2 $ pretty eBranch)
    <> line <> pretty "endif"

instance Pretty e => Pretty (ImpWhile e) where
  pretty (ImpWhile cond body _) =
    pretty "while" <> softline <> pretty cond
    <> line <> (indent 2 $ pretty body)
    <> line <> pretty "end"

instance Pretty ImpProgram where
  pretty (In p) = pretty p


--------------------------------------------
-- Backward Predicate Transform (Partial) --
--------------------------------------------

class ImpBackwardPT c e where
  impBackwardPT :: c -> e -> Assertion -> Ceili Assertion

instance ImpBackwardPT c (ImpSkip e) where
  impBackwardPT _ ImpSkip post = return post

instance ImpBackwardPT c (ImpAsgn e) where
  impBackwardPT _ (ImpAsgn lhs rhs) post =
    return $ A.subArith (TypedName lhs Name.Int)
                        (aexpToArith rhs)
                        post

instance ImpBackwardPT c e => ImpBackwardPT c (ImpSeq e) where
  impBackwardPT ctx (ImpSeq stmts) post =
    case stmts of
      [] -> return post
      (s:ss) -> do
        post' <- impBackwardPT ctx (ImpSeq ss) post
        impBackwardPT ctx s post'

instance ImpBackwardPT c e => ImpBackwardPT c (ImpIf e) where
  impBackwardPT ctx (ImpIf condB tBranch eBranch) post = do
    wpT <- impBackwardPT ctx tBranch post
    wpE <- impBackwardPT ctx eBranch post
    let cond   = bexpToAssertion condB
        ncond  = A.Not $ cond
    return $ A.And [A.Imp cond wpT, A.Imp ncond wpE]

instance (CollectableNames e, ImpBackwardPT c e) => ImpBackwardPT c (ImpWhile e) where
  impBackwardPT ctx (ImpWhile condB body meta) post = let
    cond          = bexpToAssertion condB
    varSet        = Set.unions [Name.namesIn condB, Name.namesIn body]
    vars          = Set.toList varSet
    freshMapping  = snd $ Name.buildFreshMap (Name.buildFreshIds vars) vars
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
                   mInferredInv <- Pie.loopInvGen impBackwardPT ctx cond body post tests
                   case mInferredInv of
                     Just inv -> return inv
                     Nothing  -> do
                       log_i "Unable to infer loop invariant, proceeding with False"
                       return A.AFalse
      bodyWP <- impBackwardPT ctx body inv
      let loopWP = A.Forall qNames
                   (freshen $ A.Imp (A.And [cond, inv]) bodyWP)
      let endWP  = A.Forall qNames
                    (freshen $ A.Imp (A.And [A.Not cond, inv]) post)
      return $ A.And [inv, loopWP, endWP]

instance (ImpBackwardPT c (f e), ImpBackwardPT c (g e)) =>
         ImpBackwardPT c ((f :+: g) e) where
  impBackwardPT ctx (Inl f) post = impBackwardPT ctx f post
  impBackwardPT ctx (Inr f) post = impBackwardPT ctx f post

instance ImpBackwardPT c ImpProgram where
  impBackwardPT ctx (In f) post = impBackwardPT ctx f post


-------------------------------------------
-- Forward Predicate Transform (Partial) --
-------------------------------------------

class ImpForwardPT c e where
  impForwardPT :: c -> e -> Assertion -> Ceili Assertion

instance ImpForwardPT c (ImpSkip e) where
  impForwardPT _ ImpSkip pre = return pre

instance ImpForwardPT c (ImpAsgn e) where
  impForwardPT _ (ImpAsgn lhs rhs) pre = do
    lhs' <- envFreshen lhs
    let
      subPre   = Name.substitute lhs lhs' pre
      rhsArith = aexpToArith rhs
      ilhs     = TypedName lhs  Name.Int
      ilhs'    = TypedName lhs' Name.Int
      subRhs   = A.subArith ilhs (A.Var ilhs') rhsArith
    return $ A.Exists [ilhs'] $ A.And [A.Eq (A.Var ilhs) subRhs, subPre]

instance ImpForwardPT c e => ImpForwardPT c (ImpSeq e) where
  impForwardPT ctx (ImpSeq stmts) pre = case stmts of
    []     -> return pre
    (s:ss) -> do
      pre' <- impForwardPT ctx s pre
      impForwardPT ctx (ImpSeq ss) pre'

instance ImpForwardPT c e => ImpForwardPT c (ImpIf e) where
  impForwardPT ctx (ImpIf b s1 s2) pre = do
    let cond = bexpToAssertion b
    postS1 <- impForwardPT ctx s1 (A.And [pre, cond])
    postS2 <- impForwardPT ctx s2 (A.And [pre, A.Not cond])
    return $ A.Or [postS1, postS2]

instance (CollectableNames e, ImpForwardPT c e) => ImpForwardPT c (ImpWhile e) where
  impForwardPT ctx (ImpWhile b body meta) pre = do
    let cond = bexpToAssertion b
    inv <- case (iwm_invariant meta) of
      Nothing  -> Houdini.infer (namesInToInt body) Set.empty 2 pre (impForwardPT ctx body) -- TODO: Lits
      Just inv -> return inv
    bodyInvSP <- impForwardPT ctx body inv
    log_d "Checking loop invariant verification conditions..."
    vcCheck <- checkValidB $ A.And [ A.Imp pre inv, A.Imp bodyInvSP inv ]
    if vcCheck
      then do log_d "Loop invariant verification conditions passed."
              return $ A.And [A.Not cond, inv]
      else throwError
           $ "Loop failed verification conditions. Invariant: " ++ showSMT inv

instance (ImpForwardPT c (f e), ImpForwardPT c (g e)) =>
         ImpForwardPT c ((f :+: g) e) where
  impForwardPT ctx (Inl f) pre = impForwardPT ctx f pre
  impForwardPT ctx (Inr f) pre = impForwardPT ctx f pre

instance ImpForwardPT c ImpProgram where
  impForwardPT ctx (In f) pre = impForwardPT ctx f pre


-------------
-- Utility --
-------------

namesInToInt :: CollectableNames c => c -> Set TypedName
namesInToInt c = let
   names = namesIn c
   in Set.map (\n -> TypedName n Int) names
