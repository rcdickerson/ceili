{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE MonoLocalBinds #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE UndecidableInstances #-}

module Ceili.Language.Imp
  ( AExp(..)
  , BExp(..)
  , CollectLoopHeadStates(..)
  , Fuel(..)
  , FuelTank(..)
  , ImpAsgn(..)
  , ImpBackwardPT(..)
  , ImpExpr(..)
  , ImpForwardPT(..)
  , ImpIf(..)
  , ImpPieContext(..)
  , ImpProgram
  , ImpSeq(..)
  , ImpSkip(..)
  , ImpWhile(..)
  , ImpWhileMetadata(..)
  , IterStateMap
  , LoopHeadStates
  , Name(..)
  , ProgState
  , emptyWhileMetadata
  , impAsgn
  , impIf
  , impSeq
  , impSeqIfNeeded
  , impSkip
  , impWhile
  , impWhileWithMeta
  , inject
  , unionIterStates
  ) where

import Ceili.Assertion.AssertionLanguage ( Assertion)
import Ceili.Assertion.AssertionParser ( AssertionParseable )
import qualified Ceili.Assertion.AssertionLanguage as A
import Ceili.CeiliEnv
import Ceili.Evaluation
import qualified Ceili.InvariantInference.Houdini as Houdini
import qualified Ceili.InvariantInference.Pie as Pie
import Ceili.Language.AExp
import Ceili.Language.BExp
import Ceili.Language.Compose
import Ceili.Literal
import Ceili.Name
import Ceili.ProgState
import Ceili.SMTString
import Ceili.StatePredicate
import Data.List ( partition )
import Data.UUID
import qualified Data.UUID.V4 as UUID
import Data.Map ( Map )
import qualified Data.Map as Map
import Data.Maybe ( catMaybes )
import Data.Set ( Set )
import qualified Data.Set as Set
import Prettyprinter


--------------
-- Language --
--------------

data ImpExpr t f = In (f (ImpExpr t f))

instance Eq (f (ImpExpr t f)) => Eq (ImpExpr t f) where
  (In f1) == (In f2) = f1 == f2

instance Show (f (ImpExpr t f)) => Show (ImpExpr t f) where
  show (In f) = show f

data ImpSkip t e = ImpSkip
  deriving (Eq, Ord, Show, Functor)

data ImpAsgn t e = ImpAsgn Name (AExp t)
  deriving (Eq, Ord, Show, Functor)

data ImpSeq t e = ImpSeq [e]
  deriving (Eq, Ord, Show, Functor)

data ImpIf t e = ImpIf (BExp t) e e
  deriving (Eq, Ord, Show, Functor)

data ImpWhile t e = ImpWhile (BExp t) e (ImpWhileMetadata t)
  deriving (Eq, Ord, Show, Functor)

type ImpProgram t = ImpExpr t ( ImpSkip t
                            :+: ImpAsgn t
                            :+: ImpSeq t
                            :+: ImpIf t
                            :+: ImpWhile t )

-----------------------
-- ImpWhile Metadata --
-----------------------

data ImpWhileMetadata t =
  ImpWhileMetadata { iwm_id        :: Maybe UUID
                   , iwm_invariant :: Maybe (Assertion t)
                   , iwm_measure   :: Maybe (A.Arith t)
                   } deriving (Eq, Ord, Show)

emptyWhileMetadata :: ImpWhileMetadata t
emptyWhileMetadata = ImpWhileMetadata Nothing Nothing Nothing

instance MappableNames (ImpWhileMetadata t) where
  mapNames f (ImpWhileMetadata loopId mInvar mMeasure) =
    let
      mInvar'   = do invar   <- mInvar;   return $ mapNames f invar
      mMeasure' = do measure <- mMeasure; return $ mapNames f measure
    in ImpWhileMetadata loopId mInvar' mMeasure'

instance FreshableNames (ImpWhileMetadata t) where
  freshen (ImpWhileMetadata loopId invar measure) = do
    invar'   <- freshen invar
    measure' <- freshen measure
    return $ ImpWhileMetadata loopId invar' measure'


------------------------
-- Smart Constructors --
------------------------

inject :: (g t :<: f) => g t (ImpExpr t f) -> ImpExpr t f
inject = In . inj

impSkip :: (ImpSkip t :<: f) => ImpExpr t f
impSkip = inject ImpSkip

impAsgn :: (ImpAsgn t :<: f) => Name -> AExp t -> ImpExpr t f
impAsgn lhs rhs = inject $ ImpAsgn lhs rhs

impSeq :: (ImpSeq t :<: f) => [ImpExpr t f] -> ImpExpr t f
impSeq stmts = inject $ ImpSeq stmts

impSeqIfNeeded :: (ImpSkip t :<: f, ImpSeq t :<: f) => [ImpExpr t f] -> ImpExpr t f
impSeqIfNeeded stmts = case stmts of
  []   -> impSkip
  s:[] -> s
  ss   -> impSeq ss

impIf :: (ImpIf t :<: f) => BExp t -> ImpExpr t f -> ImpExpr t f -> ImpExpr t f
impIf cond tBranch eBranch = inject $ ImpIf cond tBranch eBranch

impWhile :: (ImpWhile t :<: f) => BExp t -> ImpExpr t f -> ImpExpr t f
impWhile cond body = inject $ ImpWhile cond body emptyWhileMetadata

impWhileWithMeta :: (ImpWhile t :<: f) => BExp t -> ImpExpr t f -> ImpWhileMetadata t -> ImpExpr t f
impWhileWithMeta cond body meta = inject $ ImpWhile cond body meta


----------------------
-- CollectableNames --
----------------------

instance CollectableNames (ImpSkip t e) where
  namesIn ImpSkip = Set.empty

instance CollectableNames (ImpAsgn t e) where
  namesIn (ImpAsgn var aexp) = Set.insert var $ namesIn aexp

instance CollectableNames e => CollectableNames (ImpSeq t e) where
  namesIn (ImpSeq stmts) = namesIn stmts

instance CollectableNames e => CollectableNames (ImpIf t e) where
  namesIn (ImpIf cond bThen bElse) = Set.unions
    [namesIn cond, namesIn bThen, namesIn bElse]

instance CollectableNames e => CollectableNames (ImpWhile t e) where
  namesIn (ImpWhile cond body _) = Set.union (namesIn cond) (namesIn body)

instance CollectableNames (ImpProgram t)
  where namesIn (In p) = namesIn p


---------------------------
-- CollectableTypedNames --
---------------------------

instance CollectableTypedNames (ImpSkip t e) where
  typedNamesIn ImpSkip = Set.empty

instance Integral t => CollectableTypedNames (ImpAsgn t e) where
  typedNamesIn (ImpAsgn var aexp) = Set.insert (TypedName var Int) $ typedNamesIn aexp

instance CollectableTypedNames e => CollectableTypedNames (ImpSeq t e) where
  typedNamesIn (ImpSeq stmts) = typedNamesIn stmts

instance (Integral t, CollectableTypedNames e) => CollectableTypedNames (ImpIf t e) where
  typedNamesIn (ImpIf cond bThen bElse) = Set.unions
    [typedNamesIn cond, typedNamesIn bThen, typedNamesIn bElse]

instance (Integral t, CollectableTypedNames e) => CollectableTypedNames (ImpWhile t e) where
  typedNamesIn (ImpWhile cond body _) = Set.union (typedNamesIn cond) (typedNamesIn body)

instance Integral t => CollectableTypedNames (ImpProgram t)
  where typedNamesIn (In p) = typedNamesIn p


-------------------
-- MappableNames --
-------------------

instance MappableNames (ImpSkip t e) where
  mapNames _ ImpSkip = ImpSkip

instance MappableNames (ImpAsgn t e) where
  mapNames f (ImpAsgn var aexp) = ImpAsgn (f var) (mapNames f aexp)

instance MappableNames e => MappableNames (ImpSeq t e) where
  mapNames f (ImpSeq stmts) = ImpSeq $ mapNames f stmts

instance MappableNames e => MappableNames (ImpIf t e) where
  mapNames f (ImpIf c t e) = ImpIf (mapNames f c) (mapNames f t) (mapNames f e)

instance MappableNames e => MappableNames (ImpWhile t e) where
    mapNames f (ImpWhile cond body meta) =
      ImpWhile (mapNames f cond) (mapNames f body) (mapNames f meta)

instance MappableNames (ImpProgram t)
  where mapNames f (In p) = In $ mapNames f p


--------------------
-- FreshableNames --
--------------------

instance FreshableNames (ImpSkip t e) where
  freshen ImpSkip = return ImpSkip

instance FreshableNames (ImpAsgn t e) where
  freshen (ImpAsgn var aexp) = do
    var'  <- freshen var
    aexp' <- freshen aexp
    return $ ImpAsgn var' aexp'

instance FreshableNames e => FreshableNames (ImpSeq t e) where
  freshen (ImpSeq stmts) = return . ImpSeq =<< freshen stmts

instance FreshableNames e => FreshableNames (ImpIf t e) where
  freshen (ImpIf c t e) = do
    c' <- freshen c
    t' <- freshen t
    e' <- freshen e
    return $ ImpIf c' t' e'

instance FreshableNames e => FreshableNames (ImpWhile t e) where
  freshen (ImpWhile cond body meta) = do
    cond' <- freshen cond
    body' <- freshen body
    meta' <- freshen meta
    return $ ImpWhile cond' body' meta'

instance FreshableNames (ImpProgram t) where
  freshen (In p) = return . In =<< freshen p


-------------------------
-- CollectableLiterals --
-------------------------

instance CollectableLiterals (ImpSkip t e) t where
  litsIn ImpSkip = Set.empty

instance Ord t => CollectableLiterals (ImpAsgn t e) t where
  litsIn (ImpAsgn _ rhs) = litsIn rhs

instance (Ord t, CollectableLiterals e t) => CollectableLiterals (ImpSeq t e) t where
  litsIn (ImpSeq stmts) = litsIn stmts

instance (Ord t, CollectableLiterals e t) => CollectableLiterals (ImpIf t e) t where
  litsIn (ImpIf cond tBranch eBranch) = Set.unions
    [litsIn cond, litsIn tBranch, litsIn eBranch]

instance (Ord t, CollectableLiterals e t) => CollectableLiterals (ImpWhile t e) t where
  litsIn (ImpWhile cond body _) = Set.union (litsIn cond) (litsIn body)

instance Ord t => CollectableLiterals (ImpProgram t) t where
  litsIn (In f) = litsIn f


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

type ImpStep t = Ceili (Maybe (ProgState t))

instance Evaluable c t (ImpSkip t e) (ImpStep t) where
  eval _ st _ = return $ Just st

instance (Evaluable c t (AExp t) t) => Evaluable c t (ImpAsgn t e) (ImpStep t) where
  eval ctx st (ImpAsgn var aexp) = return $ Just $ Map.insert var (eval ctx st aexp) st

instance Evaluable c t e (ImpStep t) => Evaluable c t (ImpSeq t e) (ImpStep t) where
  eval = evalSeq

evalSeq :: Evaluable c t e (ImpStep t)
        => c -> ProgState t -> (ImpSeq t e) -> ImpStep t
evalSeq ctx st (ImpSeq stmts) =
  case stmts of
    [] -> return $ Just st
    (stmt:rest) -> do
      mSt' <- eval ctx st stmt
      case mSt' of
        Nothing  -> return Nothing
        Just st' -> evalSeq ctx st' (ImpSeq rest)

instance ( Evaluable c t (BExp t) Bool
         , Evaluable c t e (ImpStep t)
         )
        => Evaluable c t (ImpIf t e) (ImpStep t) where
  eval ctx st (ImpIf cond t f) = if   (eval ctx st cond)
                                 then (eval ctx st t)
                                 else (eval ctx st f)

instance ( FuelTank c
         , Evaluable c t (BExp t) Bool
         , Evaluable c t e (ImpStep t)
         )
        => Evaluable c t (ImpWhile t e) (ImpStep t) where
  eval = evalWhile

evalWhile :: ( FuelTank c
             , Evaluable c t (BExp t) Bool
             , Evaluable c t e (ImpStep t)
             )
          => c
          -> ProgState t
          -> (ImpWhile t e)
          -> ImpStep t
evalWhile ctx st (ImpWhile cond body meta) =
    case (eval ctx st cond) of
      False -> return $ Just st
      True  ->
        let ctx' = decrementFuel ctx
        in case (getFuel ctx') of
          Fuel n | n <= 0 -> do log_e "Evaluation ran out of fuel"
                                return Nothing
          _ -> do
            mSt' <- eval ctx' st body
            case mSt' of
              Nothing  -> return Nothing
              Just st' -> evalWhile ctx' st' (ImpWhile cond body meta)

instance ( FuelTank c
         , Evaluable c t (AExp t) t
         , Evaluable c t (BExp t) Bool
         )
        => Evaluable c t (ImpProgram t) (ImpStep t) where
  eval ctx st (In program) = eval ctx st program


----------------------
-- Loop Head States --
----------------------

type LoopHeadStates t = Map UUID (IterStateMap t)
type IterStateMap t   = Map Int (Set (ProgState t))

class Evaluable ctx t expr (ImpStep t) => CollectLoopHeadStates ctx expr t where
  collectLoopHeadStates :: ctx -> [ProgState t] -> expr -> Ceili (LoopHeadStates t)

instance CollectLoopHeadStates c (ImpSkip t e) t where
  collectLoopHeadStates _ _ _ = return Map.empty

instance Evaluable c t (AExp t) t => CollectLoopHeadStates c (ImpAsgn t e) t where
  collectLoopHeadStates _ _ _ = return Map.empty

instance ( Ord t
         , CollectLoopHeadStates c e t
         )
         => CollectLoopHeadStates c (ImpSeq t e) t where
  collectLoopHeadStates = seqHeadStates

seqHeadStates :: (Ord t, CollectLoopHeadStates c e t)
              => c
              -> [ProgState t]
              -> ImpSeq t e
              -> Ceili (LoopHeadStates t)
seqHeadStates ctx sts (ImpSeq stmts) =
  case stmts of
    [] -> return Map.empty
    stmt:rest -> do
      stmtHeads <- collectLoopHeadStates ctx sts stmt
      mSts' <- sequence $ map (\st -> eval ctx st stmt) sts
      let sts' = catMaybes mSts'
      restHeads <- seqHeadStates ctx sts' (ImpSeq rest)
      return $ unionLoopHeadStates stmtHeads restHeads

instance ( Ord t
         , Evaluable c t (BExp t) Bool
         , CollectLoopHeadStates c e t
         )
         => CollectLoopHeadStates c (ImpIf t e) t where
  collectLoopHeadStates ctx sts (ImpIf cond t f) =
    let (tStates, fStates) = partition (\st -> eval ctx st cond) sts
    in do
      tHeads <- collectLoopHeadStates ctx tStates t
      fHeads <- collectLoopHeadStates ctx fStates f
      return $ unionLoopHeadStates tHeads fHeads

instance ( FuelTank c
         , Ord t
         , Evaluable c t (BExp t) Bool
         , CollectLoopHeadStates c e t
         )
         => CollectLoopHeadStates c (ImpWhile t e) t where
  collectLoopHeadStates ctx sts loop@(ImpWhile cond body meta) = do
    loopId <- case iwm_id meta of
      Nothing  -> throwError "Loop missing ID."
      Just lid -> return lid
    loopStates <- iterateLoopStates ctx 0 sts loop
    let (trueSts, _) = partition (\st -> eval ctx st cond) sts
    bodyStates <- collectLoopHeadStates ctx trueSts body
    return $ unionLoopHeadStates (Map.singleton loopId loopStates) bodyStates

iterateLoopStates :: ( FuelTank c
                     , Ord t
                     , Evaluable c t (BExp t) Bool
                     , Evaluable c t e (ImpStep t)
                     )
                  => c
                  -> Int
                  -> [ProgState t]
                  -> (ImpWhile t e)
                  -> Ceili (IterStateMap t)
iterateLoopStates ctx iterNum sts loop@(ImpWhile cond body _) = do
  let thisIter = Map.singleton iterNum (Set.fromList sts)
  case getFuel ctx of
    Fuel 0 -> return thisIter
    _ -> do
      let (trueSts, _) = partition (\st -> eval ctx st cond) sts
      case trueSts of
        [] -> return thisIter
        _  -> do
          nextSts <- sequence $ map (\st -> eval ctx st body) sts
          rest <- iterateLoopStates (decrementFuel ctx) (iterNum + 1) (catMaybes nextSts) loop
          return $ unionIterStates thisIter rest

instance (CollectLoopHeadStates c (f e) t, CollectLoopHeadStates c (g e) t) =>
         CollectLoopHeadStates c ((f :+: g) e) t where
  collectLoopHeadStates ctx st (Inl f) = collectLoopHeadStates ctx st f
  collectLoopHeadStates ctx st (Inr g) = collectLoopHeadStates ctx st g

instance ( FuelTank c
         , Ord t
         , Evaluable c t (AExp t) t
         , Evaluable c t (BExp t) Bool
         )
         => CollectLoopHeadStates c (ImpProgram t) t where
  collectLoopHeadStates fuel sts (In f) = collectLoopHeadStates fuel sts f

unionLoopHeadStates :: Ord t => LoopHeadStates t -> LoopHeadStates t -> LoopHeadStates t
unionLoopHeadStates = Map.unionWith unionIterStates

unionIterStates :: Ord t => IterStateMap t -> IterStateMap t -> IterStateMap t
unionIterStates = Map.unionWith Set.union

mapIterMapNames :: Ord t => (Name -> Name) -> IterStateMap t -> IterStateMap t
mapIterMapNames f iterMap = let
  assocList = Map.assocs iterMap
  mapAssoc (k, v) = (k, mapNames f v)
  in Map.fromAscList $ map mapAssoc assocList

freshenIterMapNames :: Ord t => IterStateMap t -> Freshener (IterStateMap t)
freshenIterMapNames iterMap = do
  let assocList = Map.assocs iterMap
  let freshenAssoc (k, v) = do v' <- freshen v; return (k, v')
  assocList' <- sequence $ map freshenAssoc assocList
  return $ Map.fromAscList assocList'


--------------------
-- Pretty Printer --
--------------------

instance Pretty (ImpSkip t e) where
  pretty _ = pretty "skip"

instance Pretty t => Pretty (ImpAsgn t e) where
  pretty (ImpAsgn lhs rhs) = pretty lhs <+> pretty ":=" <+> pretty rhs

instance Pretty e => Pretty (ImpSeq t e) where
  pretty (ImpSeq stmts) = vsep $ map (\stmt -> pretty stmt <> semi) stmts

instance (Pretty t, Pretty e) => Pretty (ImpIf t e) where
  pretty (ImpIf cond tBranch eBranch) =
    pretty "if" <> softline <> pretty cond
    <> softline <> pretty "then"
    <> line <> (indent 2 $ pretty tBranch)
    <> line <> pretty "else"
    <> line <> (indent 2 $ pretty eBranch)
    <> line <> pretty "endif"

instance (Pretty t, Pretty e) => Pretty (ImpWhile t e) where
  pretty (ImpWhile cond body _) =
    pretty "while" <> softline <> pretty cond
    <> line <> (indent 2 $ pretty body)
    <> line <> pretty "end"

instance Pretty t => Pretty (ImpProgram t) where
  pretty (In p) = pretty p


--------------------------------------------
-- Backward Predicate Transform (Partial) --
--------------------------------------------

class ImpPieContextProvider ctx t where
  impPieCtx :: ctx -> ImpPieContext t

data ImpPieContext t = ImpPieContext
  { pc_loopHeadStates :: LoopHeadStates t
  , pc_programNames   :: Set TypedName
  , pc_programLits    :: Set t
  }

class ImpBackwardPT ctx expr t where
  impBackwardPT :: ctx -> expr -> Assertion t -> Ceili (Assertion t)

instance ImpBackwardPT c (ImpSkip t e) t where
  impBackwardPT _ ImpSkip post = return post

instance ImpBackwardPT c (ImpAsgn t e) t where
  impBackwardPT _ (ImpAsgn lhs rhs) post =
    return $ A.subArith (TypedName lhs Int)
                        (aexpToArith rhs)
                        post

instance ImpBackwardPT c e t => ImpBackwardPT c (ImpSeq t e) t where
  impBackwardPT = impSeqBackwardPT

impSeqBackwardPT :: (ImpBackwardPT c e t)
                 => c
                 -> (ImpSeq t e)
                 -> Assertion t
                 -> Ceili (Assertion t)
impSeqBackwardPT ctx (ImpSeq stmts) post =
  case stmts of
    [] -> return post
    (s:ss) -> do
      post' <- impSeqBackwardPT ctx (ImpSeq ss) post
      impBackwardPT ctx s post'

instance ImpBackwardPT c e t => ImpBackwardPT c (ImpIf t e) t where
  impBackwardPT ctx (ImpIf condB tBranch eBranch) post = do
    wpT <- impBackwardPT ctx tBranch post
    wpE <- impBackwardPT ctx eBranch post
    let cond   = bexpToAssertion condB
        ncond  = A.Not $ cond
    return $ A.And [A.Imp cond wpT, A.Imp ncond wpE]

instance ( Num t
         , Ord t
         , SMTString t
         , AssertionParseable t
         , CollectableNames e
         , StatePredicate (Assertion t) t
         , ImpPieContextProvider c t
         , ImpBackwardPT c e t
         )
         => ImpBackwardPT c (ImpWhile t e) t where
  impBackwardPT ctx loop@(ImpWhile condB body _) post = let
    cond          = bexpToAssertion condB
    varSet        = Set.unions [namesIn condB, namesIn body]
    vars          = Set.toList varSet
    freshMapping  = snd $ buildFreshMap (buildFreshIds vars) vars
    (orig, fresh) = unzip $ Map.toList freshMapping
    freshen       = substituteAll orig fresh
    qNames        = Set.toList $ namesInToInt fresh
    in do
      mInv <- getLoopInvariant ctx loop post
      inv <- case mInv of
               Nothing -> do
                 log_i "Unable to find or infer loop invariant, proceding with False."
                 return A.AFalse
               Just i -> return i
      bodyWP <- impBackwardPT ctx body inv
      let loopWP = A.Forall qNames
                   (freshen $ A.Imp (A.And [cond, inv]) bodyWP)
      let endWP  = A.Forall qNames
                    (freshen $ A.Imp (A.And [A.Not cond, inv]) post)
      return $ A.And [inv, loopWP, endWP]

getLoopInvariant :: ( Num t
                    , Ord t
                    , SMTString t
                    , AssertionParseable t
                    , StatePredicate (Assertion t) t
                    , ImpPieContextProvider ctx t
                    , ImpBackwardPT ctx e t )
                 => ctx
                 -> ImpWhile t e
                 -> Assertion t
                 -> Ceili (Maybe (Assertion t))
getLoopInvariant ctx (ImpWhile condB body meta) post =
  case iwm_invariant meta of
    Just i  -> return $ Just i
    Nothing -> do
      let pieCtx = impPieCtx ctx
      let mHeadStates = do
            loopId <- iwm_id meta
            Map.lookup loopId $ pc_loopHeadStates pieCtx
      case mHeadStates of
        Nothing -> return Nothing
        Just testStates -> do
          let names = pc_programNames pieCtx
          let lits  = pc_programLits  pieCtx
          let tests = Set.toList . Set.unions . Map.elems $ testStates
          let cond  = bexpToAssertion condB
          Pie.loopInvGen names lits impBackwardPT ctx cond body post tests

instance (ImpBackwardPT c (f e) t, ImpBackwardPT c (g e) t) =>
         ImpBackwardPT c ((f :+: g) e) t where
  impBackwardPT ctx (Inl f) post = impBackwardPT ctx f post
  impBackwardPT ctx (Inr f) post = impBackwardPT ctx f post

instance ( Num t
         , Ord t
         , SMTString t
         , AssertionParseable t
         , StatePredicate (Assertion t) t
         , ImpPieContextProvider c t)
         => ImpBackwardPT c (ImpProgram t) t where
  impBackwardPT ctx (In f) post = impBackwardPT ctx f post


-------------------------------------------
-- Forward Predicate Transform (Partial) --
-------------------------------------------

class ImpForwardPT ctx expr t where
  impForwardPT :: ctx -> expr -> Assertion t -> Ceili (Assertion t)

instance ImpForwardPT c (ImpSkip t e) t where
  impForwardPT _ ImpSkip pre = return pre

instance forall c t e. ImpForwardPT c (ImpAsgn t e) t where
  impForwardPT _ (ImpAsgn lhs rhs) pre = do
    lhs' <- envFreshen lhs
    let
      subPre   = substitute lhs lhs' pre
      rhsArith = aexpToArith rhs
      ilhs     = TypedName lhs  Int
      ilhs'    = TypedName lhs' Int
      subRhs   = A.subArith ilhs (A.Var @t ilhs') rhsArith
    return $ A.Exists [ilhs'] $ A.And [A.Eq (A.Var ilhs) subRhs, subPre]

instance ImpForwardPT c e t => ImpForwardPT c (ImpSeq t e) t where
  impForwardPT = impSeqForwardPT

impSeqForwardPT :: (ImpForwardPT c e t)
                 => c
                 -> (ImpSeq t e)
                 -> Assertion t
                 -> Ceili (Assertion t)
impSeqForwardPT ctx (ImpSeq stmts) pre =
  case stmts of
    []     -> return pre
    (s:ss) -> do
      pre' <- impForwardPT ctx s pre
      impSeqForwardPT ctx (ImpSeq ss) pre'

instance ImpForwardPT c e t => ImpForwardPT c (ImpIf t e) t where
  impForwardPT ctx (ImpIf b s1 s2) pre = do
    let cond = bexpToAssertion b
    postS1 <- impForwardPT ctx s1 (A.And [pre, cond])
    postS2 <- impForwardPT ctx s2 (A.And [pre, A.Not cond])
    return $ A.Or [postS1, postS2]

instance ( Num t
         , Ord t
         , SMTString t
         , CollectableNames e
         , ImpForwardPT c e t )
        => ImpForwardPT c (ImpWhile t e) t where
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

instance (ImpForwardPT c (f e) t, ImpForwardPT c (g e) t) =>
         ImpForwardPT c ((f :+: g) e) t where
  impForwardPT ctx (Inl f) pre = impForwardPT ctx f pre
  impForwardPT ctx (Inr f) pre = impForwardPT ctx f pre

instance (Num t, Ord t, SMTString t) => ImpForwardPT c (ImpProgram t) t where
  impForwardPT ctx (In f) pre = impForwardPT ctx f pre


-------------
-- Utility --
-------------

namesInToInt :: CollectableNames c => c -> Set TypedName
namesInToInt c = let
   names = namesIn c
   in Set.map (\n -> TypedName n Int) names
