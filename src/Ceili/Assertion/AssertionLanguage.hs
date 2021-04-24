{-# LANGUAGE OverloadedStrings #-}

module Ceili.Assertion.AssertionLanguage
  ( Arith(..)
  , Assertion(..)
  , Name(..)
  , freeVars
  , subArith
  , toSMT
  ) where

import Ceili.Name ( Name(..)
                  , TypedName(..)
                  , CollectableNames(..)
                  , MappableNames(..) )
import Ceili.SMTString ( SMTString(..) )
import Data.ByteString ( ByteString )
import qualified Data.ByteString.Char8 as S8
import Data.Set  ( Set )
import qualified Data.Set as Set

----------------------------
-- Arithmetic Expressions --
----------------------------

data Arith = Num Integer
           | Var TypedName
           | Add [Arith]
           | Sub [Arith]
           | Mul [Arith]
           | Div Arith Arith
           | Mod Arith Arith
           | Pow Arith Arith
           deriving (Show, Eq, Ord)

toSexp :: SMTString a => ByteString -> [a] -> ByteString
toSexp name as = "(" <> name <> " "<> (S8.intercalate " " $ map toSMT as) <> ")"

instance MappableNames Arith where
  mapNames f arith = case arith of
    Num x     -> Num x
    Var tname -> Var (mapNames f tname)
    Add as    -> Add $ map (mapNames f) as
    Sub as    -> Sub $ map (mapNames f) as
    Mul as    -> Mul $ map (mapNames f) as
    Div a1 a2 -> Div (mapNames f a1) (mapNames f a2)
    Mod a1 a2 -> Mod (mapNames f a1) (mapNames f a2)
    Pow a1 a2 -> Pow (mapNames f a1) (mapNames f a2)

instance CollectableNames Arith where
  namesIn arith = case arith of
    Num _     -> Set.empty
    Var tname -> namesIn tname
    Add as    -> Set.unions $ map namesIn as
    Sub as    -> Set.unions $ map namesIn as
    Mul as    -> Set.unions $ map namesIn as
    Div a1 a2 -> Set.union (namesIn a1) (namesIn a2)
    Mod a1 a2 -> Set.union (namesIn a1) (namesIn a2)
    Pow a1 a2 -> Set.union (namesIn a1) (namesIn a2)

instance SMTString Arith where
  toSMT arith = case arith of
    Num n -> S8.pack $ show n
    Var tname -> toSMT $ tnName tname
    Add as    -> toSexp "+"   as
    Sub as    -> toSexp "-"   as
    Mul as    -> toSexp "*"   as
    Div a1 a2 -> toSexp "/"   [a1, a2]
    Mod a1 a2 -> toSexp "mod" [a1, a2]
    Pow a1 a2 -> toSexp "^"   [a1, a2]


----------------
-- Assertions --
----------------

data Assertion = ATrue
               | AFalse
               | Atom     TypedName
               | Not      Assertion
               | And      [Assertion]
               | Or       [Assertion]
               | Imp      Assertion Assertion
               | Eq       Arith Arith
               | Lt       Arith Arith
               | Gt       Arith Arith
               | Lte      Arith Arith
               | Gte      Arith Arith
               | Forall   [TypedName] Assertion
               | Exists   [TypedName] Assertion
               deriving (Eq, Ord, Show)

instance MappableNames Assertion where
  mapNames f assertion = case assertion of
    ATrue         -> ATrue
    AFalse        -> AFalse
    Atom tname    -> Atom $ mapNames f tname
    Not a         -> Not  $ mapNames f a
    And as        -> And  $ map (mapNames f) as
    Or as         -> Or   $ map (mapNames f) as
    Imp a1 a2     -> Imp (mapNames f a1) (mapNames f a2)
    Eq a1 a2      -> Eq  (mapNames f a1) (mapNames f a2)
    Lt a1 a2      -> Lt  (mapNames f a1) (mapNames f a2)
    Gt a1 a2      -> Gt  (mapNames f a1) (mapNames f a2)
    Lte a1 a2     -> Lte (mapNames f a1) (mapNames f a2)
    Gte a1 a2     -> Gte (mapNames f a1) (mapNames f a2)
    Forall vs a   -> Forall (map (mapNames f) vs) (mapNames f a)
    Exists vs a   -> Exists (map (mapNames f) vs) (mapNames f a)

instance CollectableNames Assertion where
  namesIn assertion = case assertion of
    ATrue          -> Set.empty
    AFalse         -> Set.empty
    Atom tname     -> namesIn tname
    Not a          -> namesIn a
    And as         -> Set.unions $ map namesIn as
    Or as          -> Set.unions $ map namesIn as
    Imp a1 a2      -> Set.union (namesIn a1) (namesIn a2)
    Eq a1 a2       -> Set.union (namesIn a1) (namesIn a2)
    Lt a1 a2       -> Set.union (namesIn a1) (namesIn a2)
    Gt a1 a2       -> Set.union (namesIn a1) (namesIn a2)
    Lte a1 a2      -> Set.union (namesIn a1) (namesIn a2)
    Gte a1 a2      -> Set.union (namesIn a1) (namesIn a2)
    Forall vs a    -> Set.unions $ (namesIn a):(map namesIn vs)
    Exists vs a    -> Set.unions $ (namesIn a):(map namesIn vs)

instance SMTString Assertion where
  toSMT assertion = case assertion of
    ATrue           -> "true"
    AFalse          -> "false"
    Atom tname      -> toSMT $ tnName tname
    Not a           -> toSexp "not" [a]
    And as          -> toSexp "and" as
    Or as           -> toSexp "or" as
    Imp a1 a2       -> toSexp "=>" [a1, a2]
    Eq a1 a2        -> toSexp "="  [a1, a2]
    Lt a1 a2        -> toSexp "<"  [a1, a2]
    Gt a1 a2        -> toSexp ">"  [a1, a2]
    Lte a1 a2       -> toSexp "<=" [a1, a2]
    Gte a1 a2       -> toSexp ">=" [a1, a2]
    Forall vars a   -> quantToSMT "forall" vars a
    Exists vars a   -> quantToSMT "exists" vars a
    where
      quantToSMT :: ByteString -> [TypedName] -> Assertion -> ByteString
      quantToSMT name qvars body =
        let qvarsSMT = S8.intercalate " " $ map toSMT qvars
        in "(" <> name <> " (" <> qvarsSMT <> ") " <> toSMT body <> ")"


------------------------------
--- Arithmetic Substitution --
------------------------------

class SubstitutableArith a where
  subArith :: TypedName -> Arith -> a -> a

instance SubstitutableArith Arith where
  subArith from to arith =
    let sub = subArith from to
    in case arith of
      Num x     -> Num x
      Var tname -> if from == tname then to else Var tname
      Add as    -> Add $ map sub as
      Sub as    -> Sub $ map sub as
      Mul as    -> Mul $ map sub as
      Div a1 a2 -> Div (sub a1) (sub a2)
      Mod a1 a2 -> Mod (sub a1) (sub a2)
      Pow a1 a2 -> Pow (sub a1) (sub a2)

instance SubstitutableArith Assertion where
  subArith from to assertion =
    let sub = subArith from to
    in case assertion of
      ATrue         -> ATrue
      AFalse        -> AFalse
      Atom tname    -> Atom tname
      Not a         -> Not $ sub a
      And as        -> And $ map sub as
      Or as         -> Or  $ map sub as
      Imp a1 a2     -> Imp (sub a1) (sub a2)
      Eq a1 a2      -> Eq  (subArith from to a1) (subArith from to a2)
      Lt a1 a2      -> Lt  (subArith from to a1) (subArith from to a2)
      Gt a1 a2      -> Gt  (subArith from to a1) (subArith from to a2)
      Lte a1 a2     -> Lte (subArith from to a1) (subArith from to a2)
      Gte a1 a2     -> Gte (subArith from to a1) (subArith from to a2)
      Forall vars a -> Forall vars (sub a)
      Exists vars a -> Exists vars (sub a)


--------------------
-- Free Variables --
--------------------

class FreeVariables a where
  freeVars :: a -> Set TypedName

instance FreeVariables Arith where
  freeVars arith = case arith of
    Num _     -> Set.empty
    Var ident -> Set.singleton ident
    Add as    -> Set.unions $ map freeVars as
    Sub as    -> Set.unions $ map freeVars as
    Mul as    -> Set.unions $ map freeVars as
    Div a1 a2 -> Set.union (freeVars a1) (freeVars a2)
    Mod a1 a2 -> Set.union (freeVars a1) (freeVars a2)
    Pow a1 a2 -> Set.union (freeVars a1) (freeVars a2)

instance FreeVariables Assertion where
  freeVars assertion = case assertion of
    ATrue        -> Set.empty
    AFalse       -> Set.empty
    Atom i       -> Set.singleton i
    Not  a       -> freeVars a
    And  as      -> Set.unions $ map freeVars as
    Or   as      -> Set.unions $ map freeVars as
    Imp  a1 a2   -> Set.union (freeVars a1) (freeVars a2)
    Eq   a1 a2   -> Set.union (freeVars a1) (freeVars a2)
    Lt   a1 a2   -> Set.union (freeVars a1) (freeVars a2)
    Gt   a1 a2   -> Set.union (freeVars a1) (freeVars a2)
    Lte  a1 a2   -> Set.union (freeVars a1) (freeVars a2)
    Gte  a1 a2   -> Set.union (freeVars a1) (freeVars a2)
    Forall ids a -> Set.difference (freeVars a) (Set.fromList ids)
    Exists ids a -> Set.difference (freeVars a) (Set.fromList ids)
