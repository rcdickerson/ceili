{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE OverloadedStrings #-}

module Ceili.Assertion.AssertionLanguage
  ( Arith(..)
  , Assertion(..)
  , Name(..)
  , SubstitutableArith(..)
  , eval
  , freeVars
  , subAriths
  , toSMT
  ) where

import Ceili.Evaluation
import Ceili.Literal
import Ceili.Name
import Ceili.ProgState
import Ceili.SMTString ( SMTString(..) )
import Data.ByteString ( ByteString )
import qualified Data.ByteString.Char8 as S8
import qualified Data.Map as Map
import Data.Set  ( Set )
import qualified Data.Set as Set
import Prettyprinter


----------------------------
-- Arithmetic Expressions --
----------------------------

data Arith t = Num t
             | Var TypedName
             | Add [Arith t]
             | Sub [Arith t]
             | Mul [Arith t]
             | Div (Arith t) (Arith t)
             | Mod (Arith t) (Arith t)
             | Pow (Arith t) (Arith t)
           deriving (Eq, Ord)

instance SMTString t => Show (Arith t) where
  show = S8.unpack . toSMT

toSexp :: SMTString a => ByteString -> [a] -> ByteString
toSexp name as = "(" <> name <> " "<> (S8.intercalate " " $ map toSMT as) <> ")"

instance MappableNames (Arith t) where
  mapNames f arith = case arith of
    Num x     -> Num x
    Var tname -> Var (mapNames f tname)
    Add as    -> Add $ map (mapNames f) as
    Sub as    -> Sub $ map (mapNames f) as
    Mul as    -> Mul $ map (mapNames f) as
    Div a1 a2 -> Div (mapNames f a1) (mapNames f a2)
    Mod a1 a2 -> Mod (mapNames f a1) (mapNames f a2)
    Pow a1 a2 -> Pow (mapNames f a1) (mapNames f a2)

instance CollectableNames (Arith t) where
  namesIn arith = case arith of
    Num _     -> Set.empty
    Var tname -> namesIn tname
    Add as    -> Set.unions $ map namesIn as
    Sub as    -> Set.unions $ map namesIn as
    Mul as    -> Set.unions $ map namesIn as
    Div a1 a2 -> Set.union (namesIn a1) (namesIn a2)
    Mod a1 a2 -> Set.union (namesIn a1) (namesIn a2)
    Pow a1 a2 -> Set.union (namesIn a1) (namesIn a2)

instance Integral t => CollectableTypedNames (Arith t) where
  typedNamesIn arith = Set.map (\n -> TypedName n Int) $ namesIn arith

instance FreshableNames (Arith t) where
  freshen arith = case arith of
    Num i     -> return $ Num i
    Var tname -> return . Var =<< freshen tname
    Add as    -> return . Add =<< freshen as
    Sub as    -> return . Sub =<< freshen as
    Mul as    -> return . Mul =<< freshen as
    Div a1 a2 -> freshenBinop Div a1 a2
    Mod a1 a2 -> freshenBinop Mod a1 a2
    Pow a1 a2 -> freshenBinop Pow a1 a2

instance Ord t => CollectableLiterals (Arith t) t where
  litsIn arith = case arith of
    Num i     -> Set.singleton i
    Var _     -> Set.empty
    Add as    -> Set.unions $ map litsIn as
    Sub as    -> Set.unions $ map litsIn as
    Mul as    -> Set.unions $ map litsIn as
    Div a1 a2 -> Set.union (litsIn a1) (litsIn a2)
    Mod a1 a2 -> Set.union (litsIn a1) (litsIn a2)
    Pow a1 a2 -> Set.union (litsIn a1) (litsIn a2)

instance SMTString t => SMTString (Arith t) where
  toSMT arith = case arith of
    Num n     -> toSMT n
    Var tname -> toSMT $ tn_name tname
    Add as    -> toSexp "+"   as
    Sub as    -> toSexp "-"   as
    Mul as    -> toSexp "*"   as
    Div a1 a2 -> toSexp "/"   [a1, a2]
    Mod a1 a2 -> toSexp "mod" [a1, a2]
    Pow a1 a2 -> toSexp "^"   [a1, a2]

instance Integral t => Evaluable c t (Arith t) t where
   eval _ = evalArith

evalArith :: Integral t => ProgState t -> Arith t -> t
evalArith state arith = case arith of
  Num i     -> i
  Var v     -> case Map.lookup (tn_name v) state of
                 Nothing -> 0
                 Just n  -> n
  Add as    -> foldr (+) 0 $ map (evalArith state) as
  Sub as    -> case as of
                 []      -> 0
                 (a:as') -> foldl (-) (evalArith state a)
                            $ map (evalArith state) as'
  Mul as    -> foldr (*) 1 $ map (evalArith state) as
  Div a1 a2 -> (evalArith state a1) `quot` (evalArith state a2)
  Mod a1 a2 -> (evalArith state a1) `mod`  (evalArith state a2)
  Pow a1 a2 -> (evalArith state a1) ^      (evalArith state a2)


----------------
-- Assertions --
----------------

data Assertion t = ATrue
                 | AFalse
                 | Atom     TypedName
                 | Not      (Assertion t)
                 | And      [Assertion t]
                 | Or       [Assertion t]
                 | Imp      (Assertion t) (Assertion t)
                 | Eq       (Arith t) (Arith t)
                 | Lt       (Arith t) (Arith t)
                 | Gt       (Arith t) (Arith t)
                 | Lte      (Arith t) (Arith t)
                 | Gte      (Arith t) (Arith t)
                 | Forall   [TypedName] (Assertion t)
                 | Exists   [TypedName] (Assertion t)
               deriving (Eq, Ord)

instance SMTString t => Show (Assertion t) where
  show = S8.unpack . toSMT

instance MappableNames (Assertion t) where
  mapNames f assertion = case assertion of
    ATrue       -> ATrue
    AFalse      -> AFalse
    Atom tname  -> Atom $ mapNames f tname
    Not a       -> Not  $ mapNames f a
    And as      -> And  $ map (mapNames f) as
    Or as       -> Or   $ map (mapNames f) as
    Imp a1 a2   -> Imp (mapNames f a1) (mapNames f a2)
    Eq a1 a2    -> Eq  (mapNames f a1) (mapNames f a2)
    Lt a1 a2    -> Lt  (mapNames f a1) (mapNames f a2)
    Gt a1 a2    -> Gt  (mapNames f a1) (mapNames f a2)
    Lte a1 a2   -> Lte (mapNames f a1) (mapNames f a2)
    Gte a1 a2   -> Gte (mapNames f a1) (mapNames f a2)
    Forall vs a -> Forall (map (mapNames f) vs) (mapNames f a)
    Exists vs a -> Exists (map (mapNames f) vs) (mapNames f a)

instance CollectableNames (Assertion t) where
  namesIn assertion = case assertion of
    ATrue       -> Set.empty
    AFalse      -> Set.empty
    Atom tname  -> namesIn tname
    Not a       -> namesIn a
    And as      -> Set.unions $ map namesIn as
    Or as       -> Set.unions $ map namesIn as
    Imp a1 a2   -> Set.union (namesIn a1) (namesIn a2)
    Eq a1 a2    -> Set.union (namesIn a1) (namesIn a2)
    Lt a1 a2    -> Set.union (namesIn a1) (namesIn a2)
    Gt a1 a2    -> Set.union (namesIn a1) (namesIn a2)
    Lte a1 a2   -> Set.union (namesIn a1) (namesIn a2)
    Gte a1 a2   -> Set.union (namesIn a1) (namesIn a2)
    Forall vs a -> Set.unions $ (namesIn a):(map namesIn vs)
    Exists vs a -> Set.unions $ (namesIn a):(map namesIn vs)

instance Integral t => CollectableTypedNames (Assertion t) where
  typedNamesIn assertion = Set.map (\n -> TypedName n Int) $ namesIn assertion

instance FreshableNames (Assertion t) where
  freshen assertion = case assertion of
    ATrue       -> return ATrue
    AFalse      -> return AFalse
    Atom tname  -> return . Atom =<< freshen tname
    Not a       -> return . Not =<< freshen a
    And as      -> return . And =<< freshen as
    Or as       -> return . Or =<< freshen as
    Imp a1 a2   -> freshenBinop Imp a1 a2
    Eq a1 a2    -> freshenBinop Eq a1 a2
    Lt a1 a2    -> freshenBinop Lt a1 a2
    Gt a1 a2    -> freshenBinop Gt a1 a2
    Lte a1 a2   -> freshenBinop Lte a1 a2
    Gte a1 a2   -> freshenBinop Gte a1 a2
    Forall vs a -> quant Forall vs a
    Exists vs a -> quant Exists vs a
    where
      quant op vs a = do
        vs' <- freshen vs
        a'  <- freshen a
        return $ op vs' a'

instance Ord t => CollectableLiterals (Assertion t) t where
  litsIn assertion = case assertion of
    ATrue      -> Set.empty
    AFalse     -> Set.empty
    Atom _     -> Set.empty
    Not a      -> litsIn a
    And as     -> Set.unions $ map litsIn as
    Or as      -> Set.unions $ map litsIn as
    Imp a1 a2  -> Set.union (litsIn a1) (litsIn a2)
    Eq a1 a2   -> Set.union (litsIn a1) (litsIn a2)
    Lt a1 a2   -> Set.union (litsIn a1) (litsIn a2)
    Gt a1 a2   -> Set.union (litsIn a1) (litsIn a2)
    Lte a1 a2  -> Set.union (litsIn a1) (litsIn a2)
    Gte a1 a2  -> Set.union (litsIn a1) (litsIn a2)
    Forall _ a -> litsIn a
    Exists _ a -> litsIn a

instance Integral t => Evaluable c t (Assertion t) Bool where
 eval ctx state assertion = case assertion of
   ATrue     -> True
   AFalse    -> False
   Atom _    -> False -- This assumes states cannot store booleans.
   Not a     -> not $ eval ctx state a
   And as    -> and $ map (eval ctx state) as
   Or  as    -> or  $ map (eval ctx state) as
   Imp a1 a2 -> not (eval ctx state a1) || eval ctx state a2
   Eq  a1 a2 -> (evalArith state a1) == (evalArith state a2)
   Lt  a1 a2 -> (evalArith state a1) <  (evalArith state a2)
   Gt  a1 a2 -> (evalArith state a1) >  (evalArith state a2)
   Lte a1 a2 -> (evalArith state a1) <= (evalArith state a2)
   Gte a1 a2 -> (evalArith state a1) >= (evalArith state a2)
   Forall _ _ -> error "Quantified formulas not supported."
   Exists _ _ -> error "Quantified formulas not supported."

instance SMTString t => SMTString (Assertion t) where
  toSMT assertion = case assertion of
    ATrue           -> "true"
    AFalse          -> "false"
    Atom tname      -> toSMT $ tn_name tname
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
      quantToSMT :: SMTString t => ByteString -> [TypedName] -> Assertion t -> ByteString
      quantToSMT name qvars body =
        let qvarsSMT = S8.intercalate " " $ map toSMT qvars
        in "(" <> name <> " (" <> qvarsSMT <> ") " <> toSMT body <> ")"


------------------------------
--- Arithmetic Substitution --
------------------------------

class SubstitutableArith t a where
  subArith :: TypedName -> (Arith t) -> a -> a

instance SubstitutableArith t (Arith t) where
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

instance SubstitutableArith t (Assertion t) where
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

subAriths :: SubstitutableArith t a => [TypedName] -> [Arith t] -> a -> a
subAriths from to sa = foldr (uncurry subArith) sa $ zip from to


--------------------
-- Free Variables --
--------------------

class FreeVariables a where
  freeVars :: a -> Set TypedName

instance FreeVariables (Arith t) where
  freeVars arith = case arith of
    Num _     -> Set.empty
    Var ident -> Set.singleton ident
    Add as    -> Set.unions $ map freeVars as
    Sub as    -> Set.unions $ map freeVars as
    Mul as    -> Set.unions $ map freeVars as
    Div a1 a2 -> Set.union (freeVars a1) (freeVars a2)
    Mod a1 a2 -> Set.union (freeVars a1) (freeVars a2)
    Pow a1 a2 -> Set.union (freeVars a1) (freeVars a2)

instance FreeVariables (Assertion t) where
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


--------------------
-- Pretty Printer --
--------------------

instance SMTString t => Pretty (Arith t) where
  pretty = pretty . S8.unpack . toSMT

instance SMTString t => Pretty (Assertion t) where
  pretty = pretty . S8.unpack . toSMT
