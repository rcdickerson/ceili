{-# LANGUAGE OverloadedStrings #-}

module Ceili.Language.AExp
  ( AExp(..)
  , State
  , aexpToArith
  , evalAExp
  ) where

import qualified Ceili.Assertion.AssertionLanguage as A
import Ceili.Name
import Ceili.Literal
import Ceili.SMTString
import Ceili.State
import qualified Data.Map as Map
import qualified Data.Set as Set
import Prettyprinter

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

instance CollectableTypedNames AExp where
  typedNamesIn aexp = Set.map (\n -> TypedName n Int) $ namesIn aexp

instance MappableNames AExp where
  mapNames f aexp = case aexp of
    ALit i       -> ALit i
    AVar v       -> AVar (f v)
    AAdd lhs rhs -> AAdd (mapNames f lhs) (mapNames f rhs)
    ASub lhs rhs -> ASub (mapNames f lhs) (mapNames f rhs)
    AMul lhs rhs -> AMul (mapNames f lhs) (mapNames f rhs)
    ADiv lhs rhs -> ADiv (mapNames f lhs) (mapNames f rhs)
    AMod lhs rhs -> AMod (mapNames f lhs) (mapNames f rhs)
    APow lhs rhs -> APow (mapNames f lhs) (mapNames f rhs)

instance FreshableNames AExp where
  freshen aexp = case aexp of
    ALit i -> return $ ALit i
    AVar v -> return . AVar =<< freshen v
    AAdd lhs rhs -> freshenBinop AAdd lhs rhs
    ASub lhs rhs -> freshenBinop ASub lhs rhs
    AMul lhs rhs -> freshenBinop AMul lhs rhs
    ADiv lhs rhs -> freshenBinop ADiv lhs rhs
    AMod lhs rhs -> freshenBinop AMod lhs rhs
    APow lhs rhs -> freshenBinop APow lhs rhs

instance CollectableLiterals AExp where
  litsIn aexp = case aexp of
    ALit i -> Set.singleton i
    AVar _ -> Set.empty
    AAdd lhs rhs -> Set.union (litsIn lhs) (litsIn rhs)
    ASub lhs rhs -> Set.union (litsIn lhs) (litsIn rhs)
    AMul lhs rhs -> Set.union (litsIn lhs) (litsIn rhs)
    ADiv lhs rhs -> Set.union (litsIn lhs) (litsIn rhs)
    AMod lhs rhs -> Set.union (litsIn lhs) (litsIn rhs)
    APow lhs rhs -> Set.union (litsIn lhs) (litsIn rhs)

aexpToArith :: AExp -> A.Arith
aexpToArith aexp = case aexp of
  ALit i           -> A.Num i
  AVar var         -> A.Var (TypedName var Int)
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


--------------------
-- Pretty Printer --
--------------------

instance Pretty AExp where
  pretty aexp =
    case aexp of
      ALit i -> pretty i
      AVar name -> pretty $ showSMT name
      AAdd lhs rhs -> maybeParens lhs <+> "+" <+> maybeParens rhs
      ASub lhs rhs -> maybeParens lhs <+> "-" <+> maybeParens rhs
      AMul lhs rhs -> maybeParens lhs <+> "*" <+> maybeParens rhs
      ADiv lhs rhs -> maybeParens lhs <+> "/" <+> maybeParens rhs
      AMod lhs rhs -> maybeParens lhs <+> "%" <+> maybeParens rhs
      APow lhs rhs -> maybeParens lhs <+> "^" <+> maybeParens rhs

maybeParens :: AExp -> Doc ann
maybeParens aexp =
  case aexp of
    ALit _ -> pretty aexp
    AVar _ -> pretty aexp
    _      -> parens $ pretty aexp
