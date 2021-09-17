module Ceili.Assertion
  ( Arith(..)
  , ArithAlgebra(..)
  , Assertion(..)
  , AssertionAlgebra(..)
  , AssertionParseable(..)
  , Name(..)
  , ParseError
  , SubstitutableArith(..)
  , assertionAtState
  , freeVars
  , parseArith
  , parseAssertion
  , subAriths
  , toSMT
  ) where

import Ceili.Assertion.AssertionLanguage
import Ceili.Assertion.AssertionParser
import Ceili.ProgState
import qualified Data.Map as Map

assertionAtState :: ProgState t -> Assertion t -> Assertion t
assertionAtState st assertion = Map.foldrWithKey subArith assertion arithSt
  where arithSt = Map.map Num st
