module Ceili.Assertion
  ( Arith(..)
  , Assertion(..)
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
import Ceili.Language.AExp
import Ceili.State
import qualified Data.Map as Map

assertionAtState :: State -> Assertion -> Assertion
assertionAtState st assertion = Map.foldrWithKey subArith assertion arithSt
  where arithSt = Map.map Num $ withTypedKeys st
