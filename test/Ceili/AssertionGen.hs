-- Abitrary assertion generation for Quickcheck.

module Ceili.AssertionGen where
import Test.Framework

import Control.Monad ( liftM, liftM2 )
import Data.Char ( isAlpha, isAscii )
import Ceili.Assertion
import Ceili.Name

instance Arbitrary Name where
  arbitrary = do
    first <- suchThat arbNameChar isAlpha
    rest  <- listOf arbNameChar
    i <- chooseInt (0, 10000)
    return $ Name (first:rest) i

arbNameChar :: Gen Char
arbNameChar = elements $ ['!', '_', '.'] ++ ['a'..'z'] ++ ['A'..'Z']

validName :: String -> Bool
validName str = case str of
  []    -> False
  (c:_) -> isAscii c && isAlpha c

instance Arbitrary TypedName where
  arbitrary = arbTypedName =<< oneof [ return Bool
                                     , return Int
                                     ]

arbTypedName :: Type -> Gen TypedName
arbTypedName ty = liftM (\n -> TypedName n ty) arbitrary

instance Arbitrary Arith where
  arbitrary = sized arbArith

arbArith :: Int -> Gen Arith
arbArith 0 = oneof [ liftM Num arbitrary
                   , liftM Var $ arbTypedName Int
                   ]
arbArith n = oneof [ liftM  Add $ vector (n - 1)
                   , liftM  Sub $ vector (n - 1)
                   , liftM  Mul $ vector (n - 1)
                   , liftM2 Div (arbArith $ n - 1) (arbArith $ n - 1)
                   , liftM2 Mod (arbArith $ n - 1) (arbArith $ n - 1)
                   , liftM2 Pow (arbArith $ n - 1) (arbArith $ n - 1)
                   ]

instance Arbitrary Assertion where
  arbitrary = sized arbAssertion

arbAssertion :: Int -> Gen Assertion
arbAssertion 0 = oneof [ return ATrue
                       , return AFalse
                       , liftM Atom $ arbTypedName Bool
                       ]
arbAssertion n = oneof [ liftM  Not $ arbAssertion (n - 1)
                       , liftM  And $ vector (n - 1)
                       , liftM  Or  $ vector (n - 1)
                       , liftM2 Imp (arbAssertion $ n - 1) (arbAssertion $ n - 1)
                       , liftM2 Eq  (arbArith $ n - 1) (arbArith $ n - 1)
                       , liftM2 Lt  (arbArith $ n - 1) (arbArith $ n - 1)
                       , liftM2 Gt  (arbArith $ n - 1) (arbArith $ n - 1)
                       , liftM2 Lte (arbArith $ n - 1) (arbArith $ n - 1)
                       , liftM2 Gte (arbArith $ n - 1) (arbArith $ n - 1)
                       , liftM2 Forall (vector $ n - 1) (arbAssertion $ n - 1)
                       , liftM2 Exists (vector $ n - 1) (arbAssertion $ n - 1)
                     --, Uninterp (omitted)
                       ]
