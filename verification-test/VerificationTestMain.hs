{-# OPTIONS_GHC -F -pgmF htfpp #-}
module VerificationTestMain where

import Test.Framework

main = htfMain htf_thisModulesTests

test_foo = assertEqual True True
