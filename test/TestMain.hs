{-# OPTIONS_GHC -F -pgmF htfpp #-}
module Main where

import Test.Framework
import {-@ HTF_TESTS @-} Ceili.AssertionTest
import {-@ HTF_TESTS @-} Ceili.NameTest

main = htfMain htf_importedTests
