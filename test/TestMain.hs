{-# OPTIONS_GHC -F -pgmF htfpp #-}
module Main where

import Test.Framework
import {-@ HTF_TESTS @-} Ceili.AssertionTest
import {-@ HTF_TESTS @-} Ceili.Language.FunImpParserTest
import {-@ HTF_TESTS @-} Ceili.Language.ImpTest
import {-@ HTF_TESTS @-} Ceili.Language.ImpParserTest
import {-@ HTF_TESTS @-} Ceili.NameTest

main = htfMain htf_importedTests
