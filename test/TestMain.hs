{-# OPTIONS_GHC -F -pgmF htfpp #-}
module Main where

import Test.Framework

main = htfMain htf_importedTests
