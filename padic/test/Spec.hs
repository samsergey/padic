module Main where

import Test.Tasty
import qualified Test.Commons
import qualified Test.Integer
import qualified Test.Rational
import qualified Test.Analysis

-----------------------------------------------------------

testSuite :: TestTree
testSuite = testGroup "Padic module"
  [
    Test.Commons.testSuite
  , Test.Integer.testSuite
  , Test.Rational.testSuite 
  --  Test.Analysis.testSuite
  ]

main = defaultMain testSuite 
