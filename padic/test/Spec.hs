module Main where

import Test.Tasty
import qualified Test.Commons
import qualified Test.Integer
import qualified Test.FixedInteger
import qualified Test.Rational
import qualified Test.FixedRational

-----------------------------------------------------------

testSuite :: TestTree
testSuite = testGroup "Padic module"
  [ Test.Commons.testSuite
  , Test.Integer.testSuite
  , Test.FixedInteger.testSuite
  , Test.Rational.testSuite
  , Test.FixedRational.testSuite
  ]

main = defaultMain testSuite 
