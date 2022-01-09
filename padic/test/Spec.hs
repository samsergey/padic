module Main where

import Test.Tasty
import qualified Test.Commons
import qualified Test.Integer
import qualified Test.Rational

-----------------------------------------------------------

testSuite :: TestTree
testSuite = testGroup "Padic module"
  [ Test.Commons.testSuite
  , Test.Integer.testSuite
  , Test.Rational.testSuite
  ]

main = defaultMain testSuite 
