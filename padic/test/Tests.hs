{-# LANGUAGE DataKinds #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE UndecidableInstances #-}

module Tests where

import Math.NumberTheory.Padic
import Test.Tasty
import Test.Tasty.HUnit
import Test.Tasty.QuickCheck
import Test.QuickCheck
import Data.Mod
import Data.Maybe
import Data.Ratio

instance Radix m => Arbitrary (Mod m) where
  arbitrary = fromInteger <$> arbitrary

integerZ :: Radix p => Gen (Z p)
integerZ = fromInteger <$> arbitrary

arbitraryZ :: Radix p => Gen (Z p)
arbitraryZ = fromDigits <$> infiniteList

rationalZ :: Radix p => Gen (Z p)
rationalZ = do
  a <- integerZ
  b <- suchThat integerZ (isJust . divMaybe a)
  return $ a `div` b

instance Radix m => Arbitrary (Z m) where
  arbitrary = oneof [integerZ, rationalZ, arbitraryZ]

integerQ :: Radix p => Gen (Q p)
integerQ = fromInteger <$> arbitrary

rationalQ :: Radix p => Gen (Q p)
rationalQ = do
  a <- integerQ
  b <- integerQ `suchThat` isInvertible
  return $ a / b

arbitraryQ :: Radix p => Gen (Q p)
arbitraryQ = fromDigits <$> infiniteList

instance Radix m => Arbitrary (Q m) where
  arbitrary = oneof [integerQ, rationalQ, arbitraryQ]

a @/= b = assertBool "" (a /= b)

------------------------------------------------------------
digitsTestZ :: Radix p => Z p -> Bool
digitsTestZ n = fromDigits (digits n) == n

digitsTestQ :: Radix p => Q p -> Property
digitsTestQ n = valuation n == 0 ==> fromDigits (digits n) == n

digitTests = testGroup "Conversion to and from digits"
  [ testProperty "Z 2" $ digitsTestZ @2
  , testProperty "Z 10" $ digitsTestZ @10
  , testProperty "Z 257" $ digitsTestZ @257
  , testProperty "Q 2" $ digitsTestQ @2
  , testProperty "Q 10" $ digitsTestQ @10
  , testProperty "Q 257" $ digitsTestQ @257
  ]
  
------------------------------------------------------------
equivTest :: TestTree
equivTest = testGroup "Equivalence tests"
  [ testCase "1" $ (0 :: Z' 10 5) @?= 432100000
  , testCase "2" $ (0 :: Z' 10 5) @/= 543210000
  , testCase "3" $ (87654321 :: Z' 10 5) @?= 87054321
  , testCase "4" $ (87654321 :: Z' 10 5) @/= 87604321
  , testCase "5" $ (0 :: Q' 10 5) @?= 432100000
  , testCase "6" $ (0 :: Q' 10 5) @/= 543210000
  , testCase "7" $ (1/7 :: Q' 10 5) @?= 57143
  , testCase "8" $ (1/7 :: Q' 10 5) @?= 657143
  , testCase "9" $ (1/7 :: Q' 10 5) @/= 67143
  ]

------------------------------------------------------------
cycleTest :: TestTree
cycleTest = testGroup "findCycle tests"
  [ testCase "1" $ findCycle 10 [1..5] @?= ([1..5],[])
  , testCase "2" $ findCycle 10 [1] @?= ([1],[])
  , testCase "3" $ findCycle 10 (repeat 1) @?= ([],[1])
  , testCase "4" $ findCycle 10 ([1..5] ++ repeat 1) @?= ([1..5],[1])
  , testCase "5" $ findCycle 10 ([1..15] ++ repeat 1) @?= ([1..10],[])
  , testCase "6" $ findCycle 10 ([1,1,1] ++ repeat 1) @?= ([],[1])
  , testCase "7" $ findCycle 10 ([2,1,1] ++ repeat 1) @?= ([2],[1])
  , testCase "8" $ findCycle 10 ([1,2,3] ++ cycle [1,2,3]) @?= ([],[1,2,3])
  , testCase "9" $ findCycle 10 ([2,3] ++ cycle [1,2,3]) @?= ([],[2,3,1])
  , testCase "10" $ findCycle 10 ([0,1,2,3] ++ cycle [1,2,3]) @?= ([0],[1,2,3])
  , testCase "11" $ findCycle 10 ([0,2,3] ++ cycle [1,2,3]) @?= ([0],[2,3,1])
  , testCase "12" $ findCycle 200 ([1..99] ++ cycle [100..200]) @?= ([1..99],[100..200])
  ]


------------------------------------------------------------
showTests = testGroup "String representation"
  [ showTestZ, showTestQ ]
  
showTestZ = testGroup "Z"
  [ testCase "0" $ show (0 :: Z 3) @?= "0"
  , testCase "3" $ show (3 :: Z 3) @?= "10"
  , testCase "-3" $ show (-3 :: Z 3) @?= "(2)0"
  , testCase "123" $ show (123 :: Z 10) @?= "123"
  , testCase "123" $ show (123 :: Z 2) @?= "1111011"
  , testCase "-123" $ show (-123 :: Z 10) @?= "(9)877"
  , testCase "1/23" $ show (1 `div` 23 :: Z 10) @?= "…65217391304347826087"
  , testCase "1/23" $ show (1 `div` 23 :: Z' 10 40) @?= "(6956521739130434782608)7"
  ]

showTestQ = testGroup "Q"
  [ testCase "0" $ show (0 :: Q 3) @?= "0.0"
  , testCase "3" $ show (3 :: Q 3) @?= "10.0"
  , testCase "-3" $ show (-3 :: Q 3) @?= "(2)0.0"
  , testCase "123" $ show (123 :: Q 10) @?= "123.0"
  , testCase "123" $ show (123 :: Q 2) @?= "1111011.0"
  , testCase "-123" $ show (-123 :: Q 10) @?= "(9)877.0"
  , testCase "1/2" $ show (1/2 :: Q 2) @?= "0.1"
  , testCase "-1/2" $ show (-1/2 :: Q 2) @?= "(1).1"
  , testCase "1/700" $ show (1/700 :: Q 10) @?= "(428571).43"
  , testCase "100/7" $ show (100/7 :: Q 10) @?= "(285714)300.0"
  , testCase "1/23" $ show (1/23 :: Q 10) @?= "…65217391304347826087.0"
  , testCase "1/23" $ show (1/23 :: Q' 10 40) @?= "(6956521739130434782608)7.0"
  ]

------------------------------------------------------------
testSuite :: TestTree
testSuite = testGroup "test"
  [
    cycleTest
  , showTests
  , digitTests 
  , equivTest
  ]

main = defaultMain testSuite 
