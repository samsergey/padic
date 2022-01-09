{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}

module Test.FixedInteger (testSuite) where

import Math.NumberTheory.Padic.Fixed
import Test.Base
import GHC.TypeLits hiding (Mod)
import Test.Tasty
import Test.Tasty.HUnit
import Test.Tasty.QuickCheck
import Test.Tasty.ExpectedFailure
import Test.QuickCheck
import Data.Mod

------------------------------------------------------------
digitsTestZ :: (Show n, Eq n, PadicNum n) => n -> n -> Property
digitsTestZ t n = fromDigits (digits n) === n

digitsTests = testGroup "Conversion to and from digits"
  [ testProperty "Z 2" $ digitsTestZ (0 :: Z 2)
  , testProperty "Z 10" $ digitsTestZ (0 :: Z 10)
  , testProperty "Z 257" $ digitsTestZ (0 :: Z 257)
  ]
  
------------------------------------------------------------
equivTest :: TestTree
equivTest = testGroup "Equivalence tests"
  [ testCase "1" $ (0 :: Z' 10 5) @?= 432100000
  , testCase "2" $ (0 :: Z' 10 5) @/= 543210000
  , testCase "3" $ (87654321 :: Z' 10 5) @?= 87054321
  , testCase "4" $ (87654321 :: Z' 10 5) @/= 87604321
  ]

------------------------------------------------------------
showTests = testGroup "String representation"
  [ testCase "0" $ show (0 :: Z 3) @?= "0"
  , testCase "3" $ show (3 :: Z 3) @?= "10"
  , testCase "-3" $ show (-3 :: Z 3) @?= "…22222222222222222220"
  , testCase "123" $ show (123 :: Z 10) @?= "123"
  , testCase "123" $ show (123 :: Z 2) @?= "1111011"
  , testCase "123456789" $ show (123456789 :: Z' 10 5) @?= "…56789"
  , testCase "-123" $ show (-123 :: Z 10) @?= "…99999999999999999877"
  , testCase "1/23" $ show (1 `div` 23 :: Z 10) @?= "…65217391304347826087"
  , testCase "1/23" $ show (1 `div` 23 :: Z' 17 5) @?= "… 8 14 13 5 3"
  , testCase "123456" $ show (123456 :: Z' 257 4) @?= "1 223 96"
  , testCase "123456" $ show (-123456 :: Z' 257 6) @?= "… 256 256 256 255 33 161"
  ]

------------------------------------------------------------
ringIsoZ ::
     ( Integral n
     , PadicNum n
     , KnownRadix p
     , Digit n ~ Mod p
     , Arbitrary n
     , Show n
     )
  => TestName -> n -> TestTree
ringIsoZ s t = testGroup s 
  [ testProperty "Z <-> Zp" $ homo0 fromInteger toInteger t
  , testProperty "add Z -> Zp" $ homo1 fromInteger (+) (+) t
  , testProperty "add Zp -> Z" $ homo2 fromInteger toInteger (+) (+) t
  , testProperty "mul Z -> Zp" $ homo1 fromInteger (*) (*) t
  , testProperty "mul Zp -> Z" $ homo2 fromInteger toInteger (*) (*) t
  , testProperty "negation Zp" $ invOp fromInteger (+) negate (const True) t
  , testProperty "inversion Zp" $ invOp fromInteger (*) (div 1) isInvertible t
  , ringLaws t
  , testProperty "Division in the ring" $ divMulZ t
  ]

ringIsoZTests = testGroup "Ring isomorphism"
  [ ringIsoZ "Z 2" (0 :: Z 2)
  , ringIsoZ "Z' 2 60" (0 :: Z' 2 60)
  , ringIsoZ "Z 3" (0 :: Z 3)
  , ringIsoZ "Z' 3 60" (0 :: Z' 3 60)
  , ringIsoZ "Z 10" (0 :: Z 10)
  , ringIsoZ "Z' 10 60" (0 :: Z' 10 60)
  , ringIsoZ "Z 65535" (0 :: Z 65535)
  , ringIsoZ "Z' 65535 60" (0 :: Z' 65535 60)
  ]

divMulZ ::
     (Show a, Eq a, Integral a, PadicNum a, KnownRadix p, Digit a ~ Mod p)
  => a -> a -> a -> Property
divMulZ t a b = isInvertible b ==> b * (a `div` b) === a

------------------------------------------------------------
pAdicUnitTests :: TestTree
pAdicUnitTests = testGroup "p-adic units."
  [ testCase "13" $ splitUnit (0 :: Z 2) @?= (0, 20)
  , testCase "14" $ splitUnit (1 :: Z 2) @?= (1, 0)
  , testCase "15" $ splitUnit (100 :: Z 2) @?= (25, 2)
  , testCase "16" $ splitUnit (4 `div` 15 :: Z 2) @?= (1 `div` 15, 2)
  ]

------------------------------------------------------------
testSuite :: TestTree
testSuite = testGroup "Integer Fixed"
  [
    showTests
  , digitsTests 
  , equivTest
  , ringIsoZTests
  , pAdicUnitTests
  ]

main = defaultMain testSuite 
