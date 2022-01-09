{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}

module Test.FixedRational (testSuite) where


import Math.NumberTheory.Padic.Fixed
import Test.Base
import GHC.TypeLits hiding (Mod)
import Test.Tasty
import Test.Tasty.HUnit
import Test.Tasty.QuickCheck
import Test.Tasty.ExpectedFailure
import Test.QuickCheck
import Data.Mod
import Data.Ratio


------------------------------------------------------------
digitsTestQ :: (Show n, Eq n, PadicNum n) => n -> n -> Property
digitsTestQ t n = valuation n == 0 ==> fromDigits (digits n) === n

digitsTests = testGroup "Conversion to and from digits"
  [ testProperty "Q 2" $ digitsTestQ (0 :: Q 2)
  , testProperty "Q 13" $ digitsTestQ (0 :: Q 13)
  , testProperty "Q 257" $ digitsTestQ (0 :: Q 257)
  , testCase "1" $ firstDigit (1 :: Q 3) @?= 1
  , testCase "-1" $ firstDigit (-1 :: Q 3) @?= 2
  , testCase "2" $ firstDigit (0 :: Q 3) @?= 0
  , testCase "3" $ firstDigit (9 :: Q 3) @?= 0
  , testCase "4" $ firstDigit (9 :: Q 10) @?= 9
  ]
  
------------------------------------------------------------
equivTest :: TestTree
equivTest = testGroup "Equivalence tests"
  [ testCase "5" $ (432100000 :: Q' 10 5) @?= 0
  , testCase "6" $ (0 :: Q' 10 5) @/= 543210000
  , testCase "7" $ (1/7 :: Q' 10 5) @?= 57143
  , testCase "8" $ (1/7 :: Q' 10 5) @?= 657143
  , testCase "9" $ (1/7 :: Q' 10 5) @/= 67143
  ]

------------------------------------------------------------
showTests = testGroup "String representation"
  [ testCase "0" $ show (0 :: Q 3) @?= "0.0"
  , testCase "3" $ show (3 :: Q 3) @?= "10.0"
  , testCase "-3" $ show (-3 :: Q 3) @?= "…22222222222222222220.0"
  , testCase "123" $ show (123 :: Q 10) @?= "123.0"
  , testCase "123" $ show (123 :: Q 2) @?= "1111011.0"
  , testCase "-123" $ show (-123 :: Q 10) @?= "…99999999999999999877.0"
  , testCase "1/2" $ show (1/2 :: Q 2) @?= "0.1"
  , testCase "-1/2" $ show (-1/2 :: Q 2) @?= "…11111111111111111111.1"
  , testCase "1/15" $ show (1/15 :: Q 3) @?= "…12101210121012101210.2"
  , testCase "1/700" $ show (1/700 :: Q 10) @?= "…71428571428571428571.43"
  , testCase "100/7" $ show (100/7 :: Q 10) @?= "…85714285714285714300.0"
  , testCase "1/23" $ show (1/23 :: Q 10) @?= "…65217391304347826087.0"
  , testCase "1/23" $ show (1/23 :: Q' 17 5) @?= "… 8 14 13 5 3 . 0"
  , testCase "123456" $ show (123456 :: Q' 257 4) @?= "1 223 96 . 0"
  , testCase "123456" $ show (-123456 :: Q' 257 6) @?= "… 256 256 256 255 33 161 . 0"
  ]

ringIsoQ ::
     ( KnownRadix m
     , Fractional n
     , Real n
     , PadicNum n
     , Digit n ~ Mod m
     , Arbitrary n
     , Show n
     )
  => TestName -> n -> TestTree
ringIsoQ s t = testGroup s 
  [ testProperty "Q <-> Qp" $ homo0 phi psi t
  , testProperty "add Q -> Qp" $ homo1 phi (+) (+) t
  , testProperty "add Qp -> Q" $ homo2 phi psi (+) (+) t
  , testProperty "mul Q -> Qp" $ homo1 phi (*) (*) t
  , testProperty "mul Qp -> Q" $ homo2 phi psi (*) (*) t
  , testProperty "negation Qp" $ invOp phi (+) negate (const True) t
  , testProperty "inversion Qp" $ invOp phi (*) (1 /) isInvertible t
  , ringLaws t
  ]

phi :: (Fractional n, Real n) => SmallRational -> n
phi (SmallRational r) = fromRational r
psi :: (Fractional n, Real n) => n -> SmallRational
psi = SmallRational . toRational 

ringIsoQTests = testGroup "Ring isomorphism"
  [ ringIsoQ "Q 2" (0 :: Q' 2 68)
  , ringIsoQ "Q 3" (0 :: Q' 3 45)
  , ringIsoQ "Q 5" (0 :: Q' 5 29)
  , ringIsoQ "Q 7" (0 :: Q' 7 26)
  , ringIsoQ "Q 13" (0 :: Q 13)
  , ringIsoQ "Q 257" (0 :: Q 257)
  ]

------------------------------------------------------------
 
pAdicUnitTests :: TestTree
pAdicUnitTests = testGroup "p-adic units."
  [ testCase "8" $ splitUnit (0 :: Q' 2 13) @?= (0, 13)
  , testCase "9" $ splitUnit (1 :: Q 2) @?= (1, 0)
  , testCase "10" $ splitUnit (100 :: Q 2) @?= (25, 2)
  , testCase "11" $ splitUnit (1/96 :: Q 2) @?= (1 `div` 3, -5)
  , testCase "12" $ splitUnit (-1/96 :: Q 2) @?= (-1 `div` 3, -5)
  ]


------------------------------------------------------------
testSuite :: TestTree
testSuite = testGroup "Ratonal Fixed"
  [
    showTests
  , digitsTests 
  , equivTest
  , ringIsoQTests
  , pAdicUnitTests
  ]

test = defaultMain testSuite 
