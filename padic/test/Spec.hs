{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE TypeSynonymInstances #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}

module Main where

import Math.NumberTheory.Padic
import Math.NumberTheory.Padic.Classes
import Math.NumberTheory.Padic.Rational
import GHC.TypeLits hiding (Mod)
import GHC.Prim (coerce)
import Test.Tasty
import Test.Tasty.HUnit
import Test.Tasty.QuickCheck
import Test.Tasty.ExpectedFailure
import Test.QuickCheck
import Data.Mod
import Data.Maybe
import Data.Ratio
import Data.Word

instance Radix m => Arbitrary (Mod m) where
  arbitrary = fromInteger <$> arbitrary

instance (KnownNat prec, Radix m) => Arbitrary (Z' m prec) where
  arbitrary = oneof [integerZ, rationalZ, arbitraryZ]
    where
      integerZ = fromInteger <$> arbitrary
      arbitraryZ = fromDigits . take 20 <$> infiniteList
      rationalZ = do
        a <- integerZ
        b <- suchThat integerZ isInvertible
        return $ a `div` b
      shrink _ = []

newtype SmallRational = SmallRational (Rational)
  deriving (Show, Eq, Num, Fractional)

instance Arbitrary SmallRational where
  arbitrary = do
    n <- chooseInteger (-65535,65535)
    d <- chooseInteger (1,65535)
    return $ SmallRational (n % d)
  shrink (SmallRational r) = SmallRational <$> []
  
instance (KnownNat prec, Radix m) => Arbitrary (Q' m prec) where
  arbitrary = oneof [integerQ, rationalQ, arbitraryQ]
    where
      integerQ = fromInteger <$> arbitrary
      arbitraryQ = fromDigits . take 20 <$> infiniteList
      rationalQ = do
        SmallRational r <- arbitrary
        return $ fromRational r
  shrink _ = []

a @/= b = assertBool "" (a /= b)

------------------------------------------------------------
digitsTestZ :: Radix p => Z p -> Property
digitsTestZ n = fromDigits (digits n) === n

digitsTestQ :: Radix p => Q p -> Property
digitsTestQ n = valuation n == 0 ==> fromDigits (digits n) === n

digitsTests = testGroup "Conversion to and from digits"
  [ testProperty "Z 2" $ digitsTestZ @2
  , testProperty "Z 10" $ digitsTestZ @10
  , testProperty "Z 257" $ digitsTestZ @257
  , testProperty "Q 2" $ digitsTestQ @2
  , testProperty "Q 13" $ digitsTestQ @13
  , testProperty "Q 257" $ digitsTestQ @257
  , testCase "1" $ firstDigit (1 :: Q 3) @?= 1
  , testCase "-1" $ firstDigit (-1 :: Q 3) @?= 2
  , testCase "2" $ firstDigit (0 :: Q 3) @?= 0
  , testCase "3" $ firstDigit (9 :: Q 3) @?= 0
  , testCase "4" $ firstDigit (9 :: Q 10) @?= 9
  ]
  
------------------------------------------------------------
equivTest :: TestTree
equivTest = testGroup "Equivalence tests"
  [ testCase "1" $ (0 :: Z' 10 5) @?= 432100000
  , testCase "2" $ (0 :: Z' 10 5) @/= 543210000
  , testCase "3" $ (87654321 :: Z' 10 5) @?= 87054321
  , testCase "4" $ (87654321 :: Z' 10 5) @/= 87604321
  , testCase "5" $ (432100000 :: Q' 10 5) @?= 0
  , testCase "6" $ (0 :: Q' 10 5) @/= 543210000
  , testCase "7" $ (1/7 :: Q' 10 5) @?= 57143
  , testCase "8" $ (1/7 :: Q' 10 5) @?= 657143
  , testCase "9" $ (1/7 :: Q' 10 5) @/= 67143
  ]

------------------------------------------------------------
{-
cycleTest :: TestTree
cycleTest = testGroup "findCycle tests"
  [ testCase "1" $ findCycle 10 [1..5] @?= Nothing
  , testCase "2" $ findCycle 10 [1] @?= Nothing
  , testCase "3" $ findCycle 10 (repeat 1) @?= Just ([],[1])
  , testCase "4" $ findCycle 10 ([1..5] ++ repeat 1) @?= Just ([1..5],[1])
  , testCase "5" $ findCycle 10 ([1..15] ++ repeat 1) @?= Nothing
  , testCase "6" $ findCycle 10 ([1,1,1] ++ repeat 1) @?= Just ([],[1])
  , testCase "7" $ findCycle 10 ([2,1,1] ++ repeat 1) @?= Just ([2],[1])
  , testCase "8" $ findCycle 10 ([1,2,3] ++ cycle [1,2,3]) @?= Just ([],[1,2,3])
  , testCase "9" $ findCycle 10 ([2,3] ++ cycle [1,2,3]) @?= Just ([],[2,3,1])
  , testCase "10" $ findCycle 10 ([0,1,2,3] ++ cycle [1,2,3]) @?= Just ([0],[1,2,3])
  , testCase "11" $ findCycle 10 ([0,2,3] ++ cycle [1,2,3]) @?= Just ([0],[2,3,1])
  , testCase "12" $ findCycle 200 ([1..99] ++ cycle [100..200]) @?= Just ([1..99],[100..200])
  ]
-}
------------------------------------------------------------

------------------------------------------------------------
showTests = testGroup "String representation"
  [ showTestZ, showTestQ ]
  
showTestZ = testGroup "Z"
  [ testCase "0" $ show (0 :: Z 3) @?= "0"
  , testCase "3" $ show (3 :: Z 3) @?= "10"
  , testCase "-3" $ show (-3 :: Z 3) @?= "…22222222222222222220"
  , testCase "123" $ show (123 :: Z 10) @?= "123"
  , testCase "123" $ show (123 :: Z 2) @?= "1111011"
  , testCase "123456789" $ show (123456789 :: Z' 10 5) @?= "…56789"
  , testCase "-123" $ show (-123 :: Z 10) @?= "…99999999999999999877"
  , testCase "1/23" $ show (1 `div` 23 :: Z 10) @?= "…65217391304347826087"
  , testCase "1/23" $ show (1 `div` 23 :: Z' 17 5) @?= "… 8 14 13 5 3"
  , testCase "123456" $ show (123456 :: Z 257) @?= "1 223 96"
  , testCase "123456" $ show (-123456 :: Z' 257 6) @?= "… 256 256 256 255 33 161"
  ]

showTestQ = testGroup "Q"
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
  , testCase "123456" $ show (123456 :: Q 257) @?= "1 223 96 . 0"
  , testCase "123456" $ show (-123456 :: Q' 257 6) @?= "… 256 256 256 255 33 161 . 0"
  ]

------------------------------------------------------------

homo0 :: (Show a, Eq a) => (a -> t) -> (t -> a) -> t -> a -> Property
homo0 phi psi w a =
  let [x, _] = [phi a, w] in psi x === a

homo1 :: (Show t , Eq t) => (a -> t)
      -> (a -> a -> a)
      -> (t -> t -> t)
      -> t -> a -> a -> Property
homo1 phi opa opt w a b =
  let [x, y, _] = [phi a, phi b, w]
  in x `opt` y === phi (a `opa` b)

homo2 :: (Show a, Eq a) => (a -> t) -> (t -> a)
      -> (a -> a -> a)
      -> (t -> t -> t)
      -> t -> a -> a -> Property
homo2 phi psi opa opt w a b =
  let [x, y, _] = [phi a, phi b, w]
  in psi (x `opt` y) === a `opa` b

invOp :: (Show t, Eq t) => (a -> t) 
      -> (t -> t -> t) 
      -> (t -> t)
      -> (t -> Bool)
      -> t -> a -> a -> Property
invOp phi op inv p w a b =
  let [x, y, _] = [phi a, phi b, w]
  in p y ==> (x `op` y) `op` inv y === x 
  

ringIsoZ ::
     ( Integral n
     , Padic n
     , Radix p
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

ringIsoQ ::
     ( ValidRadix m
     , Fractional n
     , Real n
     , KnownNat m
     , Padic n
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
  [ ringIsoQ "Q' 2 33" (0 :: Q' 2 34)
  , ringIsoQ "Q' 3 21" (0 :: Q' 3 21)
  , ringIsoQ "Q' 257 5" (0 :: Q' 257 5)
  ]

test = ringIsoQ "Q' 2 34" (0 :: Q' 2 34)
------------------------------------------------------------
newtype AnyRadix = AnyRadix Int
  deriving (Show, Eq, Num)
  
instance Arbitrary AnyRadix where
  arbitrary = AnyRadix <$> arbitrary `suchThat` (> 1)
  
pAdicUnitTests :: TestTree
pAdicUnitTests = testGroup "p-adic units."
  [ testCase "2" $ getUnitQ 2 (4%7) @?= (1 % 7, 2)
  , testCase "7" $ getUnitQ 7 (4%7) @?= (4 % 1, -1)
  , testProperty "0" $ \(AnyRadix p) -> getUnitQ @Int p 0 === (0, 0)
  , testProperty "1" $ \(AnyRadix p) -> getUnitQ @Int p 1 === (1, 0)
  , testProperty "p" $
      \(AnyRadix p) r -> let (u, k) = getUnitQ @Int p r
                         in r === fromIntegral p^^k * u
  , testCase "8" $ splitUnit (0 :: Q' 2 13) @?= (0, 13)
  , testCase "9" $ splitUnit (1 :: Q 2) @?= (1, 0)
  , testCase "10" $ splitUnit (100 :: Q 2) @?= (25, 2)
  , testCase "11" $ splitUnit (1/96 :: Q 2) @?= (1 `div` 3, -5)
  , testCase "12" $ splitUnit (-1/96 :: Q 2) @?= (-1 `div` 3, -5)
  , testCase "13" $ splitUnit (0 :: Z 2) @?= (0, 20)
  , testCase "14" $ splitUnit (1 :: Z 2) @?= (1, 0)
  , testCase "15" $ splitUnit (100 :: Z 2) @?= (25, 2)
  , testCase "16" $ splitUnit (4 `div` 15 :: Z 2) @?= (1 `div` 15, 2)
  ]

------------------------------------------------------------
{-
toRadixTests = testGroup "Conversion to and from digits" $
  [ testProperty "num -> dig -> num" $
    \(AnyRadix p) (Positive n) -> fromRadix p (toRadix p n) === n
  , testProperty "dig -> num -> dig" $
    \(AnyRadix p) (Positive n) -> let ds = toRadix p n
                                  in toRadix p (fromRadix p ds) === ds ]-}
------------------------------------------------------------

addComm :: (Show a, Eq a, Num a) => a -> a -> a -> Bool
addComm t a b = a + b == b + a

addAssoc :: (Show a, Eq a, Num a) => a -> a -> a -> a -> Bool
addAssoc t a b c = a + (b + c) == (a + b) + c

negInvol :: (Show a, Eq a, Num a) => a -> a -> Bool
negInvol t a = - (- a) == a

negInvers :: (Eq a, Num a) => a -> a -> Bool
negInvers t a = a - a == 0

negScale :: (Eq a, Num a) => a -> a -> Bool
negScale t a = (-1) * a == - a

mulZero :: (Eq a, Num a) => a -> a -> Bool
mulZero t a = 0 * a == 0

mulOne :: (Eq a, Num a) => a -> a -> Bool
mulOne t a = 1 * a == a

mulComm :: (Eq a, Num a) => a -> a -> a -> Bool
mulComm t a b = a * b == b * a

mulAssoc :: (Eq a, Num a) => a -> a -> a -> a -> Bool
mulAssoc t a b c = a * (b * c) == (a * b) * c

mulDistr :: (Eq a, Num a) => a -> a -> a -> a -> Bool
mulDistr t a b c = a * (b + c) == a * b + a * c
  
divDistr :: (Eq a, Fractional a) => a -> a -> a -> a -> Property
divDistr t a b c = a /= 0 ==> (b + c) / a == b / a + c / a
  
divMul :: (Eq a, Fractional a) => a -> a -> a -> Property
divMul t a b = b /= 0 ==> (a / b) * b == a

mulSign :: (Eq a, Num a) => a -> a -> a -> Bool
mulSign t a b = and [a * (- b) == - (a * b), (- a) * (- b) == a * b]

ringLaws t = testGroup "Ring laws" $
  [ testProperty "Addition commutativity" $ addComm t
  , testProperty "Addition associativity" $ addAssoc t
  , testProperty "Negation involution" $ negInvol t
  , testProperty "Addition inverse" $ negInvers t
  , testProperty "Negative scaling" $ negScale t
  , testProperty "Multiplicative zero" $ mulZero t
  , testProperty "Multiplicative one" $ mulOne t
  , testProperty "Multiplication commutativity" $ mulComm t
  , testProperty "Multiplication associativity" $ mulAssoc t
  , testProperty "Multiplication distributivity" $ mulDistr t
  , testProperty "Multiplication signs" $ mulSign t
  ]

divMulZ ::
     (Show a, Eq a, Num a, Integral a, Padic a, Radix p, Digit a ~ Mod p)
  => a -> a -> a -> Property
divMulZ t a b = isInvertible b ==> b * (a `div` b) === a


------------------------------------------------------------
testSuite :: TestTree
testSuite = testGroup "test"
  [
    showTests
  , digitsTests 
  , equivTest
  , ringIsoZTests
  , ringIsoQTests
  , pAdicUnitTests
  ]

main = defaultMain testSuite 
