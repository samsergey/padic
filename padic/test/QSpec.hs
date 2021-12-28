{-# LANGUAGE DataKinds #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE UndecidableInstances #-}

module QSpec where

import qualified Data.InfList as Inf
import Data.List
import Data.Maybe
import Data.Ratio
import Data.Mod
import PMath.NumberTheory.Padic
import Test.Hspec
import Test.QuickCheck

  
digitsTest :: (Eq n, Padic n) => n -> Property
digitsTest n = valuation n == 0 ==> fromDigits (digits n) == n

showTest = do
  it "0" $ property $ show (0 :: Q 3) == "0.0"
  it "3" $ property $ show (3 :: Q 3) == "10.0"
  it "-3" $ property $ show (-3 :: Q 3) == "(2)0.0"
  it "123" $ property $ show (123 :: Q 10) == "123.0"
  it "123" $ property $ show (123 :: Q 2) == "1111011.0"
  it "-123" $ property $ show (-123 :: Q 10) == "(9)877.0"

equivTest = do
  it "1" $ property $ (0 :: Q' 10 5) == 432100000
  it "2" $ property $ (0 :: Q' 10 5) /= 543210000
  it "3" $ property $ (87654321 :: Q' 10 5) == 87054321
  it "4" $ property $ (87654321 :: Q' 10 5) /= 87604321

addHomo :: (Eq a, Num a) => a -> Integer -> Integer -> Bool
addHomo t a b =
  let [x, y, _] = [fromInteger a, fromInteger b, t]
   in x + y == fromInteger (a + b)

mulHomo :: (Eq a, Num a) => a -> Integer -> Integer -> Bool
mulHomo t a b =
  let [x, y, _] = [fromInteger a, fromInteger b, t]
   in x * y == fromInteger (a * b)
  
divHomo :: (Eq a, Fractional a) => a -> Rational -> Rational -> Property
divHomo t a b =
  let [x, y, _] = [fromRational a, fromRational b, t]
   in b /= 0 ==> x / y == fromRational (a / b)

addComm :: (Eq a, Num a) => a -> a -> Bool
addComm a b = a + b == b + a

addAssoc :: (Eq a, Num a) => a -> a -> a -> Bool
addAssoc a b c = a + (b + c) == (a + b) + c

negInvol :: (Eq a, Num a) => a -> Bool
negInvol a = - (- a) == a

negInvers :: (Eq a, Num a) => a -> Bool
negInvers a = a - a == 0

negScale :: (Eq a, Num a) => a -> Bool
negScale a = (-1) * a == - a

mulZero :: (Eq a, Num a) => a -> Bool
mulZero a = 0 * a == 0

mulOne :: (Eq a, Num a) => a -> Bool
mulOne a = 1 * a == a

mulComm :: (Eq a, Num a) => a -> a -> Bool
mulComm a b = a * b == b * a

mulAssoc :: (Eq a, Num a) => a -> a -> a -> Bool
mulAssoc a b c = a * (b * c) == (a * b) * c

mulDistr :: (Eq a, Num a) => a -> a -> a -> Bool
mulDistr a b c = a * (b + c) == a * b + a * c
  
divDistr :: (Eq a, Fractional a) => a -> a -> a -> Property
divDistr a b c = a /= 0 ==> (b + c) / a == b / a + c / a
  
divMul :: (Eq a, Fractional a) => a -> a -> Property
divMul a b = b /= 0 ==> (a / b) * b == a

mulSign :: (Eq a, Num a) => a -> a -> Bool
mulSign a b = and [a * (- b) == - (a * b), (- a) * (- b) == a * b]

ratRec :: (Real a, Fractional a) => a -> Ratio Word -> Bool
ratRec t r = let [_, x] = [t, fromRational (toRational r)]
             in toRational x == toRational r

plog p b
  | b `mod` p == 0 = 1 + plog p (b `div` p)
  | otherwise = 0

integerQ :: Radix p => Gen (Q p)
integerQ = fromInteger <$> arbitrary

rationalQ :: Radix p => Gen (Q p)
rationalQ = do
  a <- arbitrary
  b <- arbitrary `suchThat` (/= 0)
  return $ fromRational $ a % b

instance Radix m => Arbitrary (Mod m) where
  arbitrary = fromInteger <$> arbitrary

arbitraryQ :: Radix p => Gen (Q p)
arbitraryQ = fromDigits <$> infiniteList

instance Radix m => Arbitrary (Q m) where
  arbitrary = oneof [integerQ, rationalQ, arbitraryQ]

test :: Spec
test = it "ratRec" $ property $ ratRec (0 :: Q 2)

spec :: Spec
spec = do
  describe "show" showTest
  describe "equiv" equivTest
  describe "radix 2" $ do
    it "digitsTest" $ property $ digitsTest @(Q 2)
    it "addHomo" $ property $ addHomo (0 :: Q 2)
    it "mulHomo" $ property $ mulHomo (0 :: Q 2)
    it "divHomo" $ property $ divHomo (0 :: Q 2)
    it "addComm" $ property $ addComm @(Q 2)
    it "addAssoc" $ property $ addAssoc @(Q 2)
    it "negInvol" $ property $ negInvol @(Q 2)
    it "negInvers" $ property $ negInvers @(Q 2)
    it "negScale" $ property $ negScale @(Q 2)
    it "mulZero" $ property $ mulZero @(Q 2)
    it "mulOne" $ property $ mulOne @(Q 2)
    it "mulComm" $ property $ mulComm @(Q 2)
    it "mulAssoc" $ property $ mulAssoc @(Q 2)
    it "mulDistr" $ property $ mulDistr @(Q 2)
    it "mulSign" $ property $ mulSign @(Q 2)
    it "divDistr" $ property $ divDistr @(Q 2)
    it "divMul" $ property $ divMul @(Q 2)

  describe "radix 7" $ do
    it "digitsTest" $ property $ digitsTest @(Q 7)
    it "addHomo" $ property $ addHomo (0 :: Q 7)
    it "mulHomo" $ property $ mulHomo (0 :: Q 7)
    it "divHomo" $ property $ divHomo (0 :: Q 2)
    it "addComm" $ property $ addComm @(Q 7)
    it "addAssoc" $ property $ addAssoc @(Q 7)
    it "negInvol" $ property $ negInvol @(Q 7)
    it "negInvers" $ property $ negInvers @(Q 7)
    it "negScale" $ property $ negScale @(Q 7)
    it "mulZero" $ property $ mulZero @(Q 7)
    it "mulOne" $ property $ mulOne @(Q 7)
    it "mulComm" $ property $ mulComm @(Q 7)
    it "mulAssoc" $ property $ mulAssoc @(Q 7)
    it "mulDistr" $ property $ mulDistr @(Q 7)
    it "mulSign" $ property $ mulSign @(Q 7)
    it "divDistr" $ property $ divDistr @(Q 7)
    it "divMul" $ property $ divMul @(Q 7)


  describe "radix 131" $ do
    it "digitsTest" $ property $ digitsTest @(Q 131)
    it "addHomo" $ property $ addHomo (0 :: Q 131)
    it "mulHomo" $ property $ mulHomo (0 :: Q 131)
    it "divHomo" $ property $ divHomo (0 :: Q 2)
    it "addComm" $ property $ addComm @(Q 131)
    it "addAssoc" $ property $ addAssoc @(Q 131)
    it "negInvol" $ property $ negInvol @(Q 131)
    it "negInvers" $ property $ negInvers @(Q 131)
    it "negScale" $ property $ negScale @(Q 131)
    it "mulZero" $ property $ mulZero @(Q 131)
    it "mulOne" $ property $ mulOne @(Q 131)
    it "mulComm" $ property $ mulComm @(Q 131)
    it "mulAssoc" $ property $ mulAssoc @(Q 131)
    it "mulDistr" $ property $ mulDistr @(Q 131)
    it "mulSign" $ property $ mulSign @(Q 131)
    it "divDistr" $ property $ divDistr @(Q 131)
    it "divMul" $ property $ divMul @(Q 131)

