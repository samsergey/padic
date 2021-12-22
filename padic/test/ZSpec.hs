{-# LANGUAGE DataKinds #-}
{-# LANGUAGE UndecidableInstances #-}
{-# language TypeApplications #-}
{-# language GeneralizedNewtypeDeriving #-}

module ZSpec where

import Test.Hspec
import Test.QuickCheck
import Padic
import Data.List
import qualified Data.InfList as Inf
import Data.Mod
import Data.Maybe

intHomo :: Integral a => a -> Integer -> Bool
intHomo t a = let [x,_] = [fromInteger a,t]
              in toInteger x == a

addHomo :: (Eq a, Num a) => a -> Integer -> Integer -> Bool
addHomo t a b = let [x,y,_] = [fromInteger a, fromInteger b, t]
                in x + y == fromInteger (a + b)
                   
mulHomo :: (Eq a, Num a) => a -> Integer -> Integer -> Bool
mulHomo t a b = let [x,y,_] = [fromInteger a, fromInteger b, t]
                in x * y == fromInteger (a * b)

addComm :: (Eq a, Num a) => a -> a -> Bool
addComm a b = a + b == b + a

addAssoc :: (Eq a, Num a) => a -> a -> a -> Bool
addAssoc a b c = a + (b + c) == (a + b) + c

negInvol ::  (Eq a, Num a) => a -> Bool
negInvol a = - (- a) == a

negInvers :: (Eq a, Num a) => a -> Bool
negInvers a = a - a == 0

negScale :: (Eq a, Num a) => a -> Bool
negScale a = (-1) * a == -a

mulZero :: (Eq a, Num a) => a -> Bool
mulZero a = 0 * a == 0  

mulOne :: (Eq a, Num a) => a -> Bool
mulOne a = 1 * a == a  

mulComm :: (Eq a, Num a) => a -> a -> Bool
mulComm a b = a * b == b * a

mulAssoc :: (Eq a, Num a) => a -> a -> a -> Bool
mulAssoc a b c = a * (b * c) == (a * b) * c

mulDistr :: (Eq a, Num a) => a -> a -> a -> Bool
mulDistr a b c = a * (b + c) == a*b + a*c

mulSign :: (Eq a, Num a) => a -> a -> Bool
mulSign a b = and [ a * (-b) == - (a * b)
                  , (- a) * (-b) == a * b ]

divTest :: Radix m => Z m -> Z m -> Z m -> Bool
divTest t a b =
  case a `divMaybe` b of
    Nothing -> True
    Just r -> b * r == a

splitUnitTest :: Radix p => Z p -> Integer -> Bool
splitUnitTest t a =
  let [_, x] = [t, fromInteger a]
      b = base x
      v' = plog b (abs a)
      u' = abs a `div` (b^v')
      (u, v) = splitUnit x
  in if a == 0
     then u == 0 && v == maxBound
     else u == fromInteger (signum a * u') && v == v'


instance Radix m => Arbitrary (Mod m) where
  arbitrary = fromInteger <$> arbitrary

integerZ :: Radix p => Gen (Z p)
integerZ = fromInteger <$> arbitrary

arbitraryZ :: Radix p => Gen (Z p)
arbitraryZ = fromDigits . Inf.fromList <$> infiniteList

rationalZ :: Radix p => Gen (Z p)
rationalZ = do
  a <- integerZ
  b <- suchThat integerZ (isJust . divMaybe a)
  return $ a `div` b

instance Radix m => Arbitrary (Z m) where
  arbitrary = oneof [integerZ, rationalZ, arbitraryZ]

spec :: Spec
spec = do
  describe "base 2" $ do
    it "intHomo"   $ property $ intHomo  (0 :: Z 2)
    it "addHomo"   $ property $ addHomo  (0 :: Z 2)
    it "mulHomo"   $ property $ mulHomo  (0 :: Z 2)
    it "addComm"   $ property $ addComm   @(Z 2)
    it "addAssoc"  $ property $ addAssoc  @(Z 2)
    it "negInvol"  $ property $ negInvol  @(Z 2)
    it "negInvers" $ property $ negInvers @(Z 2)
    it "negScale"  $ property $ negScale  @(Z 2)
    it "mulZero"   $ property $ mulZero   @(Z 2)
    it "mulOne"    $ property $ mulOne    @(Z 2)
    it "mulComm"   $ property $ mulComm   @(Z 2)
    it "mulAssoc"  $ property $ mulAssoc  @(Z 2)
    it "mulDistr"  $ property $ mulDistr  @(Z 2)
    it "mulSign"   $ property $ mulSign   @(Z 2)
    it "splitUnit" $ property $ splitUnitTest (0 :: Z 2)

  describe "base 10" $ do
    it "intHomo"   $ property $ intHomo  (0 :: Z 10)
    it "addHomo"   $ property $ addHomo  (0 :: Z 10)
    it "mulHomo"   $ property $ mulHomo  (0 :: Z 10)
    it "addComm"   $ property $ addComm   @(Z 10)
    it "addAssoc"  $ property $ addAssoc  @(Z 10)
    it "negInvol"  $ property $ negInvol  @(Z 10)
    it "negInvers" $ property $ negInvers @(Z 10)
    it "negScale"  $ property $ negScale  @(Z 10)
    it "mulZero"   $ property $ mulZero   @(Z 10)
    it "mulOne"    $ property $ mulOne    @(Z 10)
    it "mulComm"   $ property $ mulComm   @(Z 10)
    it "mulAssoc"  $ property $ mulAssoc  @(Z 10)
    it "mulDistr"  $ property $ mulDistr  @(Z 10)
    it "mulSign"   $ property $ mulSign   @(Z 10)
    it "splitUnit" $ property $ splitUnitTest (0 :: Z 10)
      
  describe "base 131" $ do
    it "intHomo"   $ property $ intHomo  (0 :: Z 131)    
    it "addHomo"   $ property $ addHomo  (0 :: Z 131)
    it "mulHomo"   $ property $ mulHomo  (0 :: Z 131)
    it "addComm"   $ property $ addComm   @(Z 131)
    it "addAssoc"  $ property $ addAssoc  @(Z 131)
    it "negInvol"  $ property $ negInvol  @(Z 131)
    it "negInvers" $ property $ negInvers @(Z 131)
    it "negScale"  $ property $ negScale  @(Z 131)
    it "mulZero"   $ property $ mulZero   @(Z 131)
    it "mulOne"    $ property $ mulOne    @(Z 131)
    it "mulComm"   $ property $ mulComm   @(Z 131)
    it "mulAssoc"  $ property $ mulAssoc  @(Z 131)
    it "mulDistr"  $ property $ mulDistr  @(Z 131)
    it "mulSign"   $ property $ mulSign   @(Z 131)
    it "splitUnit" $ property $ splitUnitTest (0 :: Z 131)
