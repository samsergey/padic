{-# LANGUAGE DataKinds #-}
{-# LANGUAGE UndecidableInstances #-}
{-# language TypeApplications #-}

module ZSpec where

import Test.Hspec
import Test.QuickCheck
import Padic

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

divTest :: Base m => Z m -> Z m -> Z m -> Bool
divTest t a b =
  case a `divMaybe` b of
    Nothing -> True
    Just r -> b * r == a

            
instance Base m => Arbitrary (Z m) where
  arbitrary = fromInteger <$> arbitrary

spec :: Spec
spec = do
  describe "base 2" $ do
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
  describe "base 10" $ do
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
  describe "base 131" $ do
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
