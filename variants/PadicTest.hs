{-# LANGUAGE UndecidableInstances #-}
{-# language TypeApplications #-}
import Test.QuickCheck
import Data.Ratio
import Data.Mod
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
  case a `divZ` b of
    Nothing -> True
    Just r -> b * r == a

             
instance Base m => Arbitrary (Z m) where
  arbitrary = fromInteger <$> arbitrary

testZ = do
  quickCheck (intHomo (0 :: Z 13))
  quickCheck (addHomo (0 :: Z 3))
  quickCheck (mulHomo (0 :: Z 3))
  quickCheck (addComm @(Z 3))
  quickCheck (addAssoc @(Z 3))
  quickCheck (negInvol @(Z 3))
  quickCheck (negInvers @(Z 3))
  quickCheck (negScale @(Z 3))
  quickCheck (mulZero @(Z 3))
  quickCheck (mulOne @(Z 3))
  quickCheck (mulComm @(Z 3))
  quickCheck (mulAssoc @(Z 3))
  quickCheck (mulDistr @(Z 3))
  quickCheck (mulSign @(Z 3))
  quickCheck (divTest (0 :: Z 2))
  quickCheck (divTest (0 :: Z 7))
  quickCheck (divTest (0 :: Z 10))

