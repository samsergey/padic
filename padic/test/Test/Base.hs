{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}

module Test.Base where

import qualified Math.NumberTheory.Padic.Fixed.Rational
import qualified Math.NumberTheory.Padic.Fixed.Integer
import qualified Math.NumberTheory.Padic.Rational
import qualified Math.NumberTheory.Padic.Integer
import Math.NumberTheory.Padic.Classes

import GHC.TypeLits hiding (Mod)
import Test.Tasty
import Test.Tasty.HUnit
import Test.Tasty.QuickCheck
import Test.Tasty.ExpectedFailure
import Test.QuickCheck
import Data.Mod
import Data.Word
import Data.Ratio
import Data.Maybe

instance KnownRadix m => Arbitrary (Mod m) where
  arbitrary = fromInteger <$> arbitrary

instance Radix p prec => Arbitrary (Math.NumberTheory.Padic.Integer.Z' p prec) where
  arbitrary = oneof [integerZ, rationalZ, arbitraryZ]
    where
      integerZ = fromInteger <$> arbitrary
      arbitraryZ = fromDigits . take 20 <$> infiniteList
      rationalZ = do
        a <- integerZ
        b <- suchThat integerZ isInvertible
        return $ a `div` b
      shrink _ = []


instance Radix p prec => Arbitrary (Math.NumberTheory.Padic.Fixed.Integer.Z' p prec) where
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
    let m = fromIntegral (maxBound :: Word32)
    n <- chooseInteger (-m, m)
    d <- chooseInteger (1,m)
    return $ SmallRational (n % d)
  shrink (SmallRational r) = SmallRational <$> []
 
instance Radix p prec => Arbitrary (Math.NumberTheory.Padic.Rational.Q' p prec) where
  arbitrary = oneof [integerQ, rationalQ, arbitraryQ]
    where
      integerQ = fromInteger <$> arbitrary
      arbitraryQ = fromDigits . take 20 <$> infiniteList
      rationalQ = do
        SmallRational r <- arbitrary
        return $ fromRational r
  shrink _ = []

instance Radix p prec => Arbitrary (Math.NumberTheory.Padic.Fixed.Rational.Q' p prec) where
  arbitrary = oneof [integerQ, rationalQ, arbitraryQ]
    where
      integerQ = fromInteger <$> arbitrary
      arbitraryQ = fromDigits . take 20 <$> infiniteList
      rationalQ = do
        SmallRational r <- arbitrary
        return $ fromRational r
  shrink _ = []

a @/= b = assertBool "" (a /= b)

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
