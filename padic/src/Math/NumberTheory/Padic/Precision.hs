{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE DerivingVia #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE UndecidableInstances #-}
{-# OPTIONS_HADDOCK hide, prune, ignore-exports #-}


module Math.NumberTheory.Padic.Precision where

import GHC.TypeLits
import Math.NumberTheory.Padic.Classes
import Math.NumberTheory.Padic.Integer

newtype a % (prec :: Nat) = Prec a

instance (KnownNat prec, Fixed a) => Fixed (a % prec) where
  precision = fromIntegral . natVal
  showPrec pr (Prec a) = showPrec pr a
  eqPrec pr (Prec a) (Prec b) = eqPrec pr a b

instance Digital a => Digital (a % prec) where
  type Digits (a % prec) = Digits a
  type LiftedDigits (a % prec) = LiftedDigits a
  radix (Prec x) = radix x
  digits (Prec x) = digits x
  fromDigits ds = Prec $ fromDigits ds
  liftedDigits (Prec x) = liftedDigits x
  mkUnit ds = Prec $ mkUnit ds

instance (KnownNat prec, Padic a, Eq a, Num (Unit a)) => Padic (a % prec) where
  type Unit (a % prec) = Unit a % prec
  fromUnit (Prec u, v) = Prec $ fromUnit (u, v)
  splitUnit x@(Prec 0) = (Prec 0, precision x) 
  splitUnit (Prec a) = (Prec $ unit a, valuation a) 
  inverse (Prec a) = Prec <$> inverse a

instance (KnownNat prec, Fixed a) => Show (a % prec) where
  show p@(Prec a) = showPrec (precision p) a

instance (Padic a, KnownNat prec, Num a) => Num (a % prec) where
  fromInteger n = res
    where
      (_, v) = getUnitZ p n
      res | v >= pr = 0
          | otherwise = Prec $ fromInteger n
      pr = precision res
      p = radix res
      
  Prec a + Prec b = Prec (a + b)
  Prec a * Prec b = Prec (a * b)
  Prec a - Prec b = Prec (a - b)
  negate (Prec a) = Prec (negate a)
  abs (Prec a) = Prec (abs a)
  signum (Prec a) = Prec (signum a)

instance (KnownNat prec, Fixed a) => Eq (a % prec) where
  p@(Prec a) == Prec b = eqPrec (precision p) a b
  
instance (KnownNat prec, Fixed a, Ord a) => Ord (a % prec) where
  compare (Prec a) (Prec b) = a `compare` b 
  
instance (KnownNat prec, Enum a) => Enum (a % prec) where
  toEnum = Prec . toEnum
  fromEnum (Prec a) = fromEnum a

instance (KnownNat prec, RealPadic a p) => Real (a % prec) where
  toRational x@(Prec a) = ratDecomposition (precision x) a

instance (KnownNat prec, Integral a, RealPadic a p) => Integral (a % prec) where
  toInteger (Prec a) = toInteger a
  quotRem (Prec a) (Prec b) = let (q, r) = quotRem a b
                              in (Prec q, Prec r)

instance (KnownNat prec, Fractional a, Padic a) => Fractional (a % prec) where
  fromRational = Prec . fromRational
  recip (Prec a) = Prec (recip a)
  Prec a / Prec b = Prec (a / b)

