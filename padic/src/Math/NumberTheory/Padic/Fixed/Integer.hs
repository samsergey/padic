{-# OPTIONS_HADDOCK hide, prune, ignore-exports #-}

{-# LANGUAGE DerivingVia #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE UnboxedTuples #-}
{-# LANGUAGE UnliftedFFITypes #-}
{-# LANGUAGE NoStarIsType #-}

module Math.NumberTheory.Padic.Fixed.Integer where

import Data.List
import Data.Mod
import Data.Ratio
import GHC.TypeLits hiding (Mod)
import GHC.Integer.GMP.Internals (recipModInteger)
import Data.Constraint (Constraint)

import Math.NumberTheory.Padic.Classes

------------------------------------------------------------
type family Lifted p prec where
  Lifted p prec = p ^ (2*prec + 1)

type family LiftedRadix p prec :: Constraint where
  LiftedRadix p prec =
    ( KnownNat prec
    , KnownNat p
    , ValidRadix p
    , KnownNat (p ^ (2*prec + 1))
    , ValidRadix (p ^ (2*prec + 1))
    )

-- |  Integer p-adic number (an element of \(\mathbb{Z}_p\)) with 20 digits precision.
type Z p = Z' p 20

-- |  Integer p-adic number with explicitly specified precision.
newtype Z' (p :: Nat) (prec :: Nat) = Z' (Z_ prec p)

deriving via Z_ prec p instance (LiftedRadix p prec) => Num (Z' p prec)

newtype Z_ (prec :: Nat ) (p :: Nat) = Z_ (Mod (Lifted p prec))

deriving via Mod (Lifted p prec) instance (LiftedRadix p prec) => Num (Z_ prec p)

instance LiftedRadix p prec => Eq (Z' p prec) where
  x@(Z' (Z_ a)) == Z' (Z_ b) = unMod a `mod` pk == unMod b `mod` pk
    where
      pk = radix x ^ precision x

instance LiftedRadix p prec => Show (Z' p prec) where
  show 0 = "0"
  show n  
    | length ds > pr = ell ++ toString (take pr ds)
    | otherwise = toString (take pr ds)
    where
      ds = digits n
      pr = precision n
      toString = intercalate sep . map showD . reverse
      showD = show . unMod 
      ell = "…" ++ sep 
      sep
        | radix n < 11 = ""
        | otherwise = " "

instance LiftedRadix p prec => Padic (Z' p prec) where
  type Unit (Z' p prec) = Z' p prec
  type LiftedDigits (Z' p prec) = Integer
  type Digit (Z' p prec) = Mod p 

  {-# INLINE precision #-}
  precision = fromIntegral . natVal

  {-# INLINE  radix #-}
  radix (Z' n) = fromIntegral $ natVal n
  
  {-# INLINE fromDigits #-}
  fromDigits = mkUnit . fromRadix

  {-# INLINE digits #-}
  digits n = toRadix (lifted n)

  {-# INLINE lifted #-}
  lifted (Z' (Z_ n)) = lifted n

  {-# INLINE mkUnit #-}
  mkUnit = Z' . Z_ . fromInteger

  {-# INLINE fromUnit #-}
  fromUnit (u, v) = mkUnit $ radix u ^ fromIntegral v * lifted u

  splitUnit n = case getUnitZ (radix n) (lifted n) of
                  (0, 0) -> (0, precision n)
                  (u, v) -> (mkUnit u, v)
  
  isInvertible n = (lifted n `mod` p) `gcd` p == 1
    where
      p = radix n
  
  inverse (Z' (Z_ n))  = Z' . Z_ <$> invertMod n

instance LiftedRadix p prec  => Enum (Z' p prec) where
  toEnum = fromIntegral
  fromEnum = fromIntegral . toInteger

instance LiftedRadix p prec => Real (Z' p prec) where
  toRational 0 = 0
  toRational n = extEuclid (lifted n, liftedRadix n)

instance LiftedRadix p prec => Integral (Z' p prec) where
  toInteger n = if denominator r == 1
                then numerator r
                else lifted n `mod` (radix n ^ precision n)
    where
      r = toRational n
  a `quotRem` b = case inverse b of
    Nothing -> error "not divisible!" 
    Just r -> let q = a*r in (q, a - q * b)


instance LiftedRadix p prec => Ord (Z' p prec) where
  compare = error "ordering is not defined for Z"

