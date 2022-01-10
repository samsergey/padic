{-# OPTIONS_HADDOCK hide, prune, ignore-exports #-}

{-# LANGUAGE DerivingVia #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE FlexibleInstances #-}

module Math.NumberTheory.Padic.Integer  where

import Data.List (intercalate)
import Data.Mod
import Data.Word
import Data.Ratio
import GHC.TypeLits (Nat, natVal)
import GHC.Integer.GMP.Internals (recipModInteger)
import Math.NumberTheory.Padic.Types

------------------------------------------------------------

type instance Padic Integer p = Z' p (SufficientPrecision Word p)
type instance Padic Int p = Z' p (SufficientPrecision Int p)
type instance Padic Word8 p = Z' p (SufficientPrecision Word8 p)
type instance Padic Word16 p = Z' p (SufficientPrecision Word16 p)
type instance Padic Word32 p = Z' p (SufficientPrecision Word32 p)
type instance Padic Word64 p = Z' p (SufficientPrecision Word64 p)
type instance Padic Word p = Z' p (SufficientPrecision Word64 p)


-- |  Integer p-adic number (an element of \(\mathbb{Z}_p\)) with default precision.
type Z p = Z' p (SufficientPrecision Word32 p)

-- |  Integer p-adic number with explicitly specified precision.
newtype Z' (p :: Nat) (prec :: Nat) = Z' (R prec p)
newtype R (prec :: Nat ) (p :: Nat) = R (Mod (LiftedRadix p prec))

deriving via Mod (LiftedRadix p prec) instance Radix p prec => Num (R prec p)
deriving via R prec p instance Radix p prec => Num (Z' p prec)

instance Radix p prec => Eq (Z' p prec) where
  x@(Z' (R a)) == Z' (R b) = unMod a `mod` pk == unMod b `mod` pk
    where
      pk = radix x ^ precision x

instance Radix p prec => PadicNum (Z' p prec) where
  type Unit (Z' p prec) = Z' p prec
  type Lifted (Z' p prec) = Integer
  type Digit (Z' p prec) = Mod p 

  {-# INLINE precision #-}
  precision = fromIntegral . natVal

  {-# INLINE  radix #-}
  radix (Z' r) = fromIntegral $ natVal r
  
  {-# INLINE fromDigits #-}
  fromDigits = mkUnit . fromRadix

  {-# INLINE digits #-}
  digits n = toRadix (lifted n)

  {-# INLINE lifted #-}
  lifted (Z' (R n)) = lifted n

  {-# INLINE mkUnit #-}
  mkUnit = Z' . R . fromInteger

  {-# INLINE fromUnit #-}
  fromUnit (u, v) = mkUnit $ radix u ^ fromIntegral v * lifted u

  splitUnit n = case getUnitZ (radix n) (lifted n) of
                  (0, 0) -> (0, precision n)
                  (u, v) -> (mkUnit u, v)
  
  isInvertible n = (lifted n `mod` p) `gcd` p == 1
    where
      p = radix n
  
  inverse (Z' (R n))  = Z' . R <$> invertMod n

instance Radix p prec => Show (Z' p prec) where
  show n = 
     case findCycle pr ds of
       Nothing | length ds > pr -> ell ++ toString (take pr ds)
               | otherwise -> toString ds
       Just ([],[0]) -> "0"
       Just (pref, [0]) -> toString pref
       Just (pref, cyc)
        | length pref + length cyc <= pr ->
          let sp = toString pref
              sc = toString cyc
           in "(" ++ sc ++ ")" ++ sep ++ sp
        | otherwise -> ell ++ toString (take pr $ pref ++ cyc)
    where
      pr = precision n
      ds = digits n
      showD = show . unMod
      toString = intercalate sep . map showD . reverse
      ell = "…" ++ sep 
      sep
        | radix n < 11 = ""
        | otherwise = " "

instance Radix p prec  => Enum (Z' p prec) where
  toEnum = fromIntegral
  fromEnum = fromIntegral . toInteger

instance Radix p prec => Real (Z' p prec) where
  toRational 0 = 0
  toRational n = extEuclid (lifted n, liftedRadix n)

instance Radix p prec => Integral (Z' p prec) where
  toInteger n = if denominator r == 1
                then numerator r
                else lifted n `mod` (radix n ^ precision n)
    where
      r = toRational n
  a `quotRem` b = case inverse b of
    Nothing -> error "not divisible!" 
    Just r -> let q = a*r in (q, a - q * b)

instance Radix p prec => Ord (Z' p prec) where
  compare = error "ordering is not defined for Z"

