{-# LANGUAGE DerivingVia #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# OPTIONS_HADDOCK hide, prune, ignore-exports #-}

{-# LANGUAGE DataKinds #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE UnboxedTuples #-}
{-# LANGUAGE UnliftedFFITypes #-}
{-# LANGUAGE NoStarIsType #-}

module Math.NumberTheory.Padic.Modular where

import Data.List
import Data.Mod
import Data.Ratio
import Data.Maybe (listToMaybe)
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
deriving via Z_ prec p instance (LiftedRadix p prec) => Eq (Z' p prec)

newtype Z_ (prec :: Nat ) (p :: Nat) = Z_ (Mod (Lifted p prec))

deriving via Mod (Lifted p prec) instance (LiftedRadix p prec) => Num (Z_ prec p)
deriving via Mod (Lifted p prec) instance (LiftedRadix p prec) => Eq (Z_ prec p)

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
  
  type Digit (Z' p prec) = Mod p 

  precision = fromIntegral . natVal

  radix (Z' n) = fromIntegral $ natVal n
  
  fromDigits = mkUnit . fromRadix

  digits n = toRadix (lifted n)

  lifted (Z' (Z_ n)) = fromIntegral $ unMod n

  mkUnit = Z' . Z_ . fromInteger

  fromUnit (u, v) = mkUnit $ radix u ^ fromIntegral v * lifted u

  splitUnit n = case getUnitZ (radix n) (lifted n) of
                  (0, 0) -> (0, precision n)
                  (u, v) -> (mkUnit u, v)
  
  isInvertible n = (lifted n `mod` p) `gcd` p == 1
    where
      p = radix n
  
  inverse n
    | isInvertible n = Just (mkUnit $ recipModInteger (lifted n) pk)
    | otherwise = Nothing
    where
      pk = liftedMod n

instance LiftedRadix p prec  => Enum (Z' p prec) where
  toEnum = fromIntegral
  fromEnum = fromIntegral . toInteger

instance LiftedRadix p prec => Real (Z' p prec) where
  toRational 0 = 0
  toRational n = extEuclid (lifted n, liftedMod n)

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

------------------------------------------------------------
------------------------------------------------------------



extEuclid :: Integral i => (Integer, Integer) -> Ratio i
extEuclid (n, m) = go (m, 0) (n, 1)
  where
    go (v1, v2) (w1, w2)
      | 2*w1*w1 > abs m =
        let q = v1 `div` w1
         in go (w1, w2) (v1 - q * w1, v2 - q * w2)
      | otherwise = fromRational (w1 % w2)


-- | Extracts p-adic unit from integer number. For radix \(p\) and integer \(n\) returns
-- pair \((u, k)\) such that \(n = u \cdot p^k\).
--
-- Examples:
-- 
-- >>> getUnitQ 3 (75/157)
-- (1,25 % 157)
-- >>> getUnitQ 5 (75/157)
-- (2,3 % 157)
-- >>> getUnitQ 157 (75/157)
-- (-1,75 % 1)
getUnitZ :: Integer -> Integer -> (Integer, Int)
getUnitZ _ 0 = (0, 0)
getUnitZ p x = (b, length v)
  where
    (v, b:_) = span (\n -> n `mod` p == 0) $ iterate (`div` p) x

-- | Unfolds a number to a list of digits (integers modulo @p@).  
toRadix :: Radix p => Integer -> [Mod p]
toRadix 0 = [0]
toRadix n = res
  where
    res = unfoldr go n
    p = fromIntegral $ natVal $ head $ 0 : res
    go 0 = Nothing
    go x =
      let (q, r) = quotRem x p
       in Just (fromIntegral r, q)
  
-- | Folds a list of digits (integers modulo @p@) to a number.
fromRadix :: Radix p => [Mod p] -> Integer
fromRadix ds = foldr (\x r -> fromIntegral (unMod x) + r * p) 0 ds
  where
    p = fromIntegral $ natVal $ head $ 0 : ds
