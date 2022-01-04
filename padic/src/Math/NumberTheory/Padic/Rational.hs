{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE DerivingVia #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE UndecidableInstances #-}
{-# OPTIONS_HADDOCK hide, prune, ignore-exports #-}

module Math.NumberTheory.Padic.Rational where

import Data.List
import Data.Ratio
import Data.Mod
import GHC.TypeLits hiding (Mod)
import Math.NumberTheory.Padic.Classes
import Math.NumberTheory.Padic.Integer

------------------------------------------------------------

-- |  Rational p-adic number (an element of \(\mathbb{Q}_p\)) with 20 digits precision.
type Q p = Q' p 20

-- |  Rational p-adic number with explicitly specified precision.
newtype Q' (p :: Nat) (prec :: Nat) = Q' (Z' p prec, Int)

instance (Radix p, KnownNat prec) => Show (Q' p prec) where
  show n = si ++ sep ++ "." ++ sep ++ sf
    where
      pr = precision n
      k = valuation n
      ds = digits (unit n)
      (f, i) =
        case compare k 0 of
          EQ -> ([0], ds)
          GT -> ([0], replicate k 0 ++ ds)
          LT -> splitAt (-k) ds
      sf = intercalate sep $ show <$> reverse f
      si =
        case findCycle pr i of
          Nothing
            | length i > pr -> ell ++ toString (take pr i)
            | otherwise -> toString (take pr i)
          Just (pref, cyc)
            | length pref + length cyc <= pr ->
              let sp = toString pref
                  sc = toString cyc
               in "(" ++ sc ++ ")" ++ sep ++ sp
            | otherwise -> ell ++ toString (take pr $ pref ++ cyc)
      toString = intercalate sep . map show . reverse
      ell = "…" ++ sep
      sep
        | radix n < 11 = ""
        | otherwise = " "

instance (Radix p, KnownNat prec) => Padic (Q' p prec) where
  type Unit (Q' p prec) = Z' p prec

  precision = fromIntegral . natVal

  radix (Q' (u, _)) = radix u

  digits (Q' (u, v)) = replicate v 0 ++ toRadix (radix u) (lifted u)

  fromDigits ds = normalize $ Q' (fromDigits ds, 0)

  lifted (Q' (u, _)) = lifted u

  mkUnit ds = normalize $ Q' (mkUnit ds, 0)

  fromUnit = Q'

  splitUnit (Q' (u, v)) = (u, v)
  

{- | Adjusts unit and valuation of p-adic number, by removing trailing zeros from the right-side of the unit.

Examples:

>>> λ> x = 2313 + 1387 :: Q 10
>>> x
3700.0
>>> splitUnit x
(3700,0)
>>> splitUnit (normalize x)
(37,2) -}
normalize :: (Radix p, KnownNat prec) => Q' p prec -> Q' p prec
normalize n@(Q' (u, v)) = go (lifted u) v
  where
    go _ k | k >= pr = zero
    go d k = case getUnitZ p d of
      (0, 0) -> zero
      (d', k')
        | k + k' >= pr -> zero
        | otherwise ->
          let s = p ^ fromIntegral k'
          in fromUnit (mkUnit d', k + k')
    p = radix u
    pr = precision n
    zero = Q' (0, pr)

instance (Radix p, KnownNat prec) => Eq (Q' p prec) where
  a == b =
    (isZero a' && isZero b')
    || (valuation a' == valuation b' && unit a' == unit b')
    where
      a' = normalize a
      b' = normalize b

instance (Radix p, KnownNat prec) => Ord (Q' p prec) where
  compare = error "Order is nor defined for p-adics."

instance (Radix p, KnownNat prec) => Num (Q' p prec) where
  fromInteger n = Q' (fromInteger n, 0)
          
  a + b = Q' (p ^ (va - v) * unit a + p ^ (vb - v) * unit b, v)
    where
      va = valuation a
      vb = valuation b
      v = va `min` vb
      p = radix a
  a * b = Q' (unit a * unit b, valuation a + valuation b)
  negate (Q' (u, v)) = Q' (negate u, v)
  abs = id
  signum 0 = 0
  signum _ = 1

instance (Radix p, KnownNat prec) => Fractional (Q' p prec) where
  fromRational 0 = 0
  fromRational x = res
    where
      res = Q' (n `div` d, v)
      p = radix res
      (q, v) = getUnitQ p x
      (n, d) = (mkUnit $ numerator q, mkUnit $ denominator q)
  a / b = Q' (res, valuation a - valuation b')
    where
      b' = normalize b
      res
        | isInvertible b = unit a `div` unit b'
        | otherwise = 
          error $ show b ++ " is indivisible in " ++ show (radix a) ++ "-adics!"

instance (Radix p, KnownNat prec) => Real (Q' p prec) where
  toRational n = toRational (unit n') * norm n'
    where n' = normalize n

------------------------------------------------------------

-- | Extracts p-adic unit from a rational number. For radix \(p\) and rational number \(x\) returns
-- pair \((r/s, k)\) such that \(x = r/s \cdot p^k\).
--
-- Examples:
--
-- >>> getUnitQ 3 (75/157)
-- (1,25 % 157)
-- >>> getUnitQ 5 (75/157)
-- (2,3 % 157)
-- >>> getUnitQ 157 (75/157)
-- (-1,75 % 1)
getUnitQ :: Integral p => p -> Ratio p -> (Ratio p, Int)
getUnitQ _ 0 = (0, 0)
getUnitQ p x = (c, genericLength v2 - genericLength v1)
  where
    (v1, b:_) =
      span (\n -> denominator n `mod` p == 0) $ iterate (* fromIntegral p) x
    (v2, c:_) =
      span (\n -> numerator n `mod` p == 0) $ iterate (/ fromIntegral p) b


