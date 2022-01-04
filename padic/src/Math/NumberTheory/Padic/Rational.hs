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
data Q (p :: Nat) = Q (Z p) Int

instance Radix p => Fixed (Q p) where
  precision _ = 20

  showPrec pr n = si ++ sep ++ "." ++ sep ++ sf
    where
      k = valuation n
      ds = digits (unit n)
      (f, i) =
        case compare k 0 of
          EQ -> ([0], ds)
          GT -> ([0], replicate k 0 ++ ds)
          LT -> splitAt (-k) ds
      sf = intercalate sep $ showD <$> reverse f
      si =
        case findCycle pr i of
          ([], [0]) -> "0"
          (pref, []) -> ell ++ toString pref
          (pref, [0]) -> toString pref
          (pref, cyc)
            | length pref + length cyc <= pr ->
              let sp = toString pref
                  sc = toString cyc
               in "(" ++ sc ++ ")" ++ sep ++ sp
            | otherwise -> ell ++ toString (take pr $ pref ++ cyc)
      showD = show . unMod
      toString = intercalate sep . map showD . reverse
      ell = "…" ++ sep
      sep
        | radix n < 11 = ""
        | otherwise = " "

  eqPrec pr a b =
    (isZero a && isZero b)
    || (valuation a' == valuation b' && eqPrec pr (unit a') (unit b'))
    where
      a' = normalize a
      b' = normalize b

instance Radix p => Show (Q p) where
  show n = showPrec (precision n) n

instance Radix p => Eq (Q p) where
  a == b = eqPrec (precision a) a b

instance Radix p => Ord (Q p) where
  compare = error "Order is nor defined for p-adics."

instance Radix p => Digital (Q p) where
  type Digits (Q p) = Digits (Z p)
  type LiftedDigits (Q p) = LiftedDigits (Z p)
  radix = fromIntegral . natVal
  digits (Q u v) = replicate v 0 ++ digits u
  fromDigits ds = normalize $ Q (fromDigits ds) 0
  liftedDigits = liftedDigits . unit
  mkUnit ds = normalize $ Q (mkUnit ds) 0

instance Radix p => Padic (Q p) where
  type Unit (Q p) = Z p
  fromUnit (u, v) = Q u v
  splitUnit (Q u v) = (u, v)
  
  inverse n
    | unMod (firstDigit n) `gcd` radix n == 1 = Just (1/n)
    | otherwise = Nothing

{- | Adjusts unit and valuation of p-adic number, by removing trailing zeros from the right-side of the unit.

Examples:

>>> λ> x = 2313 + 1387 :: Q 10
>>> x
3700.0
>>> splitUnit x
(3700,0)
>>> splitUnit (normalize x)
(37,2) -}
normalize :: RealPadic n p  => n -> n
--normalize 0 = 0
normalize n = go (liftedDigits u) v
  where
    (u, v) = splitUnit n
    go _ k | k >= pr = 0
    go (d:ds) k = case getUnitZ p (fromIntegral d) of
      (0, 0) -> go ds (k + ilog p (radix d))
      (d', k')
        | k + k' >= pr -> 0
        | otherwise ->
          let s = fromIntegral (p^k')
          in fromUnit (mkUnit (shiftL s (fromIntegral d':ds)), k + k')
    p = radix n
    pr = precision n

shiftL :: Radix p => Lifted p -> [Lifted p] -> [Lifted p]
shiftL s (d1:d2:ds) = let (q, r) = quotRem d2 s
                          pk = fromIntegral (radix s `div` fromIntegral s)
                      in d1 + r * pk : shiftL s (q : ds)
  
instance Radix p => Num (Q p) where
  fromInteger n = res
    where
      (u, v) = getUnitZ (radix res) n
      pr = precision res
      res | n == 0 = Q 0 pr
          | v >= pr = Q 0 pr
          | otherwise = normalize $ Q (fromInteger u) v
          
  a + b = Q (p ^ (va - v) * unit a + p ^ (vb - v) * unit b) v
    where
      va = valuation a
      vb = valuation b
      v = va `min` vb
      p = radix a
  a * b = Q (unit a * unit b) (valuation a + valuation b)
  negate (Q u v) = Q (negate u) v
  abs = id
  signum 0 = 0
  signum _ = 1

instance Radix p => Fractional (Q p) where
  fromRational 0 = 0
  fromRational x = res
    where
      res = normalize $ Q (fromDigits (series n)) v
      p = radix res
      (q, v) = getUnitQ p x
      (n, d) = (fromIntegral $ numerator q, fromIntegral $ denominator q)
      series 0 = repeat 0
      series n =
        let m = fromIntegral n / fromIntegral d
         in m : series ((n - fromIntegral (unMod m) * d) `div` p)
  a / b = Q res (valuation a - valuation b')
    where
      b' = normalize b
      res =
        case divMaybe (unit a) (unit b') of
          Nothing ->
            error $
            show b ++ " is indivisible in " ++ show (radix a) ++ "-adics!"
          Just r -> r

instance (Radix p) => Real (Q p) where
  toRational 0 = 0
  toRational n = ratDecomposition (precision n) n 

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

