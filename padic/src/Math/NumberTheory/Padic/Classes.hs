{-# OPTIONS_HADDOCK hide, prune, ignore-exports #-}

{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE MagicHash #-}

module Math.NumberTheory.Padic.Classes  where

import Data.Ratio
import Data.List (unfoldr, genericLength)
import Data.Maybe (isJust)
import Data.Mod  
import GHC.TypeLits hiding (Mod)
import Data.Constraint (Constraint)
import GHC.Integer (smallInteger)
import GHC.Integer.Logarithms ( integerLogBase# )

------------------------------------------------------------
-- | Constraint for non-zero natural number which can be a radix.
type family ValidRadix (m :: Nat) :: Constraint where
  ValidRadix 0 = TypeError ('Text "Zero radix!")
  ValidRadix 1 = TypeError ('Text "Radix should be more then 1!")
  ValidRadix m = ()

-- | Constraint for valid radix of a number
type Radix m = ( ValidRadix m , KnownNat m)

-- | Constraint for regular p-adic number.
type family RealPadic n p prec :: Constraint where
  RealPadic n p prec =
    ( Padic n
    , Padic (Unit n)
    , Real n
    , Radix p
    , KnownNat prec
    )

------------------------------------------------------------
-- | Typeclass for digitally representable objects
class Padic n where
  -- | A type for p-adic unit.
  type Unit n
  -- | A type for digits of p-adic expansion.
  -- This type allows to assure that digits will agree with the radix @p@ of the number.
  type Digit n
  -- | Internal representation of p-adic number.
  type LiftedDigits n
  -- | Returns the precision of a number.
  --
  -- Examples:
  --
  -- >>> precision (123 :: Z 2)
  -- 20
  -- >>> precision (123 :: Z' 2 40)
  -- 40
  precision :: Integral i => n -> i
  -- | Returns the radix of a number
  --
  -- Examples:
  --
  -- >>> radix (5 :: Z 13)
  -- 13
  -- >>> radix (-5 :: Q' 3 40)
  -- 3
  radix :: Integral i => n -> i
 
  -- | Constructor for a digital object from it's digits
  fromDigits :: [Digit n] -> n
  -- | Returns digits of a digital object
  --
  -- Examples:
  --
  -- >>> take 5 $ digits (123 :: Z 10)
  -- [(3 `modulo` 10),(2 `modulo` 10),(1 `modulo` 10),(0 `modulo` 10),(0 `modulo` 10)]
  -- >>> take 5 $ digits (-123 :: Z 2)
  -- [(1 `modulo` 2),(0 `modulo` 2),(1 `modulo` 2),(0 `modulo` 2),(0 `modulo` 2)]
  -- >>> take 5 $ digits (1/200 :: Q 10)
  -- [(1 `modulo` 2),(0 `modulo` 2),(1 `modulo` 2),(0 `modulo` 2),(0 `modulo` 2)]
  digits :: n -> [Digit n]
  -- | Returns lifted digits
  --
  -- Examples:
  --
  -- >>> take 3 $ lifted (123 :: Z 10)
  -- [(123 `modulo` 10000000000000000000),(0 `modulo` 10000000000000000000),(0 `modulo` 10000000000000000000)]
  -- >>> take 3 $ lifted (-123 :: Z 2)
  -- [(9223372036854775685 `modulo` 9223372036854775808),(9223372036854775807 `modulo` 9223372036854775808),(9223372036854775807 `modulo` 9223372036854775808)]
  lifted :: n -> LiftedDigits n

  -- | Creates digital object from it's lifted digits.
  mkUnit :: LiftedDigits n -> n

  -- | Creates p-adic number from given unit and valuation.
  --
  -- prop> fromUnit (u, v) = u * p^v
  fromUnit :: (Unit n, Int) -> n
  -- | Splits p-adic number into unit and valuation.
  --
  -- prop> splitUnit (u * p^v) = (u, v)
  splitUnit :: n -> (Unit n, Int)
 
  -- | Returns @True@ for a p-adic number which is multiplicatively invertible.
  isInvertible :: n -> Bool

  -- | Partial multiplicative inverse of p-adic number (defined both for integer or rational p-adics).
  inverse :: n -> Maybe n
  

-- | The least significant digit of a p-adic number.
{-# INLINE firstDigit #-}
firstDigit n = head (digits n)

{- | Returns the unit of a number

Examples:

>>> unit (120 :: Z 10)
12
>>> unit (75 :: Z 5)
3 -}
unit :: Padic n => n -> Unit n
{-# INLINE unit #-}
unit = fst . splitUnit

{- | Returns a valuation  of a number

Examples:

>>> valuation (120 :: Z 10)
1
>>> valuation (75 :: Z 5)
2

Valuation of zero is equal to working precision

>>> valuation (0 :: Q 2)
20
>>> valuation (0 :: Q' 2 150)
150 -}
valuation :: Padic n => n -> Int
{-# INLINE valuation #-}
valuation = snd . splitUnit

-- | returns a rational norm of a number
--
-- Examples:
--
-- >>> norm (120 :: Z 10)
-- 0.1
-- >>> norm (75 :: Z 5)
-- 4.0e-2
norm :: (Integral i, Padic n) => n -> Ratio i
{-# INLINE norm #-}
norm n = (radix n % 1) ^^ (-valuation n)

-- | Returns @True@ for a p-adic number which is equal to zero (within it's precision).
isZero :: Padic n => n -> Bool
{-# INLINE isZero #-}
isZero n = valuation n >= precision n

instance Radix p => Padic (Mod p) where
  type Unit (Mod p) = Mod p
  type LiftedDigits (Mod p) = Integer
  type Digit (Mod p) = Mod p
  radix = fromIntegral . natVal
  precision _ = fromIntegral (maxBound :: Int)
  digits = pure
  fromDigits = head
  lifted = fromIntegral . unMod
  mkUnit = fromInteger
  inverse = invertMod
  isInvertible = isJust . invertMod 
  fromUnit (u, 0) = u
  fromUnit _ = 0
  splitUnit u = (u, 0)

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
fromRadix ds = foldr (\x r -> lifted x + r * p) 0 ds
  where
    p = fromIntegral $ natVal $ head $ 0 : ds

extEuclid :: Integral i => (Integer, Integer) -> Ratio i
extEuclid (n, m) = go (m, 0) (n, 1)
  where
    go (v1, v2) (w1, w2)
      | 2*w1*w1 > abs m =
        let q = v1 `div` w1
         in go (w1, w2) (v1 - q * w1, v2 - q * w2)
      | otherwise = fromRational (w1 % w2)

ilog :: (Integral a, Integral b) => a -> a -> b
ilog a b =
  fromInteger $ smallInteger (integerLogBase# (fromIntegral a) (fromIntegral b))

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

liftedRadix :: (Padic n, Integral a) => n -> a
{-# INLINE liftedRadix #-}
liftedRadix n = radix n ^ (2*precision n + 1)
