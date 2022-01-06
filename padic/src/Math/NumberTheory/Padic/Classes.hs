{-# OPTIONS_HADDOCK hide, prune, ignore-exports #-}

{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE TypeFamilies #-}

module Math.NumberTheory.Padic.Classes  where

import Data.Ratio
import GHC.TypeLits
import Data.Constraint (Constraint)

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
  lifted :: n -> Integer

  -- | Creates digital object from it's lifted digits.
  mkUnit :: Integer -> n

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

-- | returns the unit of a number
--
-- Examples:
--
-- >>> unit (120 :: Z 10)
-- 12
-- >>> unit (75 :: Z 5)
-- 3
unit :: Padic n => n -> Unit n
{-# INLINE unit #-}
unit = fst . splitUnit

-- | returns a valuation  of a number
--
-- Examples:
--
-- >>> valuation (120 :: Z 10)
-- 1
-- >>> valuation (75 :: Z 5)
-- 2
--
-- Valuation of zero is equal to working precision
--
-- >>> valuation (0 :: Q 2)
-- 20
-- >>> valuation (0 :: Q' 2 150)
-- 150
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

liftedMod :: (Padic n, Integral a) => n -> a
{-# INLINE liftedMod #-}
liftedMod n = radix n ^ (2*precision n + 1)

