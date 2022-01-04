{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE DerivingVia #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE UndecidableInstances #-}
{-# OPTIONS_HADDOCK hide, prune, ignore-exports #-}

module Math.NumberTheory.Padic.Classes  where

------------------------------------------------------------

class Fixed a where
  -- | Returns the precision of a number.
  --
  -- Examples:
  --
  -- >>> precision (123 :: Z 2)
  -- 20
  -- >>> precision (123 :: Z' 2 % 40)
  -- 40
  precision :: Integral i => a -> i
  -- | Analog of @show@ with specified precision.
  showPrec :: Int -> a -> String
  -- | Analog of @==@ with specified precision.
  eqPrec :: Int -> a -> a -> Bool
  

------------------------------------------------------------
-- | Typeclass for digitally representable objects
class Digital n where
  -- | A type for digit or a list of digits.
  type Digits n
  -- | A type for internal representation of digits
  type LiftedDigits n
  -- | Constructor for a digital object from it's digits
  fromDigits :: Digits n -> n
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
  digits :: n -> Digits n
  -- | Returns the radix of a number
  --
  -- Examples:
  --
  -- >>> radix (5 :: Z 13)
  -- 13
  -- >>> radix (-5 :: Q' 3 40)
  -- 3
  radix :: Integral i => n -> i
  -- | Returns lifted digits
  --
  -- Examples:
  --
  -- >>> take 3 $ liftedDigits (123 :: Z 10)
  -- [(123 `modulo` 10000000000000000000),(0 `modulo` 10000000000000000000),(0 `modulo` 10000000000000000000)]
  -- >>> take 3 $ liftedDigits (-123 :: Z 2)
  -- [(9223372036854775685 `modulo` 9223372036854775808),(9223372036854775807 `modulo` 9223372036854775808),(9223372036854775807 `modulo` 9223372036854775808)]
  liftedDigits :: n -> LiftedDigits n
  -- | Creates digital object from it's lifted digits.
  mkUnit :: LiftedDigits n -> n

-- | The least significant digit of a p-adic number.
firstDigit n = head (digits n)

------------------------------------------------------------
-- | Typeclass for p-adic numbers
class (Num n, Digital n, Fixed n) => Padic n where
  -- | A type for p-adic unit.
  type Unit n
  -- | Creates p-adic number from given unit and valuation.
  --
  -- prop> fromUnit (u, v) = u * p^v
  fromUnit :: (Unit n, Int) -> n
  -- | Splits p-adic number into unit and valuation.
  --
  -- prop> splitUnit (u * p^v) = (u, v)
  splitUnit :: n -> (Unit n, Int)
  -- | Partial multiplicative inverse of p-adic number (defined both for integer or rational p-adics).
  inverse :: n -> Maybe n
  
-- | returns the unit of a number
--
-- Examples:
--
-- >>> unit (120 :: Z 10)
-- 12
-- >>> unit (75 :: Z 5)
-- 3
unit :: Padic n => n -> Unit n
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
-- >>> valuation (0 :: Q 2 % 150)
-- 150
valuation :: Padic n => n -> Int
valuation = snd . splitUnit

-- | returns a rational norm of a number
--
-- Examples:
--
-- >>> norm (120 :: Z 10)
-- 0.1
-- >>> norm (75 :: Z 5)
-- 4.0e-2
norm :: (Fractional f, Padic n) => n -> f
norm n = fromIntegral (radix n) ^^ (-valuation n)

-- | Returns @True@ for a p-adic number which is equal to zero (within it's precision).
isZero :: Padic n => n -> Bool
isZero n = valuation n >= precision n
