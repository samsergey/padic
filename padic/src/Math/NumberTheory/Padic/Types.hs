{-# OPTIONS_HADDOCK hide, prune, ignore-exports #-}

{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE UndecidableSuperClasses #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE MagicHash #-}
{-# LANGUAGE NoStarIsType #-}

module Math.NumberTheory.Padic.Types  where

import Data.Ratio
import Data.Maybe (isJust, maybeToList)
import Data.Mod  
import Data.Word  
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
type KnownRadix m = ( ValidRadix m , KnownNat m )
  
-- | Radix of the internal representation of integer p-adic number.
type family LiftedRadix p prec where
  LiftedRadix p prec = p ^ (2*prec + 1)

-- | Constraint for known valid radix of p-adic number as well as it's  lifted radix.
type family Radix p prec :: Constraint where
  Radix p prec =
    ( KnownNat prec
    , KnownRadix p
    , KnownRadix (LiftedRadix p prec)
    )

{- | Precision sufficient for rational reconstruction of number belonging to a type @num@.
Used in a type declaration as follows:

>>> x = 1 `div` 1234567898765432123456789 :: Z 2 (Sufficientprecision Word32 2)
>>> toRational x
13822228938088947473 % 12702006275138148709
>>> x = 1 `div` 1234567898765432123456789 :: Z 2 (Sufficientprecision Int 2)
>>> toRational x
1 % 1234567898765432123456789

-} 
type family SufficientPrecision num (p :: Nat) :: Nat where
  SufficientPrecision Word32 2 = 64
  SufficientPrecision Word32 3 = 43
  SufficientPrecision Word32 5 = 30
  SufficientPrecision Word32 6 = 26
  SufficientPrecision Word32 7 = 24
  SufficientPrecision Word8 p = Div (SufficientPrecision Word32 p) 4
  SufficientPrecision Word16 p = Div (SufficientPrecision Word32 p) 2
  SufficientPrecision Word64 p = 2 * (SufficientPrecision Word32 p) + 1
  SufficientPrecision Int p = 2 * SufficientPrecision Word32 p
  SufficientPrecision Word p = SufficientPrecision Word64 p
  SufficientPrecision (Ratio t) p = SufficientPrecision t p
  SufficientPrecision t p = Div (SufficientPrecision t 2) (Log2 p)

{- | Type family for p-adic numbers with precision defined by reconstructable number type.

>>>123456 :: Padic Int 7
1022634
>>> toInteger it
123456
>>> toRational (12345678987654321 :: Padic (Ratio Word16) 3)
537143292837 % 5612526479  -- insufficiend precision for proper reconstruction!!
>>> toRational (12345678987654321 :: Padic Rational 3)
12345678987654321 % 1

-}
type family Padic num (p :: Nat)

------------------------------------------------------------
{- | Typeclass for p-adic numbers.

-}
class (Eq n, Num n) => PadicNum n where
  -- | A type for p-adic unit.
  type Unit n
  -- | A type for digits of p-adic expansion.
  -- Associated type allows to assure that digits will agree with the radix @p@ of the number.
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
  -- >>> digits (123 :: Z 10)
  -- [(3 `modulo` 10),(2 `modulo` 10),(1 `modulo` 10),(0 `modulo` 10),(0 `modulo` 10)]
  -- >>> take 5 $ digits (-123 :: Z 2)
  -- [(1 `modulo` 2),(0 `modulo` 2),(1 `modulo` 2),(0 `modulo` 2),(0 `modulo` 2)]
  -- >>> take 5 $ digits (1/300 :: Q 10)
  -- [(7 `modulo` 10),(6 `modulo` 10),(6 `modulo` 10),(6 `modulo` 10),(6 `modulo` 10)]
  --
  digits :: n -> [Digit n]
  -- | Returns lifted digits
  --
  -- Examples:
  --
  -- >>> lifted (123 :: Z 10)
  -- 123
  -- >>> lifted (-123 :: Z 10)
  -- 9999999999999999999999999999999999999999877
  --
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
  

{- | The least significant digit of a p-adic number.
--
-- >>> firstDigit (123 :: Z 10)
-- (3 `modulo` 10)
-- >>> firstDigit (123 :: Z 257)
-- (123 `modulo` 257)
-}
firstDigit :: PadicNum n => n -> Digit n
{-# INLINE firstDigit #-}
firstDigit = head . digits

{- | Returns p-adic number reduced modulo @p@

>>> reduce (123 :: Z 10) :: Mod 100
(23 `modulo` 100)
-}
reduce :: (KnownRadix p, PadicNum n) => n -> Mod p
reduce = fromIntegral . lifted


{- | Returns the p-adic unit of a number

Examples:

>>> unit (120 :: Z 10)
12
>>> unit (75 :: Z 5)
3 -}
unit :: PadicNum n => n -> Unit n
{-# INLINE unit #-}
unit = fst . splitUnit

{- | Returns a p-adic valuation of a number

Examples:

>>> valuation (120 :: Z 10)
1
>>> valuation (75 :: Z 5)
2

Valuation of zero is equal to working precision

>>> valuation (0 :: Q 2)
64
>>> valuation (0 :: Q 10)
21 -}
valuation :: PadicNum n => n -> Int
{-# INLINE valuation #-}
valuation = snd . splitUnit

{- | Returns a rational p-adic norm of a number \(|x|_p\).

Examples:

>>> norm (120 :: Z 10)
0.1
>>> norm (75 :: Z 5)
4.0e-2
-}
norm :: (Integral i, PadicNum n) => n -> Ratio i
{-# INLINE norm #-}
norm n = (radix n % 1) ^^ (-valuation n)

{- | Adjusts unit and valuation of p-adic number, by removing trailing zeros from the right-side of the unit.

Examples:

>>> λ> x = 2313 + 1387 :: Q 10
>>> x
3700.0
>>> splitUnit x
(3700,0)
>>> splitUnit (normalize x)
(37,2) -}
normalize :: PadicNum n => n -> n
normalize = fromUnit . splitUnit

-- | Returns @True@ for a p-adic number which is equal to zero (within it's precision).
isZero :: PadicNum n => n -> Bool
{-# INLINE isZero #-}
isZero n = valuation n >= precision n

liftedRadix :: (PadicNum n, Integral a) => n -> a
{-# INLINE liftedRadix #-}
liftedRadix n = radix n ^ (2*precision n + 1)

{- | For given radix \(p\) and natural number \(m\) returns precision sufficient for rational
reconstruction of fractions with numerator and denominator not exceeding \(m\).

Examples:

>>> sufficientPrecision 2 (maxBound :: Int)
64
>>> sufficientPrecision 3 (maxBound :: Int)
41
>>> sufficientPrecision 10 (maxBound :: Int)
20
-}
sufficientPrecision :: Integral a => Integer -> a -> Integer
sufficientPrecision p m = ilog p (2 * fromIntegral m) + 2

ilog :: (Integral a, Integral b) => a -> a -> b
ilog a b =
  fromInteger $ smallInteger (integerLogBase# (fromIntegral a) (fromIntegral b))


-----------------------------------------------------------

instance KnownRadix p => PadicNum (Mod p) where
  type Unit (Mod p) = Mod p
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

