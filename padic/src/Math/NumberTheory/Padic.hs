{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE DerivingVia #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE MagicHash #-}

{- |
Module      : Math.NumberTheory.Padic
Description : Representation a nd simple algebra for p-adic numbers.
Copyright   : (c) Sergey Samoylenko, 2022
License     : GPL-3
Maintainer  : samsergey@yandex.ru
Stability   : experimental
Portability : POSIX

Module introduces p-adic integers \(\mathbb{Z}_p\) and p-adic rational numbers \(\mathbb{Q}_p\)
of arbitratry precision, implementing basic arithmetic as well as some specific functions,
i.e. detection of periodicity in sequence of digits, rational reconstruction, computation of square roots etc.

The radix \(p\) of a p-adic number is specified at a type level via type-literals. In order to use them GHCi should be loaded with a couple of extensions.

>>> :set -XDataKinds -XTypeOperators
>>> 45 :: Z 10
45
>>> 45 :: Q 5
140.0

Digits of p-adic expansion for rational and negative numbers eventually form infinite periodic sequences. 

>>> -3 :: Z 10
(9)7 -- equivalent to ...9999999997
>>> 1/15 :: Q 5
(13).2 -- equivalent to ...13131313.2

Negative p-adic integers and rational p-adics have trailing periodic digit sequences, which are represented in parentheses.

>>> -45 :: Z 7
(6)04
>>> 1/7 :: Q 10
(285714)3.0


In order to gain efficiency the integer p-adic number with radix \(p\) is internally
represented as only one digit /lifted/ to modulo \(p^k\), where \(k\) is
chosen so that within working precision integers and rationals could be
reconstructed.

prop> k = 2*precision n + 1

Sequence of digits modulo \(p\) are used only for textual representation and may be obtained by 'digits' function. 

Rational reconstruction is done using a method from Paul S. Wang.
For a truncated p-adic number \(x = \frac{r}{s}\) the equation
\( x \cdot s \equiv r\ (\mathrm{mod}\ p^k)\) is solved by extended Euclidean method.
-}
------------------------------------------------------------

module Math.NumberTheory.Padic
  ( 
  -- * Classes and functions
  -- ** Type synonyms and constraints
    ValidRadix
  , Radix
  -- ** p-adic numbers
  , Padic
  , Unit
  , radix
  , precision
  , digits
  , firstDigit
  , fromDigits
  , lifted
  , mkUnit
  , splitUnit
  , fromUnit
  , unit
  , valuation
  , norm
  , normalize
  , isZero
  , inverse
  , isInvertible
  -- * Data types
  -- ** p-Adic integers
  , Z
  , Z'
  -- ** p-Adic rationals
  , Q
  , Q'
  -- * Functions and utilities
  , fromRadix
  , toRadix
  , sufficientPrecision
  , henselLifting
  ) where

import Data.Maybe
import Control.Monad
import GHC.Integer.Logarithms (integerLogBase#)
import GHC.Integer (smallInteger)
import Math.NumberTheory.Padic.Classes
import Math.NumberTheory.Padic.Integer
import Math.NumberTheory.Padic.Rational

------------------------------------------------------------
-- | For given radix /p/ and natural number /m/ returns precision sufficient for rational
-- reconstruction of fractions with numerator and denominator not exceeding /m/.
--
-- Examples:
--
-- >>> sufficientPrecision 2 (maxBound :: Int)
-- 64
-- >>> sufficientPrecision 3 (maxBound :: Int)
-- 41
-- >>> sufficientPrecision 10 (maxBound :: Int)
-- 20
sufficientPrecision :: (Integral a) => Integer -> a -> Integer
sufficientPrecision p m = smallInteger (integerLogBase# p (2 * fromIntegral m)) + 1

 
-- | p-Adic solution of the equation via Newton method.
--
-- Examples:
--
-- >>> henselLifting (\x -> x*x - x) (\x -> 2*x-1) :: [Z 10]
-- [0,1,…92256259918212890625,…07743740081787109376]
-- 
henselLifting ::
     (Eq n, Num n, Padic n)
  => (n -> n) -- ^ Function to be vanished.
  -> (n -> n) -- ^ Derivative of the function.
  -> [n] -- ^ The result.
henselLifting f f' = res
  where
    pr = precision (head res)
    res = findSolutionMod f >>= iterateM pr step
    step x = do
      invf' <- maybeToList (inverse (f' x))
      return (x - f x * invf')

findSolutionMod :: (Num n, Padic n) => (n -> n) -> [n]
findSolutionMod f = res
  where
    res = [ d | d <- fromInteger <$> [0 .. p - 1]
            , firstDigit (f d) `mod` fromInteger p == 0 ]
    p = radix (head res)

iterateM :: (Eq a, Monad m) => Int -> (a -> m a) -> a -> m a
iterateM n f = go n
  where
    go 0 x = pure x
    go i x = do
      y <- f x
      if x == y then pure x else go (i - 1) y
    
fib a b = a : fib b (a + b)
