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

-- |
-- Module      : Math.NumberTheory.Padic
-- Description : Representation a nd simple algebra for p-adic numbers.
-- Copyright   : (c) Sergey Samoylenko, 2022
-- License     : GPL-3
-- Maintainer  : samsergey@yandex.ru
-- Stability   : experimental
-- Portability : POSIX
--
-- Module introduces p-adic integers \(\mathbb{Z}_p\) and p-adic rational numbers \(\mathbb{Q}_p\)
-- of arbitratry precision, implementing basic arithmetic as well as some specific functions,
-- i.e. detection of periodicity in sequence of digits, rational reconstruction, computation of square roots etc.
--
-- The radix \(p\) of a p-adic number is specified at a type level via type-literals. In order to use them GHCi should be loaded with a couple of extensions.
--
-- >>> :set -XDataKinds -XTypeOperators
-- >>> 45 :: Z 10
-- 45
-- >>> 45 :: Q 5
-- 140.0
--
-- Digits of p-adic expansion for rational and negative numbers eventually form infinite periodic sequences. 
--
-- >>> -3 :: Z 10
-- (9)7 -- equivalent to ...9999999997
-- >>> 1/15 :: Q 5
-- (13).2 -- equivalent to ...13131313.2
--
-- Negative p-adic integers and rational p-adics have trailing periodic digit sequences, which are represented in parentheses.
--
-- >>> -45 :: Z 7
-- (6)04
-- >>> 1/7 :: Q 10
-- (285714)3.0
--
--
-- The working precision of all p-adics is effetively infinite. However for textual output and rational reconstruction some finite precision should be specified.
--
-- Rational decomposition is done using a method from Paul S. Wang.
-- For a truncated p-adic number \(x = \frac{r}{s}\) the equation
-- \( x \cdot s \equiv r\ (\mathrm{mod}\ p^k)\) is solved by extended Euclidean method.
-- The power \(k\) depends on the specifiied precision of a p-adic number and affects the upper bounds of numerator and denominator of the reconstructed rational.
--
------------------------------------------------------------

module Math.NumberTheory.Padic
  ( 
  -- * Classes and functions
  -- ** Type synonyms and constraints
    ValidRadix
  , LiftedRadix
  , Lifted
  , Radix
  -- ** Digital objects
  , Digital
  , Digits
  , radix
  , digits
  , fromDigits
  , liftedDigits
  , mkUnit
  , firstDigit
  -- ** p-adic numbers
  , Padic
  , Unit
  , splitUnit
  , fromUnit
  , inverse
  , unit
  , valuation
  , norm
  , normalize
  , isZero
  -- ** Objects with fixed precision
  , Fixed
  , precision
  , showPrec
  , eqPrec
  , type (%) (..)
    -- * Data types
    -- ** p-Adic integers
  , Z
  , Q
  -- * Functions and utilities
  , isInvertible
  , fromRadix
  , toRadix
  , findCycle
  , sufficientPrecision
  , getUnitQ
  , getUnitZ
  , henselLifting
  ) where

import Data.Maybe
import Data.Mod
import Control.Monad
import Math.NumberTheory.Padic.Classes
import Math.NumberTheory.Padic.Integer
import Math.NumberTheory.Padic.Rational
import Math.NumberTheory.Padic.Precision

------------------------------------------------------------
-- | For given radix /p/ and natural number /m/ returns precision sufficient for rational
-- reconstruction of fractions with numerator and denominator not exceeding /m/.
--
-- Examples:
--
-- >>> sufficientPrecision 2 (maxBound :: Int)
-- 65
-- >>> sufficientPrecision 3 (maxBound :: Int)
-- 41
-- >>> sufficientPrecision 11 (maxBound :: Int)
-- 19
sufficientPrecision :: (Integral a) => Integer -> a -> Integer
sufficientPrecision p m = ilog p (2 * fromIntegral m) + 1

 
-- | p-Adic solution of the equation via Newton method.
--
-- Examples:
--
-- >>> henselLifting (\x -> x*x - x) (\x -> 2*x-1) :: [Z 10]
-- [0,1,…92256259918212890625,…07743740081787109376]
-- 
henselLifting ::
     (Eq n, Padic n, Digits n ~ [Mod p], Radix p)
  => (n -> n) -- ^ Function to be vanished.
  -> (n -> n) -- ^ Derivative of the function.
  -> [n] -- ^ The result.
henselLifting f f' = res
  where
    pr = precision (head res)
    mf = firstDigit . f . fromMod
    res = do
      r <- fromMod <$> filter (\x -> mf x == 0) [0..]
      iterateM pr step r
    step x = do
      invf' <- maybeToList (inverse (f' x))
      return (x - f x * invf')

iterateM :: (Eq a, Monad m) => Int -> (a -> m a) -> a -> m a
iterateM n f = go n
  where
    go 0 x = pure x
    go i x = do
      y <- f x
      if x == y then pure x else go (i - 1) y
    
fib a b = a : fib b (a + b)
