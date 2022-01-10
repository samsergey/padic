{-# LANGUAGE DataKinds #-}
{- |
Module      : Math.NumberTheory.Padic.Fixed
Description : Representation and simple algebra for p-adic numbers with fixed precision.
Copyright   : (c) Sergey Samoylenko, 2022
License     : GPL-3
Maintainer  : samsergey@yandex.ru
Stability   : experimental
Portability : POSIX

Module introduces p-adic integers \(\mathbb{Z}_p\) and p-adic rational numbers \(\mathbb{Q}_p\)
with fixed precision, implementing basic arithmetic as well as some specific functions,
i.e. rational reconstruction, computation of square roots etc.

In order to gain efficiency the integer p-adic number with radix \(p\) is internally
represented as only one digit /lifted/ to modulo \(p^k\), where \(k\) is
chosen so that within working precision numbers belogning to @Int@ and @Ratio Int@ types could be
reconstructed by extended Euclidean method. 

The radix \(p\) of a p-adic number is specified at a type level via type-literals. In order to use them GHCi should be loaded with a couple of extensions.

>>> :set -XDataKinds -XTypeOperators
>>> 45 :: Z 10
45
>>> 45 :: Q 5
140.0

Negative p-adic integers and rational p-adics have trailing periodic digit sequences, which are represented in parentheses.

>>> -45 :: Z 7
(6)04
>>> 1/7 :: Q 10
(285714)3.0

By default the precision of p-adics is computed so that it makes possible to reconstruct integers and rationals using extended Euler's method (as given in ...). However precision could be specified explicitly via type-literal:

>>> -45 :: Z' 10 5
…99955
>>> 1 / 175 :: Q' 7 50
…50165016501650165016501650165016501650165016501650.2

-}
------------------------------------------------------------
module Math.NumberTheory.Padic
( 
  -- * Data types
  -- ** p-Adic integers
    Z
  , Z'
  -- ** p-Adic rationals
  , Q
  , Q'
  , Padic
  -- * Classes and functions
  -- ** Type synonyms and constraints
  , ValidRadix
  , KnownRadix
  , LiftedRadix
  , Radix
  -- ** p-adic numbers
  , PadicNum
  , Unit
  , Digit
  , Lifted
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
  , inverse
  , isInvertible
  , isZero
  -- * Functions and utilities
  , findSolutionMod
  , henselLifting
  , pExp
  , pLog
  , fromRadix
  , toRadix
  , findCycle
  , sufficientPrecision
  , getUnitZ
  , getUnitQ
  ) where

import Math.NumberTheory.Padic.Commons
import Math.NumberTheory.Padic.Integer
import Math.NumberTheory.Padic.Rational
import Data.Word
import Data.Ratio

