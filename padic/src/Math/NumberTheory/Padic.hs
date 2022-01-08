{- |
Module      : Math.NumberTheory.Padic
Description : Representation and simple algebra for p-adic numbers.
Copyright   : (c) Sergey Samoylenko, 2022
License     : GPL-3
Maintainer  : samsergey@yandex.ru
Stability   : experimental
Portability : POSIX

Module introduces p-adic integers \(\mathbb{Z}_p\) and p-adic rational numbers \(\mathbb{Q}_p\)
of arbitratry precision, implementing basic arithmetic as well as some specific functions,
i.e. detection of periodicity in sequence of digits, rational reconstruction, computation of square roots etc.

In order to gain efficiency the integer p-adic number with radix \(p\) is internally
represented as a list of digits /lifted/ to modulo \(p^k\), where \(k\) is
chosen so that within working precision numbers belogning to @Int@ and @Ratio Int@ types could be
reconstructed by extended Euclidean method, using only the first digit.

\[
x = ...ddddddddddddddd_{(p)} =  ... \underbrace{ddddd}_k\,\underbrace{ddddd}_k\,\underbrace{ddddd}_k{}_{(p^k)}
\]

The infinite sequence of digits modulo \(p\) may be obtained by 'digits' function.
Potential infinitness of digits is used for detection of cycles in the digit sequence of p-adic expansion.
For more efficient implementation see `Math.NumberTheory.Padic.Fixed` module.

The radix \(p\) of a p-adic number is specified at a type level via type-literals. In order to use them in GHCi, set `-XDataKinds` extension on.

>>> :set -XDataKinds
>>> 45 :: Z 10
45
>>> 45 :: Q 5
140.0

Digits of p-adic expansion for rational and negative numbers eventually form infinite periodic sequences, which are represented with parentheses:

>>> -3 :: Z 10
(9)7 -- equivalent to ...9999999997
>>> 1/15 :: Q 5
(13).2 -- equivalent to ...13131313.2

By default the precision of p-adics is bounded by 20 digits. However precision could be specified explicitly:

>>> 1 `div` 23 :: Z 10
…65217391304347826087
>>> 1 `div` 23 :: Z' 10 5
…26087
>>> 1 `div` 23 :: Z' 10 50
(6956521739130434782608)7
>>> 233 / 637 :: Q' 7 50
(210352456314).45

-}
------------------------------------------------------------
module Math.NumberTheory.Padic
  ( 
  -- * Classes and functions
  -- ** p-adic numbers
    Padic
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
  -- ** Type synonyms and constraints
  , ValidRadix
  , KnownRadix
  , LiftedRadix
  , Radix
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
  , getUnitZ
  , getUnitQ
  , findSolutionMod
  , henselLifting
  ) where

import Math.NumberTheory.Padic.Classes
import Math.NumberTheory.Padic.Integer
import Math.NumberTheory.Padic.Rational

