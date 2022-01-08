{- |
Module      : Math.NumberTheory.Padic.Fixed
Description : Representation a nd simple algebra for p-adic numbers with fixed precision.
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
chosen so that within working precision integers and rationals could be
reconstructed by by extended Euclidean method. Sequence of digits modulo \(p\) are used only for textual representation and may be obtained by 'digits' function. 

The radix \(p\) of a p-adic number is specified at a type level via type-literals. In order to use them GHCi should be loaded with a couple of extensions.

>>> :set -XDataKinds -XTypeOperators
>>> 45 :: Z 10
45
>>> 45 :: Q 5
140.0

By default the precision of p-adics is bounded by 20 digits.

>>>  -45 :: Z 10
…9999999999999999955
>>> 1 / 15 :: Q 3
…12101210121012101210.2

However precision could be specified explicitly:

>>> -45 :: Z' 10 5
…99955
>>> 1 / 175 :: Q' 7 50
…50165016501650165016501650165016501650165016501650.2

-}
------------------------------------------------------------
module Math.NumberTheory.Padic.Fixed
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
  , henselLifting ) where

import Math.NumberTheory.Padic.Classes
import Math.NumberTheory.Padic.Fixed.Integer
import Math.NumberTheory.Padic.Fixed.Rational

