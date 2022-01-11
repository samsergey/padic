{-# LANGUAGE DataKinds #-}
{- |
Module      : Math.NumberTheory.Padic.Fixed
Description : Representation and simple algebra for p-adic numbers.
Copyright   : (c) Sergey Samoylenko, 2022
License     : GPL-3
Maintainer  : samsergey@yandex.ru
Stability   : experimental
Portability : POSIX

Module introduces p-adic integers and rationals with basic p-adic arithmetics
and implments some specific functions (rational reconstruction, p-adic signum function, square roots etc.).

A truncated p-adic number \(x\) can be represented in three ways:

\[
\begin{align}
x &= p^v u & (1)\\
& = d_0 + d_1 p + d_2 p^2 + ... d_k p^k & (2)\\
&= N\ \mathrm{mod}\ p^k, & (3)
\end{align}
\]
where \(p > 1, k > 0, v \in \mathbb{Z},u \in \mathbb{Z_p},d_i \in \mathbb{Z}/p\mathbb{Z}, N \in  \mathbb{Z}/p^k \mathbb{Z}\)

In order to gain efficiency the integer p-adic number with radix \(p\) is internally
represented in form \((3)\) as only one digit \(N\), lifted to modulo \(p^k\), where \(k\) is
chosen so that within working precision numbers belogning to @Int@ and @Ratio Int@ types could be
reconstructed by extended Euclidean method. Form \((2)\) is used for textual output only, and form \((1)\)
is used for transrornations to and from rationals.

The documentation and the module bindings use following terminology:

  * `radix` -- modulus \(p\) of p-adic number,
  * `precision` -- maximal power \(k\) in p-adic expansion,
  * `unit` -- invertible muliplier \(u\) for prime \(p\),
  * `valuation` -- exponent \(v\),
  * `digits` -- list \(d_0,d_1,d_2,... d_k\) in the canonical p-adic expansion of a number,
  * `lifted` -- digit \(N\) lifted to modulo \(p^k\).

Rational p-adic number is represented as a unit (belonging to \(\mathbb{Z_p}\) ) and valuation, which may be negative.

The radix \(p\) of a p-adic number is specified at a type level via type-literals. In order to use them GHCi should be loaded with `-XDataKinds` extensions.

>>> :set -XDataKinds
>>> 45 :: Z 10
45
>>> 45 :: Q 5
140.0

Negative p-adic integers and rational p-adics have trailing periodic digit sequences, which are represented in parentheses.

>>> -45 :: Z 7
(6)04
>>> 1/7 :: Q 10
(285714)3.0

By default the precision of p-adics is computed so that it is possible to reconstruct integers and rationals using extended Euler's method. However precision could be specified explicitly via type-literal:

>>> sqrt 2 :: Q 7
…623164112011266421216213.0
>>> sqrt 2 :: Q' 7 5
…16213.0
>>> sqrt 2 :: Q' 7 50
…16244246442640361054365536623164112011266421216213.0

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
  , SufficientPrecision
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
  -- * Functions and utilities
  -- ** p-adic numbers and arithmetics
  , radix
  , precision
  , digits
  , firstDigit
  , reduce
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
  , getUnitZ
  , getUnitQ
  -- ** p-adic analysis
  , findSolutionMod
  , henselLifting
  , unityRoots
  , pSqrt
  , pPow
  , pExp
  , pLog
  , pSin
  , pCos
  , pSinh
  , pCosh
  , pTanh
  , pAsin
  , pAsinh
  , pAcosh
  , pAtanh
  -- ** Miscelleneos tools
  , fromRadix
  , toRadix
  , findCycle
  , sufficientPrecision
  ) where

import Math.NumberTheory.Padic.Types
import Math.NumberTheory.Padic.Integer
import Math.NumberTheory.Padic.Rational
import Math.NumberTheory.Padic.Analysis
import Data.Word
import Data.Ratio

