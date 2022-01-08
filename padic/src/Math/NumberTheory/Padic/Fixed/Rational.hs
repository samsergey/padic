{-# OPTIONS_HADDOCK hide, prune, ignore-exports #-}

{-# LANGUAGE DataKinds #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE UndecidableInstances #-}

module Math.NumberTheory.Padic.Fixed.Rational
  ( Q
  , Q'
  , normalize
  ) where

import Data.List (intercalate)
import Data.Ratio
import Data.Mod
import GHC.TypeLits (Nat, natVal)
import Math.NumberTheory.Padic.Classes
import Math.NumberTheory.Padic.Fixed.Integer

------------------------------------------------------------

-- |  Rational p-adic number (an element of \(\mathbb{Q}_p\)) with 20 digits precision.
type Q p = Q' p 20

-- |  Rational p-adic number with explicitly specified precision.
newtype Q' (p :: Nat) (prec :: Nat) = Q' (Z' p prec, Int)

instance Radix p prec => Show (Q' p prec) where
  show n = si ++ sep ++ "." ++ sep ++ sf
    where
      pr = precision n
      (u, k) = splitUnit (normalize n)
      ds = digits u
      (f, i) =
        clean <$> case compare k 0 of
          EQ -> ([0], ds)
          GT -> ([0], replicate k 0 ++ ds)
          LT -> splitAt (-k) (ds ++ replicate pr 0)
      sf = toString f
      si | length i > pr = ell ++ toString (take pr i)
         | otherwise = toString (take pr i)
      toString = intercalate sep . map showD . reverse
      showD = show . unMod
      clean s = case dropWhile (== 0) (reverse s) of
        [] -> [0]
        x -> reverse x
      ell = "…" ++ sep
      sep
        | radix n < 11 = ""
        | otherwise = " "

instance Radix p prec => Padic (Q' p prec) where
  type Unit (Q' p prec) = Z' p prec
  type Lifted (Q' p prec) = Integer
  type Digit (Q' p prec) = Digit (Z' p prec)

  {-# INLINE precision #-}
  precision = fromIntegral . natVal

  {-# INLINE  radix #-}
  radix (Q' (u, _)) = radix u

  {-# INLINE digits #-}
  digits (Q' (u, v)) = replicate v 0 ++ toRadix (lifted u)

  {-# INLINE fromDigits #-}
  fromDigits ds = normalize $ Q' (fromDigits ds, 0)

  {-# INLINE lifted #-}
  lifted (Q' (u, _)) = lifted u

  {-# INLINE mkUnit #-}
  mkUnit ds = normalize $ Q' (mkUnit ds, 0)

  {-# INLINE fromUnit #-}
  fromUnit = Q'

  splitUnit (Q' (u, v)) = (u, v)
  
  isInvertible = isInvertible . unit . normalize
  
  inverse n = do r <- inverse (unit n)
                 return $ fromUnit (r, - valuation n)


{- | Adjusts unit and valuation of p-adic number, by removing trailing zeros from the right-side of the unit.

Examples:

>>> λ> x = 2313 + 1387 :: Q 10
>>> x
3700.0
>>> splitUnit x
(3700,0)
>>> splitUnit (normalize x)
(37,2) -}
normalize :: Radix p prec => Q' p prec -> Q' p prec
normalize n@(Q' (0, _)) = Q' (0, precision n)
normalize n@(Q' (u, v)) = go (lifted u) v
  where
    go _ k | k >= pr = zero
    go d k = case getUnitZ p d of
      (0, 0) -> zero
      (d', k')
        | k + k' >= pr -> zero
        | otherwise ->
          let s = p ^ fromIntegral k'
          in fromUnit (mkUnit d', k + k')
    p = radix u
    pr = precision n
    zero = Q' (0, pr)

instance Radix p prec => Eq (Q' p prec) where
  a' == b' =
    (isZero a && isZero b)
    || (valuation a == valuation b && unit a == unit b)
    where
      a = normalize a'
      b = normalize b'

instance Radix p prec => Ord (Q' p prec) where
  compare = error "Order is nor defined for p-adics."

instance Radix p prec => Num (Q' p prec) where
  fromInteger n = normalize $ Q' (fromInteger n, 0)
          
  x@(Q' (Z' (R a), va)) + Q' (Z' (R b), vb) =
    case compare va vb of
      LT -> Q' (Z' (R (a + p ^% (vb - va) * b)), va)
      EQ -> Q' (Z' (R (a + b)), va)
      GT -> Q' (Z' (R (p ^% (va - vb) * a + b)), vb)
    where
      p = fromInteger (radix x)
      
  Q' (Z' (R a), va) * Q' (Z' (R b), vb) = Q' (Z' (R (a * b)), va + vb)
      
  negate (Q' (u, v)) = Q' (negate u, v)
  abs = id
  signum 0 = 0
  signum _ = 1

instance Radix p prec => Fractional (Q' p prec) where
  fromRational 0 = 0
  fromRational x = res
    where
      res = Q' (n `div` d, v)
      p = radix res
      (q, v) = getUnitQ p x
      (n, d) = (mkUnit $ numerator q, mkUnit $ denominator q)
  a / b = Q' (res, valuation a - valuation b')
    where
      b' = normalize b
      res
        | isInvertible b' = unit a `div` unit b'
        | otherwise = 
          error $ show b' ++ " is indivisible in " ++ show (radix a) ++ "-adics!"

instance Radix p prec => Real (Q' p prec) where
  toRational n = toRational (unit n) / norm n
