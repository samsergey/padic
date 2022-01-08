{-# OPTIONS_HADDOCK hide, prune, ignore-exports #-}

{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE DerivingVia #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE UndecidableInstances #-}

module Math.NumberTheory.Padic.Rational
  ( Q
  , Q'
  , normalize
  ) where

import Data.List (intercalate)
import Data.Ratio
import Data.Mod
import GHC.TypeLits hiding (Mod)
import Math.NumberTheory.Padic.Classes
import Math.NumberTheory.Padic.Integer

------------------------------------------------------------

-- |  Rational p-adic number (an element of \(\mathbb{Q}_p\)) with 20 digits precision.
type Q p = Q' p 20

-- |  Rational p-adic number with explicitly specified precision.
newtype Q' (p :: Nat) (prec :: Nat) = Q' (Z' p prec, Int)

instance Radix p prec => Show (Q' p prec) where
  show n = si ++ sep ++ "." ++ sep ++ sf
    where
      k = valuation n
      pr = precision n
      ds = digits (unit n)
      (f, i) =
        case compare k 0 of
          EQ -> ([0], ds)
          GT -> ([0], replicate k 0 ++ ds)
          LT -> splitAt (-k) ds
      sf = intercalate sep $ showD <$> reverse f
      si =
        case findCycle pr i of
          Nothing -> ell ++ toString (take pr i)
          Just ([], [0]) -> "0"
          Just (pref, [0]) -> toString pref
          Just (pref, cyc)
            | length pref + length cyc <= pr ->
              let sp = toString pref
                  sc = toString cyc
               in "(" ++ sc ++ ")" ++ sep ++ sp
            | otherwise -> ell ++ toString (take pr $ pref ++ cyc)
      showD = show . unMod
      toString = intercalate sep . map showD . reverse
      ell = "…" ++ sep
      sep
        | radix n < 11 = ""
        | otherwise = " "
    
instance Radix p prec => Padic (Q' p prec) where
  type Unit (Q' p prec) = Z' p prec
  type Lifted (Q' p prec) = Lifted (Z' p prec)
  type Digit (Q' p prec) = Digit (Z' p prec)

  {-# INLINE precision #-}
  precision = fromIntegral . natVal

  {-# INLINE  radix #-}
  radix (Q' (u, _)) = radix u

  {-# INLINE digits #-}
  digits (Q' (u, v)) = replicate v 0 ++ digits u

  {-# INLINE fromDigits #-}
  fromDigits ds = Q' (fromDigits ds, 0)

  {-# INLINE lifted #-}
  lifted (Q' (u, _)) = lifted u

  {-# INLINE mkUnit #-}
  mkUnit ds = Q' (mkUnit ds, 0)

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
--normalize 0 = 0
normalize n = go (lifted u) v
  where
    (u, v) = splitUnit n
    go _ k | k >= pr = zero
    go (d:ds) k = case getUnitZ p (lifted d) of
      (0, 0) -> go ds (k + ilog p (radix d))
      (d', k')
        | k + k' >= pr -> zero
        | otherwise ->
          let s = fromIntegral (p^k')
          in fromUnit (mkUnit (shiftL s (fromIntegral d':ds)), k + k')
    p = radix n
    pr = precision n
    zero = Q' (0, precision n)

shiftL :: KnownRadix p => Mod p -> [Mod p] -> [Mod p]
shiftL s (d1:d2:ds) =
  let (q, r) = quotRem (lifted d2) (lifted s)
      pk = fromIntegral (radix s `div` lifted s)
  in d1 + fromIntegral r * pk : shiftL s (fromIntegral q : ds)

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
          
  x@(Q' (a, va)) + Q' (b, vb) =
    case compare va vb of
      LT -> Q' (a + p ^ (vb - va) * b, va)
      EQ -> Q' (a + b, va)
      GT -> Q' (p ^ (va - vb) * a + b, vb)
    where
      p = fromInteger (radix x)
      
  Q' (a, va) * Q' (b, vb) = Q' (a * b, va + vb)
      
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
      (n, d) = (fromInteger $ numerator q, fromInteger $ denominator q)
  a / b = Q' (res, valuation a - valuation b')
    where
      b' = normalize b
      res
        | isInvertible b' = unit a `div` unit b'
        | otherwise = 
          error $ show b' ++ " is indivisible in " ++ show (radix a) ++ "-adics!"

instance Radix p prec => Real (Q' p prec) where
  toRational n = toRational (unit n) / norm n

pExp x | fromRational (norm x) < p ** (-1/(p-1)) = error "eExp does not converge!"
       | otherwise = go 1000 0 1 1
  where
    p = fromIntegral (radix x)
    go n s t i
      | n <= 0 = s -- error "eExp failed to converge within precision!"
      | valuation t' > precision x = s
      | otherwise = go (n - 1) (s + t) t' (i+1)
      where t' = t*x/i


{-
instance Radix p prec => Floating (Z' p prec) where
  pi = undefined
  exp = pExp
-}
