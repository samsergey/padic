{-# OPTIONS_HADDOCK hide, prune, ignore-exports #-}

{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE DerivingVia #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE UndecidableInstances #-}

module Math.NumberTheory.Padic.Rational where

import Data.List (intercalate)
import Data.Ratio
import Data.Word (Word32)
import Data.Mod
import GHC.TypeLits hiding (Mod)
import Math.NumberTheory.Padic.Classes
import Math.NumberTheory.Padic.Integer

------------------------------------------------------------
-- |  Rational p-adic number (an element of \(\mathbb{Q}_p\)) with default 20-digit precision.
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
    
instance Radix p prec => PadicNum (Q' p prec) where
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

  splitUnit n@(Q' (u, v)) =
    let pr = precision n
        (u', v') = splitUnit u
    in if v + v' > pr then (0, pr) else (u', v + v')     
  
  isInvertible = isInvertible . unit . normalize
  
  inverse n = do r <- inverse (unit n)
                 return $ fromUnit (r, - valuation n)


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



{-
instance Radix p prec => Floating (Z p prec) where
  pi = undefined
  exp = pExp
-}
