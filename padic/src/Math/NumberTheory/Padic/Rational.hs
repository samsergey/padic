{-# OPTIONS_HADDOCK hide, prune, ignore-exports #-}

{-# LANGUAGE DataKinds #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE UndecidableInstances #-}

module Math.NumberTheory.Padic.Rational where

import Data.List (intercalate)
import Data.Ratio
import Data.Mod
import Data.Word
import GHC.TypeLits (Nat, natVal)
import Math.NumberTheory.Padic.Types
import Math.NumberTheory.Padic.Analysis
import Math.NumberTheory.Padic.Integer

------------------------------------------------------------

type instance Padic Rational p = Q' p (SufficientPrecision Word p)
type instance Padic (Ratio Int) p = Q' p (SufficientPrecision Int p)
type instance Padic (Ratio Word8) p = Q' p (SufficientPrecision Word8 p)
type instance Padic (Ratio Word16) p = Q' p (SufficientPrecision Word16 p)
type instance Padic (Ratio Word32) p = Q' p (SufficientPrecision Word32 p)
type instance Padic (Ratio Word64) p = Q' p (SufficientPrecision Word64 p)
type instance Padic (Ratio Word) p = Q' p (SufficientPrecision Word64 p)

------------------------------------------------------------
-- |  Rational p-adic number (an element of \(\mathbb{Q}_p\)) with default precision.
type Q p = Q' p (SufficientPrecision Word32 p)

-- |  Rational p-adic number with explicitly specified precision.
data Q' (p :: Nat) (prec :: Nat) = Q' !(Z' p prec) !Int

instance Radix p prec => PadicNum (Q' p prec) where
  type Unit (Q' p prec) = Z' p prec
  type Digit (Q' p prec) = Digit (Z' p prec)

  {-# INLINE precision #-}
  precision = fromIntegral . natVal

  {-# INLINE  radix #-}
  radix (Q' u _) = radix u

  {-# INLINE digits #-}
  digits (Q' u v) = replicate v 0 ++ toRadix (lifted u)

  {-# INLINE fromDigits #-}
  fromDigits ds = normalize $ Q' (fromDigits ds) 0

  {-# INLINE lifted #-}
  lifted (Q' u _) = lifted u

  {-# INLINE mkUnit #-}
  mkUnit ds = normalize $ Q' (mkUnit ds) 0

  {-# INLINE fromUnit #-}
  fromUnit (u, v) = Q' u v

  splitUnit n@(Q' u v) =
    let pr = precision n
        (u', v') = splitUnit u
    in if v + v' > pr then (0, pr) else (u', v + v')     
  
  isInvertible = isInvertible . unit . normalize
  
  inverse n = do r <- inverse (unit n)
                 return $ fromUnit (r, - valuation n)

instance Radix p prec => Show (Q' p prec) where
  show n = si ++ sep ++ "." ++ sep ++ sf
    where
      (u, k) = splitUnit (normalize n)
      pr = precision n 
      ds = digits u
      (f, i) =
        case compare k 0 of
          EQ -> ([0], ds)
          GT -> ([0], replicate k 0 ++ ds)
          LT -> splitAt (-k) (ds ++ replicate (pr + k) 0)
      sf = intercalate sep $ showD <$> reverse f
      si =
        case findCycle pr i of
          Nothing
            | null i -> "0"
            | length i > pr -> ell ++ toString (take pr i)
            | otherwise -> toString i
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
  fromInteger n = normalize $ Q' (fromInteger n) 0
          
  x@(Q' (Z' (R a)) va) + Q' (Z' (R b)) vb =
    case compare va vb of
      LT -> Q' (Z' (R (a + p ^% (vb - va) * b))) va
      EQ -> Q' (Z' (R (a + b))) va
      GT -> Q' (Z' (R (p ^% (va - vb) * a + b))) vb
    where
      p = fromInteger (radix x)
      
  Q' (Z' (R a)) va * Q' (Z' (R b)) vb = Q' (Z' (R (a * b))) (va + vb)
      
  negate (Q' u v) = Q' (negate u) v
  abs = fromRational . norm
  signum = pSignum

newtype Delay prec p = Delay (Q' p prec)

instance Radix p prec => Fractional (Q' p prec) where
  fromRational 0 = 0
  fromRational x = res
    where
      res = Q' (n `div` d) v
      p = fromInteger $ natVal (Delay res)
      (q, v) = getUnitQ p x
      (n, d) = (mkUnit $ numerator q, mkUnit $ denominator q)
  a / b = Q' u (v + valuation a - valuation b')
    where
      b' = normalize b
      Q' u v = fromRational (lifted a % lifted b')

instance Radix p prec => Real (Q' p prec) where
  toRational n = toRational (unit n) / norm n

pUndefinedError s = error $ s ++ " is undifined for p-adics."

fromEither = either error id

instance Radix p prec => Floating (Q' p prec) where
  x ** y = fromEither $ pPow x y
  exp = fromEither . pExp
  log = fromEither . pLog
  sinh = fromEither . pSinh
  cosh = fromEither . pCosh
  sin = fromEither . pSin
  cos = fromEither . pCos
  asinh = fromEither . pAsinh
  acosh = fromEither . pCosh
  atanh = fromEither . pTanh
  asin = fromEither . pAsin
  sqrt x = case pSqrt x of
    res:_ -> res
    [] -> error $ "sqrt: digit " ++ show (firstDigit x) ++ " is not a square residue!"
  pi = pUndefinedError "pi"
  acos = pUndefinedError "acos"
  atan = pUndefinedError "atan"

