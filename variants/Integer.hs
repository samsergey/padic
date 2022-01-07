{-# OPTIONS_HADDOCK hide, prune, ignore-exports #-}

{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE MagicHash #-}
{-# LANGUAGE UnboxedTuples #-}
{-# LANGUAGE UnliftedFFITypes #-}

module Math.NumberTheory.Padic.Integer where

import Data.List
import Data.Mod
import Data.Ratio
import Data.Maybe (listToMaybe)
import GHC.TypeLits hiding (Mod)
import GHC.Integer.GMP.Internals (recipModInteger)

import Math.NumberTheory.Padic.Classes

------------------------------------------------------------

-- |  Integer p-adic number (an element of \(\mathbb{Z}_p\)) with 20 digits precision.
type Z p = Z' p 20

-- |  Integer p-adic number with explicitly specified precision.
newtype Z' (p :: Nat) (prec :: Nat) = Z' (Z_ p)

newtype Z_ (p :: Nat) = Z_ Integer

instance (Radix p, KnownNat prec) => Show (Z' p prec) where
  show 0 = "0"
  show n  
    | length ds > pr = ell ++ toString (take pr ds)
    | otherwise = toString (take pr ds)
    where
      ds = digits n
      pr = precision n
      toString = intercalate sep . map showD . reverse
      showD = show . unMod 
      ell = "…" ++ sep 
      sep
        | radix n < 11 = ""
        | otherwise = " "

instance (Radix p, KnownNat prec) => Padic (Z' p prec) where
  type Unit (Z' p prec) = Z' p prec
  
  type Digit (Z' p prec) = Mod p 

  precision = fromIntegral . natVal

  fromDigits = mkUnit . fromRadix

  digits n = toRadix (lifted n)

  radix (Z' n) = fromIntegral $ natVal n

  lifted (Z' (Z_ n)) = n

  mkUnit = Z' . Z_

  fromUnit (u, v) = mkUnit $ radix u ^ fromIntegral v * lifted u

  splitUnit n = case getUnitZ (radix n) (lifted n) of
                  (0, 0) -> (0, precision n)
                  (u, v) -> (mkUnit u, v)
  
  isInvertible n = (lifted n `mod` p) `gcd` p == 1
    where
      p = radix n
  
  inverse n
    | isInvertible n = Just (mkUnit $ recipModInteger (lifted n) pk)
    | otherwise = Nothing
    where
      pk = liftedMod n


instance (Radix p, KnownNat prec) => Eq (Z' p prec) where
  x@(Z' (Z_ a)) == (Z' (Z_ b)) = a `mod` pk == b `mod` pk
    where
      pk = radix x ^ precision x

instance (Radix p, KnownNat prec) => Num (Z' p prec) where
  fromInteger n = res
    where
      res = mkUnit $ fromInteger n `mod` liftedMod res
      
  a + b = mkUnit $ (lifted a + lifted b) `mod` liftedMod a
  a * b = mkUnit $ (lifted a * lifted b) `mod` liftedMod a 
  negate a = mkUnit $ liftedMod a - lifted a
  abs = id
  signum _ = 1

instance (Radix p, KnownNat prec) => Enum (Z' p prec) where
  toEnum = fromIntegral
  fromEnum = fromIntegral . toInteger

instance (Radix p, KnownNat prec) => Real (Z' p prec) where
  toRational 0 = 0
  toRational n = extEuclid (lifted n, liftedMod n)

instance (Radix p, KnownNat prec) => Integral (Z' p prec) where
  toInteger n = if denominator r == 1
                then numerator r
                else lifted n `mod` (radix n ^ precision n)
    where
      r = toRational n
  a `quotRem` b = case inverse b of
    Nothing -> error "not divisible!" 
    Just r -> let q = a*r in (q, a - q * b)


instance (Radix p, KnownNat prec) => Ord (Z' p prec) where
  compare = error "ordering is not defined for Z"

------------------------------------------------------------
------------------------------------------------------------

-- | For a given list extracts prefix and a cycle, limiting length of prefix and cycle by @len@.
-- Uses the modified tortiose and hare method.
findCycle :: Eq a => Int -> [a] -> Maybe ([a], [a])
findCycle len lst =
  case tortoiseHare rest of
    Just (a, c) -> test $ clean $ rollback (pref ++ a, c)
    Nothing -> Nothing
  where
    (pref, rest) = splitAt 1 lst
    tortoiseHare x =
      fmap (fmap fst) . listToMaybe $
      dropWhile (\(_, (a, b)) -> notCycle a b) $
      zip (inits x) $
      zipWith splitAt [1 .. len] $ zipWith take [4,8 ..] $ tails x
    notCycle a b = not (concat (replicate 2 a) == b)
    rollback (as, bs) = go (reverse as, reverse bs)
      where
        go =
          \case
            ([], ys) -> ([], reverse ys)
            (x:xs, y:ys)
              | x == y -> go (xs, ys ++ [x])
            (xs, ys) -> (reverse xs, reverse ys)
    clean =
      \case
        (x, c:cs)
          | length x + length cs > len -> (take len (x ++ c : cs), [])
          | all (c ==) cs -> (x, [c])
        other -> other
    test (_, []) = Nothing 
    test (pref, c)
      | and $ zipWith (==) (take (2*len) lst) (pref ++ cycle c) = Just (pref, c)
      | otherwise = Nothing

extEuclid :: Integral i => (Integer, Integer) -> Ratio i
extEuclid (n, m) = go (m, 0) (n, 1)
  where
    go (v1, v2) (w1, w2)
      | 2*w1*w1 > abs m =
        let q = v1 `div` w1
         in go (w1, w2) (v1 - q * w1, v2 - q * w2)
      | otherwise = fromRational (w1 % w2)

-- | Extracts p-adic unit from integer number. For radix \(p\) and integer \(n\) returns
-- pair \((u, k)\) such that \(n = u \cdot p^k\).
--
-- Examples:
-- 
-- >>> getUnitQ 3 (75/157)
-- (1,25 % 157)
-- >>> getUnitQ 5 (75/157)
-- (2,3 % 157)
-- >>> getUnitQ 157 (75/157)
-- (-1,75 % 1)
getUnitZ :: Integer -> Integer -> (Integer, Int)
getUnitZ _ 0 = (0, 0)
getUnitZ p x = (b, length v)
  where
    (v, b:_) = span (\n -> n `mod` p == 0) $ iterate (`div` p) x


-- | Unfolds a number to a list of digits (integers modulo @p@).  
toRadix :: (Integral i, Radix p) => i -> [Mod p]
toRadix 0 = [0]
toRadix n = res
  where
    res = unfoldr go n
    p = fromIntegral $ natVal $ head $ 0 : res
    go 0 = Nothing
    go x =
      let (q, r) = quotRem x p
       in Just (fromIntegral r, q)
  
-- | Folds a list of digits (integers modulo @p@) to a number.
fromRadix :: (Integral i, Radix p) => [Mod p] -> i
fromRadix ds = foldr (\x r -> fromIntegral (unMod x) + r * p) 0 ds
  where
    p = fromIntegral $ natVal $ head $ 0 : ds

