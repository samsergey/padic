{-# OPTIONS_HADDOCK hide, prune, ignore-exports #-}

{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE MagicHash #-}
{-# LANGUAGE UnboxedTuples #-}
{-# LANGUAGE UnliftedFFITypes #-}

module Math.NumberTheory.Padic.IntegerBN where

import Data.List
import Data.Mod
import Data.Ratio
import Data.Maybe (listToMaybe)
import GHC.TypeLits hiding (Mod)
import GHC.Integer.GMP.Internals
import GHC.Natural
import GHC.Prim (int2Word#)

import Math.NumberTheory.Padic.Classes

------------------------------------------------------------

-- |  Integer p-adic number (an element of \(\mathbb{Z}_p\)) with 20 digits precision.
type Z p = Z' p 20

-- |  Integer p-adic number with explicitly specified precision.
newtype Z' (p :: Nat) (prec :: Nat) = Z' (Z# p)

newtype Z# (p :: Nat) = Z# BigNat

instance (Radix p, KnownNat prec) => Show (Z' p prec) where
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
  type Lifted (Z' p prec) = BigNat
  type Digit (Z' p prec) = Mod p 

  precision = fromIntegral . natVal

  fromDigits = mkUnit . fromRadix#

  digits n = toRadix# (lifted n)

  radix (Z' n) = fromIntegral $ natVal n

  lifted (Z' (Z# n)) = n

  mkUnit = Z' . Z#

  fromUnit (u, v) = mkUnit $ (radix# u `powBigNat` v) `timesBigNat` lifted u

  splitUnit n = case getUnit# (radix# n) (lifted n) of
                  (u, v)
                    | isZeroBigNat u -> (mkUnit zeroBigNat, precision n)
                    | otherwise -> (mkUnit u, v)

  isInvertible n = (lifted n `remBigNat` p) `gcdBigNat` p == oneBigNat
    where
      p = radix# n
  
  inverse n
    | isInvertible n = Just (mkUnit $ recipModBigNat (lifted n) pk)
    | otherwise = Nothing
    where
      pk = liftedMod# n

powBigNat :: BigNat -> Int -> BigNat
powBigNat _ 0 = oneBigNat
powBigNat n 1 = n
powBigNat n 2 = sqrBigNat n
powBigNat n k | odd k = n `timesBigNat` powBigNat n (k - 1)
              | otherwise = powBigNat (sqrBigNat n) (k `div` 2) 

liftedMod# n = radix# n `powBigNat` (2*precision n + 1)

instance (Radix p, KnownNat prec) => Eq (Z' p prec) where
  x@(Z' (Z# a)) == (Z' (Z# b)) = a `remBigNat` pk == b `remBigNat` pk
    where
      pk = radix# x `powBigNat` precision x

instance (Radix p, KnownNat prec) => Num (Z' p prec) where
  fromInteger n = res
    where
      res = case n of
        S# i# -> mkUnit $ wordToBigNat (int2Word# i#) `remBigNat` liftedMod# res
        Jp# x# -> mkUnit $ x# `remBigNat` liftedMod# res
        Jn# x# -> negate $ mkUnit $ x# `remBigNat` liftedMod# res
      
  x@(Z' (Z# a)) + Z' (Z# b) = mkUnit $ (a `plusBigNat` b) `remBigNat` liftedMod# x
  x@(Z' (Z# a)) * Z' (Z# b) = mkUnit $ (a `timesBigNat` b) `remBigNat` liftedMod# x 
  negate x@(Z' (Z# a)) = mkUnit $ liftedMod# x `minusBigNat` (a `remBigNat` liftedMod# x)
  abs = id
  signum _ = 1

instance (Radix p, KnownNat prec) => Enum (Z' p prec) where
  toEnum = fromIntegral
  fromEnum = fromIntegral . toInteger


instance (Radix p, KnownNat prec) => Real (Z' p prec) where
  toRational 0 = 0
  toRational n = extEuclid (bigNatToInteger (lifted n), liftedMod n)

extEuclid :: Integral i => (Integer, Integer) -> Ratio i
extEuclid (n, m) = go (m, 0) (n, 1)
  where
    go (v1, v2) (w1, w2)
      | 2*w1*w1 > abs m =
        let q = v1 `div` w1
         in go (w1, w2) (v1 - q * w1, v2 - q * w2)
      | otherwise = fromRational (w1 % w2)


instance (Radix p, KnownNat prec) => Integral (Z' p prec) where
  toInteger n = if denominator r == 1
                then numerator r
                else bigNatToInteger (lifted n) `mod` (radix n ^ precision n)
    where
      r = toRational n
  a `quotRem` b = case inverse b of
    Nothing -> error "not divisible!" 
    Just r -> let q = a*r in (q, a - q * b)

instance (Radix p, KnownNat prec) => Ord (Z' p prec) where
  compare = error "ordering is not defined for Z"
{-
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


-}

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
getUnit# :: BigNat -> BigNat -> (BigNat, Int)
getUnit# p x
  | isZeroBigNat x = (zeroBigNat, 0)
  | otherwise = (b, length v)
  where
    (v, b:_) = span (\n -> isZeroBigNat (n `remBigNat` p)) $ iterate (`quotBigNat` p) x

fromRadix# :: Radix p => [Mod p] -> BigNat
fromRadix# ds = foldr go zeroBigNat ds
  where
    p# = case fromIntegral $ natVal $ head $ 0 : ds of
      NatJ# x -> x
      NatS# x -> wordToBigNat x
    go x r# = let n# = case unMod x of
                         NatJ# y -> y
                         NatS# y -> wordToBigNat y
              in n# `plusBigNat` (r# `timesBigNat` p#)


toRadix# :: Radix p => BigNat -> [Mod p]
toRadix# n = res
  where
    res = unfoldr go n
    p# = radix# (head (0 : res))
    go x | isZeroBigNat x = Nothing
         | otherwise = let (# q, r #) = quotRemBigNat x p#
                       in Just (fromIntegral (NatJ# r), q)

radix# n = case fromIntegral (natVal n) of
      NatJ# x -> x
      NatS# x -> wordToBigNat x
