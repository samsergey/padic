{-# OPTIONS_HADDOCK hide, prune, ignore-exports #-}

{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE UndecidableInstances #-}

module Math.NumberTheory.Padic.Integer where

import Data.List
import Data.Ratio
import Data.Maybe (listToMaybe, maybeToList)
import GHC.TypeLits

import Math.NumberTheory.Padic.Classes

------------------------------------------------------------

-- |  Integer p-adic number (an element of \(\mathbb{Z}_p\)) with 20 digits precision.
type Z p = Z' p 20

-- |  Integer p-adic number with explicitly specified precision.
newtype Z' (p :: Nat) (prec :: Nat) = Z' (Z_ p)

newtype Z_ (p :: Nat) = Z_ Integer

instance (Radix p, KnownNat prec) => Show (Z' p prec) where
  show 0 = "0"
  show n =  
    case findCycle pr ds of
      Nothing
        | length ds > pr -> ell ++ toString (take pr ds)
        | otherwise -> toString (take pr ds)
      Just (pref, cyc)
        | length pref + length cyc <= pr ->
          let sp = toString pref
              sc = toString cyc
           in "(" ++ sc ++ ")" ++ sep ++ sp
        | otherwise -> ell ++ toString (take pr $ pref ++ cyc)
    where
      ds = digits n
      pr = precision n
      toString = intercalate sep . map show . reverse
      ell = "…" ++ sep 
      sep
        | radix n < 11 = ""
        | otherwise = " "

instance (Radix p, KnownNat prec) => Padic (Z' p prec) where
  type Unit (Z' p prec) = Z' p prec

  precision = fromIntegral . natVal

  fromDigits ds = res
    where
      res = mkUnit $ fromRadix p ds
      p = radix res

  digits n = toRadix (radix n) (lifted n)

  radix (Z' n) = fromIntegral $ natVal n

  lifted (Z' (Z_ n)) = n

  mkUnit = Z' . Z_

  fromUnit (u, v) = mkUnit $ radix u ^ fromIntegral v * lifted u

  splitUnit n = let (u, v) = getUnitZ (radix n) (lifted n)
                in (mkUnit u, v)

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
    (pref, rest) = splitAt (len `div` 2) lst
    tortoiseHare x =
      fmap (fmap fst) . listToMaybe $
      dropWhile (\(_, (a, b)) -> notCycle a b) $
      zip (inits x) $
      zipWith splitAt [1 .. len] $ zipWith take [3,6 ..] $ tails x
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
      | and $ zipWith (==) lst (pref ++ cycle c) = Just (pref, c)
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


-- | Unfolds a number to a list of digits.  
toRadix :: (Integral i, Integral d) => i -> i -> [d]
toRadix _ 0 = [0]
toRadix rad n = unfoldr go n
  where
    go 0 = Nothing
    go x =
      let (q, r) = quotRem x rad
       in Just (fromIntegral r, q)
  
-- | Folds a list of digits to a number.
fromRadix :: (Integral i, Integral d) => i -> [d] -> i
fromRadix rad = foldr (\x r -> fromIntegral x + r * rad) 0
