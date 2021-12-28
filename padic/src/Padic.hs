{-# LANGUAGE BangPatterns #-}
{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE DerivingVia #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE UndecidableInstances #-}

-- |
-- Module      : Padic
-- Description : Representation a nd simple algebra for p-adic numbers.
-- Copyright   : (c) Sergey Samoylenko, 2021
-- License     : GPL-3
-- Maintainer  : samsergey@yandex.ru
-- Stability   : experimental
-- Portability : POSIX
--
-- Module introduces p-adic integers \(\mathbb{Z}_p\) and p-adic rational numbers \(\mathbb{Q}_p\)
-- of arbitratry precision, implementing basic arithmetic as well as some specific functions,
-- i.e. detection of periodicity in digital sequence, rational reconstruction, square roots etc.
--
-- The radix \(p\) of a p-adic number is specified at a type level via type-literals. In order to use them GHCi should be loaded with '-XDataKinds' extension.
--
-- >>> :set -XDataKinds
-- >>> 45 :: Z 10
-- 45
-- >>> 45 :: Q 5
-- 140.0
--
-- Negative p-adic integers and rational p-adics have trailing periodic digit sequences, which are represented in parentheses.
--
-- >>> -45 :: Z 7
-- (6)04
-- >>> 1/7 :: Q 10
-- (285714)3.0
--
--
-- The working precision of all p-adics is effetively infinite. However for textual output and rational reconstruction some finite precision should be specified. 
--
-- Rational decomposition is done using a method from Paul S. Wang. 
-- For a truncated p-adic number \(x = \frac{r}{s}\) the equation
-- \( x \cdot s \equiv r\ (\mathrm{mod}\ p^k)\) is solved by extended Euclidean method.
-- The power \(k\) depends on the specifiied precision of a p-adic number and affects the upper bounds of numerator and denominator of the reconstructed rational.
--  
------------------------------------------------------------

module Padic
  (
  -- * Classes and functions
  -- ** Type synonyms and constraints
    ValidRadix
  , LiftedRadix
  , Lifted
  , LiftedDigits
  , Radix
  -- ** Digital objects 
  , Digital
  , Digits
  , radix
  , digits
  , fromDigits
  -- ** p-adic numbers 
  , Padic
  , Unit
  , precision
  , splitUnit
  , unit
  , valuation
  , norm
  , liftedDigits
    -- * Data types
    -- ** p-Adic integers
  , Z
  , Z'
   -- ** p-Adic rationals
  , Q
  , Q'
  -- | * Functions and utilities.
  , firstDigit
  , isDivisible
  , divMaybe
  , fromRadix
  , toRadix
  ) where

import Data.Constraint (Constraint)
import Data.List
import Data.Maybe (listToMaybe)
import Data.Mod
import Data.Ratio
import GHC.Prim (coerce)
import GHC.TypeLits hiding (Mod)

------------------------------------------------------------
-- | Constraint for non-zero natural number which can be a radix.
type family ValidRadix (m :: Nat) :: Constraint where
  ValidRadix 0 = TypeError ('Text "Zero radix!")
  ValidRadix 1 = TypeError ('Text "Radix should be more then 1!")
  ValidRadix m = ()

-- | Naive type-level log function.
type family Lg p n where
  Lg 1 _ = TypeError ('Text "Radix should be more then 1!")
  Lg 2 n = Log2 n
  Lg p 0 = 0
  Lg p n = Lg p (Div n p) + 1

-- | Constraint for valid radix of a number
type Radix m
   = ( ValidRadix m
     , KnownNat m
     , KnownNat (LiftedRadix m)
     , ValidRadix (LiftedRadix m))

------------------------------------------------------------
-- | Typeclass for digitally representable objects
class Digital n where
  -- | A type for digit or a list of digits.
  type Digits n
  -- | Constructor for a digital object from it's digits
  fromDigits :: Digits n -> n
  -- | Returns digits of a digital object
  --
  -- >>> take 5 $ digits (123 :: Z 10)
  -- [(3 `modulo` 10),(2 `modulo` 10),(1 `modulo` 10),(0 `modulo` 10),(0 `modulo` 10)]
  -- >>> take 5 $ digits (-123 :: Z 2)
  -- [(1 `modulo` 2),(0 `modulo` 2),(1 `modulo` 2),(0 `modulo` 2),(0 `modulo` 2)]
  digits :: n -> Digits n
  -- | Returns the radix of a number
  --
  -- >>> radix (5 :: Z 13)
  -- 13
  radix :: Integral i => n -> i

instance (KnownNat p, ValidRadix p) => Digital (Mod p) where
  type Digits (Mod p) = Mod p
  digits = id
  fromDigits = id
  radix = fromIntegral . natVal

------------------------------------------------------------
-- | Typeclass for p-adic numbers
class Digital n => Padic n where
  -- | A type for p-adic unit.
  type Unit n 
  type LiftedDigits n
  -- | Returns the precision of a number.
  --
  -- >>> precision (123 :: Z 2)
  -- 20
  -- >>> precision (123 :: Z' 2 40)
  -- 40
  precision :: Integral i => n -> i
  -- | Returns valuation and unit of a number.
  splitUnit :: n -> (Unit n, Int)
  -- | Adjusts unit and valuation of number removing leading zeros from the unit.
  normalize :: n -> n
  -- | Returns lifted digits
  -- 
  -- >>> take 3 $ liftedDigits (123 :: Z 10)
  -- [(123 `modulo` 10000000000000000000),(0 `modulo` 10000000000000000000),(0 `modulo` 10000000000000000000)]
  -- >>> take 3 $ liftedDigits (-123 :: Z 2)
  -- [(9223372036854775685 `modulo` 9223372036854775808),(9223372036854775807 `modulo` 9223372036854775808),(9223372036854775807 `modulo` 9223372036854775808)]
  liftedDigits :: n -> LiftedDigits n

-- | returns the unit of a number
--
-- >>> unit (120 :: Z 10)
-- 12
-- >>> unit (75 :: Z 5)
-- 3
unit :: Padic n => n -> Unit n
unit = fst . splitUnit

-- | returns a valuation  of a number
--
-- >>> valuation (120 :: Z 10)
-- 1
-- >>> valuation (75 :: Z 5)
-- 2
valuation :: Padic n => n -> Int
valuation = snd . splitUnit

-- | returns a rational norm of a number
--
-- >>> norm (120 :: Z 10)
-- 0.1
-- >>> norm (75 :: Z 5)
-- 4.0e-2
norm :: (Fractional f, Padic n) => n -> f
norm n = fromIntegral (radix n) ^^ (-valuation n)

equiv :: (Padic n, Eq (Unit n)) => n -> n -> Bool
equiv a b =
  (isZero a && isZero b) || (valuation a == valuation b && unit a == unit b)

isZero :: Padic n => n -> Bool
isZero n = valuation n >= precision n

------------------------------------------------------------
-- |
-- In order to gain efficiency the p-adic number is internally
-- represented as an infinite list of /lifted/ digits modulo \(p^k\), where \(k\) is
-- chosen so that each lifted digit fits in a 'Word'. 
--
-- \[
-- x = ...ddddddddddddddd_{(p)} =  ... \underbrace{ddddd}_k\,\underbrace{ddddd}_k\,\underbrace{ddddd}_k{}_{(p^k)}
-- \]
--
-- Sequence of digits modulo \(p\) are used mainly for textual representation and may be obtained by 'digits' function.
type LiftedRadix p = p ^ (Lg p (2 ^ 64) - 1)

-- | A wrapper for a fifted digit.
newtype Lifted p = Lifted { getLifted :: Mod (LiftedRadix p)}  

deriving via Mod (LiftedRadix p) instance Radix p => Show (Lifted p)

deriving via Mod (LiftedRadix p) instance Radix p => Eq (Lifted p)

deriving via Mod (LiftedRadix p) instance Radix p => Ord (Lifted p)

deriving via Mod (LiftedRadix p) instance Radix p => Num (Lifted p)

deriving via Mod (LiftedRadix p) instance
         Radix p => Enum (Lifted p)

deriving via Mod (LiftedRadix p) instance
         Radix p => Digital (Lifted p)

instance Radix p => Real (Lifted p) where
  toRational = undefined

instance Radix p => Integral (Lifted p) where
  toInteger = fromIntegral . unMod . getLifted
  quotRem = undefined

------------------------------------------------------------
-- | Alias for an infinite list of lifted digits
--type LiftedDigits' p = [Lifted p]

-- |  Integer p-adic number with 20 digits precision
newtype Z p = Z [Lifted p]

deriving via (Z' p 20) instance Radix p => Eq (Z p)

deriving via (Z' p 20) instance Radix p => Ord (Z p)

deriving via (Z' p 20) instance Radix p => Show (Z p)

deriving via (Z' p 20) instance Radix p => Real (Z p)
deriving via (Z' p 20) instance Radix p => Enum (Z p)

deriving via (Z' p 20) instance Radix p => Integral (Z p)

deriving via (Z' p 20) instance Radix p => Padic (Z p)

instance Radix p => Digital (Z p) where
  type Digits (Z p) = [Mod p]
  radix = fromIntegral . natVal
  digits (Z n) = unliftDigits n
  fromDigits = Z . liftDigits

liftDigits :: Radix p => Digits (Z p) -> LiftedDigits (Z p)
liftDigits ds = res
   where
     res = unfoldr go ds
     go xs =
       let (a, r) = splitAt (ilog p pk) xs
        in Just (fromIntegral $ fromRadix p (unMod <$> a), r)
     p = radix (head ds)
     pk = radix (head res)

unliftDigits :: Radix p => LiftedDigits (Z p) -> Digits (Z p)
unliftDigits ds = res
  where
    res = concatMap (take (ilog p pk) . expand) (unMod . getLifted <$> ds)
    expand d = fromIntegral <$> (toRadix p d ++ repeat 0)
    p = radix (head res)
    pk = radix (head ds)

ilog :: (Integral b, Integral a, Integral a) => a -> a -> b
ilog a b = floor (logBase (fromIntegral a) (fromIntegral b))

instance Radix p => Num (Z p) where
  fromInteger n
    | n < 0 = -fromInteger (-n)
    | otherwise = Z $ d : ds
    where
      d:ds = toRadix (radix d) n ++ repeat 0
  abs = id
  signum 0 = 0
  signum _ = 1
  Z a + Z b = Z $ addZ a b
  Z a * Z b = Z $ mulZ a b
  negate (Z a) = Z $ negZ a

toRadix :: (Integral i, Integral d) => i -> i -> [d]
toRadix _ 0 = [0]
toRadix b n = unfoldr go n
  where
    go 0 = Nothing
    go x =
      let (q, r) = quotRem x b
       in Just (fromIntegral r, q)

fromRadix :: (Integral i, Integral d) => i -> [d] -> i
fromRadix b = foldr (\x r -> fromIntegral x + r * b) 0

negZ :: Radix p => [Lifted p] -> [Lifted p]
negZ = go
  where
    go (0:t) = 0 : go t
    go (h:t) = -h : map (\x -> -x - 1) t

carry :: (Integral a, Digital b, Num b) => a -> (a, b)
{-# INLINE carry #-}
carry n =
  let d = fromIntegral n
   in (n `div` radix d, d)

addZ :: Radix p => [Lifted p] -> [Lifted p] -> [Lifted p]
{-# INLINE addZ #-}
addZ a b = snd $ mapAccumL step 0 $ zip a b
  where
    step r (x, y) = carry (fromIntegral x + fromIntegral y + r)

mulZ :: Radix p => [Lifted p] -> [Lifted p] -> [Lifted p]
{-# INLINE mulZ #-}
mulZ a = go
  where
    go (b:bs) = addZ (go bs) `apTail` scaleZ b a
    apTail f (h:t) = h : f t

scaleZ :: Radix p => Lifted p -> [Lifted p] -> [Lifted p]
{-# INLINE scaleZ #-}
scaleZ s =
  snd . mapAccumL (\r x -> carry (fromIntegral s * fromIntegral x + r)) 0

-- | Division which does not raize exceptions.
divMaybe :: Radix p => Z p -> Z p -> Maybe (Z p)
divMaybe (Z a) (Z b) = Z <$> divZ a b

divZ :: Radix p => [Lifted p] -> [Lifted p] -> Maybe ([Lifted p])
divZ a (b:bs) = go a <$ invert b
  where
    Just r = invert b
    go (0:xs) = 0 : go xs
    go xs =
      let m = head xs * r
          mulAndSub = addZ xs . negZ . scaleZ m
       in m : go (tail $ mulAndSub (b : bs))

invert :: Radix p => Lifted p -> Maybe (Lifted p)
invert (Lifted m) = Lifted <$> invertMod m
  

------------------------------------------------------------
-- |  Integer p-adic number with explicitly specified precision
newtype Z' (p :: Nat) (prec :: Nat) =
  Z' (Z p)

deriving via Z p instance Radix p => Digital (Z' p prec)

deriving via Z p instance Radix p => Num (Z' p prec)

instance (KnownNat prec, Radix p) => Padic (Z' p prec) where
  type Unit (Z' p prec) = Z' p prec
  type LiftedDigits (Z' p prec) = [Lifted p]
  precision = fromIntegral . natVal
  splitUnit n = go prec (digits n)
    where
      prec = precision n
      go 0 _ = (fromDigits $ repeat 0, maxBound)
      go k xs =
        case xs of
          0:ds -> go (k - 1) ds
          _ -> (fromDigits xs, prec - k)
  normalize = id
  liftedDigits (Z' (Z ds)) = ds

instance (KnownNat prec, Radix p) => Eq (Z' p prec) where
  a == b = and $ take pr $ zipWith (==) (digits a) (digits b)
    where
      pr = precision a

instance (KnownNat prec, Radix p) => Ord (Z' p prec) where
  compare = error "ordering is not defined for Z"

instance (KnownNat prec, Radix p) => Show (Z' p prec) where
  show 0 = "0"
  show n =
    case findCycle pr (digits n) of
      (pref, []) -> "…" ++ toString pref
      (pref, [0]) -> toString pref
      (pref, cyc)
        | length pref + length cyc <= pr ->
          let sp = toString pref
              sc = toString cyc
           in "(" ++ sc ++ ")" ++ sep ++ sp
        | otherwise -> "…" ++ toString (take pr $ pref ++ cyc)
    where
      pr = precision n
      showD = show . unMod
      toString = intercalate sep . map showD . reverse
      sep
        | radix n < 11 = ""
        | otherwise = " "

instance (KnownNat prec, Radix p) => Enum (Z' p prec) where
  toEnum = fromIntegral
  fromEnum = fromIntegral . toInteger


instance (KnownNat prec, Radix p) => Integral (Z' p prec) where
  toInteger n =
    case findCycle prec ds of
      (xs, [t])
        | t == 0 -> fromRadix p xs
        | t == (p - 1) -> fromRadix p ((+ (1 - p)) <$> xs) - 1
      _ -> fromRadix p (take prec ds)
    where
      prec = precision n
      p = radix n
      ds = map (fromIntegral . unMod) $ digits n
  div (Z' a) d@(Z' b) =
    case divMaybe a b of
      Just r -> Z' r
      Nothing ->
        error $ show d ++ " is indivisible in " ++ show (radix d) ++ "-adics!"
  quot = div
  quotRem = error "modular arithmetic is not defined for p-adics!"

findCycle :: Eq a => Int -> [a] -> ([a], [a])
findCycle len lst =
  case turlteHare rest of
    Just (a, c) -> clean $ rollback (pref ++ a, c)
    Nothing -> (pref, [])
  where
    (pref, rest) = splitAt len lst
    turlteHare x =
      fmap (fmap fst) . listToMaybe $
      dropWhile (\(_, (a, b)) -> isCycle a b) $
      zip (inits x) $
      zipWith splitAt [1 .. len] $ zipWith take [4,8 ..] $ tails x
    isCycle a b = concat (replicate 3 a) /= b
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

instance (KnownNat prec, Radix p) => Real (Z' p prec) where
  toRational 0 = 0
  toRational x@(Z' (Z ds)) = ratDecomposition n m
    where
      prec = precision x
      p = radix x
      pk = radix (head ds)
      m = p ^ (2*prec)
      n = fromRadix pk (take (ilog pk m + 1) (unMod . getLifted <$> ds))
  
ratDecomposition :: Integer -> Integer -> Rational
ratDecomposition n m = go (m,0) (n,1)
  where
    go (v1, v2) (w1, w2)
      | w1 > isqrt m = let q = v1 `div` w1
                       in go (w1, w2) (v1 - q*w1, v2 - q*w2)
      | otherwise = w1 % w2

isqrt :: (Integral b, Integral a) => a -> b
isqrt n = floor (sqrt (fromIntegral n))
  
------------------------------------------------------------
------------------------------------------------------------
-- |  Rational p-adic number with 20 digits precision.
data Q (p :: Nat)
  = Zero
  | Q Int (Z p)

-- |  Rational p-adic number with explicitly given precision.
newtype Q' (p :: Nat) (prec :: Nat) =
  Q' (Q p)

deriving via Q p instance Radix p => Num (Q' p prec)

deriving via Q p instance Radix p => Fractional (Q' p prec)

deriving via (Q' p 20) instance Radix p => Eq (Q p)

deriving via (Q' p 20) instance Radix p => Ord (Q p)

deriving via (Q' p 20) instance Radix p => Show (Q p)

deriving via (Q' p 20) instance Radix p => Real (Q p)

instance (KnownNat prec, Radix p) => Show (Q' p prec) where
  show (Q' Zero) = "0.0"
  show n = si ++ sep ++ "." ++ sep ++ sf
    where
      pr = precision n
      k = valuation n
      ds = digits (unit n)
      (f, i) =
        case compare k 0 of
          EQ -> ([0], ds)
          GT -> ([0], replicate k 0 ++ ds)
          LT -> splitAt (-k) ds
      sf = intercalate sep $ showD <$> reverse f
      si =
        case findCycle pr i of
          ([], [0]) -> "0"
          (pref, []) -> "…" ++ toString pref
          (pref, [0]) -> toString pref
          (pref, cyc)
            | length pref + length cyc <= pr ->
              let sp = toString pref
                  sc = toString cyc
               in "(" ++ sc ++ ")" ++ sep ++ sp
            | otherwise -> "…" ++ toString (take pr $ pref ++ cyc)
      showD = show . unMod
      toString = intercalate sep . map showD . reverse
      sep
        | radix n < 11 = ""
        | otherwise = " "
  
instance Radix p => Digital (Q p) where
  type Digits (Q p) = Digits (Z p)
  radix = fromIntegral . natVal
  digits =
    \case
      Zero -> repeat 0
      (Q v u) -> replicate v 0 ++ digits u
  fromDigits ds = normalize $ Q 0 (fromDigits ds)

instance (KnownNat prec, Radix p) => Digital (Q' p prec) where
  type Digits (Q' p prec) = Digits (Z' p prec)
  radix (Q' n) = radix n
  digits (Q' x) =
    case x of
      Zero -> repeat 0
      (Q v u) -> replicate v 0 ++ digits u
  fromDigits ds = normalize $ Q' (Q 0 (fromDigits ds))

instance Radix p => Padic (Q p) where
  type Unit (Q p) = Z p
  type LiftedDigits (Q p) = [Lifted p]
  precision _ = 20
  splitUnit Zero = (0, 20)
  splitUnit (Q v u) = (u, v)
  normalize Zero = Zero
  normalize n = go 0 (digits (unit n))
    where
      go i _
        | i > 20 = 0
      go i (0:u) = go (i + 1) u
      go i u = Q (valuation n + i) (fromDigits u)
  liftedDigits = liftedDigits . unit

instance (KnownNat prec, Radix p) => Padic (Q' p prec) where
  type Unit (Q' p prec) = Z' p prec
  type LiftedDigits (Q' p prec) = [Lifted p]
  precision = fromIntegral . natVal
  splitUnit n =
    case n of
      (Q' Zero) -> (0, precision n)
      (Q' (Q v u))
        | v > precision n -> (0, precision n)
        | otherwise -> (coerce u, v)
  normalize (Q' Zero) = Q' Zero
  normalize n = Q' $ go 0 (digits n)
    where
      go i _
        | i > precision n = 0
      go i (0:u) = go (i + 1) u
      go i u = Q (valuation n + i) (fromDigits u)
  liftedDigits = liftedDigits . unit

instance (KnownNat prec, Radix p) => Eq (Q' p prec) where
  (==) = equiv

instance (KnownNat prec, Radix p) => Ord (Q' p prec) where
  compare = error "ordering is not defined for Q"

instance Radix p => Num (Q p) where
  fromInteger 0 = Zero
  fromInteger n = normalize $ Q 0 (fromInteger n)
  Zero + a = a
  a + Zero = a
  a + b = normalize $ Q v (p ^ (va - v) * unit a + p ^ (vb - v) * unit b)
    where
      va = valuation a
      vb = valuation b
      v = va `min` vb
      p = radix a
  Zero * _ = Zero
  _ * Zero = Zero
  a * b = normalize $ Q (valuation a + valuation b) (unit a * unit b)
  negate Zero = Zero
  negate (Q v u) = Q v (negate u)
  abs = id
  signum Zero = 0
  signum _ = 1

instance Radix p => Fractional (Q p) where
  fromRational 0 = Zero
  fromRational x = normalize res
    where
      res = Q v (fromDigits (series n))
      p = radix res
      (v, q) = getUnit p x
      (n, d) = (fromIntegral $ numerator q, fromIntegral $ denominator q)
      series 0 = repeat 0
      series n =
        let m = fromIntegral n / fromIntegral d
         in m : series ((n - fromIntegral (unMod m) * d) `div` p)
  a / b = normalize $ Q (valuation a - valuation b) res
    where
      res =
        case divMaybe (unit a) (unit b) of
          Nothing ->
            error $
            show b ++ " is indivisible in " ++ show (radix a) ++ "-adics!"
          Just r -> r

-- extracts p-adic unit from a rational number
getUnit :: Integral i => i -> Ratio i -> (Int, Ratio i)
getUnit p x = (genericLength v2 - genericLength v1, c)
  where
    (v1, b:_) =
      span (\n -> denominator n `mod` p == 0) $ iterate (* fromIntegral p) x
    (v2, c:_) =
      span (\n -> numerator n `mod` p == 0) $ iterate (/ fromIntegral p) b

instance (KnownNat prec, Radix p) => Real (Q' p prec) where
  toRational (Q' Zero) = 0
  toRational n = toRational (unit n) / norm n

-- | Test for divisibility.
isDivisible n = unMod d `gcd` radix d == 1
  where
    d = firstDigit n

-- | The least significant digit of a p-adic number.
firstDigit n = head (digits n)
