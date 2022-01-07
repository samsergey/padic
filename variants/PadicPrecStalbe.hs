{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE DerivingVia #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE MagicHash #-}

-- |
-- Module      : Math.NumberTheory.Padic
-- Description : Representation a nd simple algebra for p-adic numbers.
-- Copyright   : (c) Sergey Samoylenko, 2022
-- License     : GPL-3
-- Maintainer  : samsergey@yandex.ru
-- Stability   : experimental
-- Portability : POSIX
--
-- Module introduces p-adic integers \(\mathbb{Z}_p\) and p-adic rational numbers \(\mathbb{Q}_p\)
-- of arbitratry precision, implementing basic arithmetic as well as some specific functions,
-- i.e. detection of periodicity in sequence of digits, rational reconstruction, computation of square roots etc.
--
-- The radix \(p\) of a p-adic number is specified at a type level via type-literals. In order to use them GHCi should be loaded with a couple of extensions.
--
-- >>> :set -XDataKinds -XTypeOperators
-- >>> 45 :: Z 10
-- 45
-- >>> 45 :: Q 5
-- 140.0
--
-- Digits of p-adic expansion for rational and negative numbers eventually form infinite periodic sequences. 
--
-- >>> -3 :: Z 10
-- (9)7 -- equivalent to ...9999999997
-- >>> 1/15 :: Q 5
-- (13).2 -- equivalent to ...13131313.2
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

module Math.NumberTheory.Padic
  ( 
  -- * Classes and functions
  -- ** Type synonyms and constraints
    ValidRadix
  , LiftedRadix
  , Lifted
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
  , splitUnit
  , unit
  , valuation
  , norm
  , normalize
  , liftedDigits
  -- ** Objects with fixed precision
  , Fixed
  , precision
  , type (%) (..)
    -- * Data types
    -- ** p-Adic integers
  , Z
  , Q
  -- * Functions and utilities
  , firstDigit
  , isInvertible
  , fromRadix
  , toRadix
  , findCycle
  , sufficientPrecision
  , getUnitQ
  , getUnitZ
  ) where

import Data.Constraint (Constraint)
import Data.List
import Data.Maybe (listToMaybe, maybeToList)
import Data.Mod
import Data.Ratio
import GHC.TypeLits hiding (Mod)
import Control.Monad
import GHC.Prim
import GHC.Integer
import GHC.Integer.Logarithms (integerLogBase#)

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

class Fixed a where
  -- | Returns the precision of a number.
  --
  -- Examples:
  -- >>> precision (123 :: Z 2)
  -- 20
  -- >>> precision (123 :: Z' 2 % 40)
  -- 40
  precision :: Integral i => a -> i
  showPrec :: Int -> a -> String
  eqPrec :: Int -> a -> a -> Bool
  
newtype a % (prec :: Nat) = Prec a

instance (KnownNat prec, Fixed a) => Fixed (a % prec) where
  precision = fromIntegral . natVal
  showPrec pr (Prec a) = showPrec pr a
  eqPrec pr (Prec a) (Prec b) = eqPrec pr a b

instance (KnownNat prec, Fixed a) => Show (a % prec) where
  show p@(Prec a) = showPrec (precision p) a

instance (Padic a, KnownNat prec, Num a) => Num (a % prec) where
  fromInteger n = res
    where
      (_, v) = getUnitZ p n
      res | v >= pr = 0
          | otherwise = Prec $ fromInteger n
      pr = precision res
      p = radix res
      
  Prec a + Prec b = Prec (a + b)
  Prec a * Prec b = Prec (a * b)
  Prec a - Prec b = Prec (a - b)
  negate (Prec a) = Prec (negate a)
  abs (Prec a) = Prec (abs a)
  signum (Prec a) = Prec (signum a)

instance (KnownNat prec, Fixed a) => Eq (a % prec) where
  p@(Prec a) == Prec b = eqPrec (precision p) a b
  
instance (KnownNat prec, Fixed a, Ord a) => Ord (a % prec) where
  compare (Prec a) (Prec b) = a `compare` b 
  
instance (KnownNat prec, Enum a) => Enum (a % prec) where
  toEnum = Prec . toEnum
  fromEnum (Prec a) = fromEnum a

instance (KnownNat prec, RealPadic a p) => Real (a % prec) where
  toRational x@(Prec a) = ratDecomposition (precision x) a

instance (KnownNat prec, Integral a, RealPadic a p) => Integral (a % prec) where
  toInteger (Prec a) = toInteger a
  quotRem (Prec a) (Prec b) = let (q, r) = quotRem a b
                              in (Prec q, Prec r)

instance (KnownNat prec, Fractional a, Padic a) => Fractional (a % prec) where
  fromRational = Prec . fromRational
  recip (Prec a) = Prec (recip a)
  Prec a / Prec b = Prec (a / b)

------------------------------------------------------------
-- | Typeclass for digitally representable objects
class Digital n where
  -- | A type for digit or a list of digits.
  type Digits n
  type LiftedDigits n
  -- | Constructor for a digital object from it's digits
  fromDigits :: Digits n -> n
  -- | Returns digits of a digital object
  --
  -- Examples:
  -- >>> take 5 $ digits (123 :: Z 10)
  -- [(3 `modulo` 10),(2 `modulo` 10),(1 `modulo` 10),(0 `modulo` 10),(0 `modulo` 10)]
  -- >>> take 5 $ digits (-123 :: Z 2)
  -- [(1 `modulo` 2),(0 `modulo` 2),(1 `modulo` 2),(0 `modulo` 2),(0 `modulo` 2)]
  -- >>> take 5 $ digits (1/200 :: Q 10)
  -- [(1 `modulo` 2),(0 `modulo` 2),(1 `modulo` 2),(0 `modulo` 2),(0 `modulo` 2)]
  digits :: n -> Digits n
  -- | Returns the radix of a number
  --
  -- Examples:
  -- >>> radix (5 :: Z 13)
  -- 13
  -- >>> radix (-5 :: Q' 3 40)
  -- 3
  radix :: Integral i => n -> i
  -- | Returns lifted digits
  --
  -- Examples:
  -- >>> take 3 $ liftedDigits (123 :: Z 10)
  -- [(123 `modulo` 10000000000000000000),(0 `modulo` 10000000000000000000),(0 `modulo` 10000000000000000000)]
  -- >>> take 3 $ liftedDigits (-123 :: Z 2)
  -- [(9223372036854775685 `modulo` 9223372036854775808),(9223372036854775807 `modulo` 9223372036854775808),(9223372036854775807 `modulo` 9223372036854775808)]
  liftedDigits :: n -> LiftedDigits n
  mkUnit :: LiftedDigits n -> n

instance (KnownNat p, ValidRadix p) => Digital (Mod p) where
  type Digits (Mod p) = Mod p
  type LiftedDigits (Mod p) = Mod p
  digits = id
  fromDigits = id
  radix = fromIntegral . natVal
  liftedDigits = id
  mkUnit = id

instance Digital a => Digital (a % prec) where
  type Digits (a % prec) = Digits a
  type LiftedDigits (a % prec) = LiftedDigits a
  radix (Prec x) = radix x
  digits (Prec x) = digits x
  fromDigits ds = Prec $ fromDigits ds
  liftedDigits (Prec x) = liftedDigits x
  mkUnit ds = Prec $ mkUnit ds

------------------------------------------------------------
type family RealPadic n p :: Constraint where
  RealPadic n p =
    ( Padic n
    , Padic (Unit n)
    , Real n
    , Radix p
    , LiftedDigits n ~ [Lifted p]
    , LiftedDigits (Unit n) ~ [Lifted p]
    )
  
-- | Typeclass for p-adic numbers
class (Num n, Digital n, Fixed n) => Padic n where
  -- | A type for p-adic unit.
  type Unit n
  fromUnit :: (Unit n, Int) -> n
  -- | Returns valuation and unit of a number.
  splitUnit :: n -> (Unit n, Int)
  inverse :: n -> Maybe n
  
-- | returns the unit of a number
--
-- Examples:
-- >>> unit (120 :: Z 10)
-- 12
-- >>> unit (75 :: Z 5)
-- 3
unit :: Padic n => n -> Unit n
unit = fst . splitUnit

-- | returns a valuation  of a number
--
-- Examples:
-- >>> valuation (120 :: Z 10)
-- 1
-- >>> valuation (75 :: Z 5)
-- 2
--
-- Valuation of zero is equal to working precision
--
-- >>> valuation (0 :: Q 2)
-- 20
-- >>> valuation (0 :: Q 2 % 150)
-- 150
valuation :: Padic n => n -> Int
valuation = snd . splitUnit

-- | returns a rational norm of a number
--
-- Examples:
-- >>> norm (120 :: Z 10)
-- 0.1
-- >>> norm (75 :: Z 5)
-- 4.0e-2
norm :: (Fractional f, Padic n) => n -> f
norm n = fromIntegral (radix n) ^^ (-valuation n)

isZero :: Padic n => n -> Bool
isZero n = valuation n >= precision n

instance (KnownNat prec, Padic a, Eq a, Num (Unit a)) => Padic (a % prec) where
  type Unit (a % prec) = Unit a % prec
  fromUnit (Prec u, v) = Prec $ fromUnit (u, v)
  splitUnit x@(Prec 0) = (Prec 0, precision x) 
  splitUnit (Prec a) = (Prec $ unit a, valuation a) 
  inverse (Prec a) = Prec <$> inverse a

------------------------------------------------------------
-- | In order to gain efficiency the p-adic number is internally
-- represented as an infinite list of /lifted/ digits modulo \(p^k\), where \(k\) is
-- chosen so that each lifted digit fits in a 'Word'.
--
-- \[
-- x = ...ddddddddddddddd_{(p)} =  ... \underbrace{ddddd}_k\,\underbrace{ddddd}_k\,\underbrace{ddddd}_k{}_{(p^k)}
-- \]
--
-- Sequence of digits modulo \(p\) are used mainly for textual representation and may be obtained by 'digits' function.
type family LiftedRadix p where
  LiftedRadix 2 = 2 ^ 64 
  LiftedRadix 8 = 8 ^ 21
  LiftedRadix p = p ^ (Lg p (2 ^ 64 - 1))

-- | A wrapper for a fifted digit.
newtype Lifted p = Lifted { getLifted :: Mod (LiftedRadix p) }

deriving via Mod (LiftedRadix p) instance Radix p => Show (Lifted p)

deriving via Mod (LiftedRadix p) instance Radix p => Eq (Lifted p)

deriving via Mod (LiftedRadix p) instance Radix p => Ord (Lifted p)

deriving via Mod (LiftedRadix p) instance Radix p => Num (Lifted p)

deriving via Mod (LiftedRadix p) instance Radix p => Enum (Lifted p)

deriving via Mod (LiftedRadix p) instance Radix p => Digital (Lifted p)

instance Radix p => Real (Lifted p) where toRational = undefined

instance Radix p => Integral (Lifted p) where
  toInteger = fromIntegral . unMod . getLifted
  quotRem a b = let (q, r) = quotRem (fromIntegral a) (fromIntegral b)
                in (fromIntegral q, fromIntegral r)

------------------------------------------------------------
-- |  Integer p-adic number (an element of \(\mathbb{Z}_p\)) with 20 digits precision
newtype Z p = Z [Lifted p]

instance Radix p => Fixed (Z p) where
  precision  _ = 20

  showPrec pr n =
    case findCycle pr (digits n) of
      ([],[0]) -> "0"
      (pref, []) -> ell ++ toString pref
      (pref, [0]) -> toString pref
      (pref, cyc)
        | length pref + length cyc <= pr ->
          let sp = toString pref
              sc = toString cyc
           in "(" ++ sc ++ ")" ++ sep ++ sp
        | otherwise -> ell ++ toString (take pr $ pref ++ cyc)
    where
      showD = show . unMod
      toString = intercalate sep . map showD . reverse
      ell = "…" ++ sep 
      sep
        | radix n < 11 = ""
        | otherwise = " "

  eqPrec pr a b = and $ take pr $ zipWith (==) (digits a) (digits b)

instance Radix p => Digital (Z p) where
  type Digits (Z p) = [Mod p]
  type LiftedDigits (Z p) = [Lifted p]
  radix = fromIntegral . natVal
  digits (Z n) = unliftDigits n
  fromDigits = Z . liftDigits
  liftedDigits (Z ds) = ds
  mkUnit = Z

instance Radix p => Padic (Z p) where
  type Unit (Z p) = Z p
  fromUnit (u, v) = radix u^v * u
  splitUnit n = go prec (digits n)
    where
      prec = precision n
      go 0 _ = (fromDigits $ repeat 0, prec)
      go k xs =
        case xs of
          0:ds -> go (k - 1) ds
          _ -> (fromDigits xs, prec - k)
  inverse n | isInvertible n = Just (1 `div` n)
            | otherwise = Nothing
  
instance Radix p => Show (Z p) where
  show n = showPrec (precision n) n

instance Radix p => Eq (Z p) where
  a == b = eqPrec (precision a) a b

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

ilog :: (Integral a, Integral b) => a -> a -> b
ilog a b =
  fromInteger $ smallInteger (integerLogBase# (fromIntegral a) (fromIntegral b))

instance Radix p => Num (Z p) where
  fromInteger n
    | n < 0 = -fromInteger (-n)
    | otherwise = Z (d:ds)
    where
      d:ds = toRadix (radix d) n ++ repeat 0
  abs = id
  signum 0 = 0
  signum _ = 1
  Z a + Z b = Z $ addZ a b
  Z a * Z b = Z $ mulZ a b
  negate (Z a) = Z $ negZ a

negZ :: Radix p => [Lifted p] -> [Lifted p]
{-# INLINE negZ #-}
negZ = go
  where
    go (0:t) = 0 : go t
    go (h:t) = -h : map (\x -> -x - 1) t

carry :: (Integral a, Radix p) => a -> (a, Lifted p)
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

-- Division which does not raize exceptions.
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

instance Radix p => Ord (Z p) where
  compare = error "ordering is not defined for Z"

instance Radix p => Enum (Z p) where
  toEnum = fromIntegral
  fromEnum = fromIntegral . toInteger

instance Radix p => Integral (Z p) where
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
  div a b =
    case divMaybe a b of
      Just r -> r
      Nothing ->
        error $ show b ++ " is indivisible in " ++ show (radix a) ++ "-adics!"
  mod a m = fromInteger (toInteger a `mod` toInteger m)
  quotRem a b = (a `div` b, a `mod` b)

  how
-- Uses the modified tortiose and hare method.
findCycle :: Eq a => Int -> [a] -> ([a], [a])
findCycle len lst =
  case tortoiseHare rest of
    Just (a, c) -> clean $ rollback (pref ++ a, c)
    Nothing -> (pref, [])
  where
    (pref, rest) = splitAt len lst
    tortoiseHare x =
      fmap (fmap fst) . listToMaybe $
      dropWhile (\(_, (a, b)) -> notCycle a b) $
      zip (inits x) $
      zipWith splitAt [1 .. len] $ zipWith take [4,8 ..] $ tails x
    notCycle a b = not (concat (replicate 3 a) == b)
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

instance Radix p => Real (Z p) where
  toRational 0 = 0
  toRational n = ratDecomposition (precision n) n

ratDecomposition :: (RealPadic n p, Integral i) => Int -> n -> Ratio i
ratDecomposition pr x = extEuclid (n, m) * fromIntegral p ^^ valuation x
    where
      p = radix x
      m = p ^ (2 * pr)
      n = pMod (unit x) m
  
pMod :: (Padic n, Radix p, LiftedDigits n ~ [Lifted p]) => n -> Integer -> Integer
pMod n m = res `mod` m
  where
    ds = liftedDigits (n)
    pk = radix (head ds)
    k = 1 + ilog pk m
    res = fromRadix pk (take k (fromIntegral <$> ds))

ratDecomposition' pr x = (n, m)
    where
      p = radix x
      m = p ^ (2*pr)
      n = pMod x m

extEuclid :: Integral i => (Integer, Integer) -> Ratio i
extEuclid (n, m) = go (m, 0) (n, 1)
  where
    go (v1, v2) (w1, w2)
      | 2*w1*w1 > abs m =
        let q = v1 `div` w1
         in go (w1, w2) (v1 - q * w1, v2 - q * w2)
      | otherwise = fromRational (w1 % w2)

-- | For given radix /p/ and natural number /m/ returns precision sufficient for rational
-- reconstruction of fractions with numerator and denominator not exceeding /m/.
--
-- Examples:
-- >>> sufficientPrecision 2 (maxBound :: Int)
-- 65
-- >>> sufficientPrecision 3 (maxBound :: Int)
-- 41
-- >>> sufficientPrecision 11 (maxBound :: Int)
-- 19
sufficientPrecision :: (Integral a) => Integer -> a -> Integer
sufficientPrecision p m = ilog p (2 * fromIntegral m) + 1

------------------------------------------------------------

-- |  Rational p-adic number (an element of \(\mathbb{Q}_p\)) with 20 digits precision.
data Q (p :: Nat) = Q (Z p) Int

instance Radix p => Fixed (Q p) where
  precision _ = 20

  showPrec pr n = si ++ sep ++ "." ++ sep ++ sf
    where
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
          (pref, []) -> ell ++ toString pref
          (pref, [0]) -> toString pref
          (pref, cyc)
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

  eqPrec pr a b =
    (isZero a && isZero b)
    || (valuation a' == valuation b' && eqPrec pr (unit a') (unit b'))
    where
      a' = normalize a
      b' = normalize b

instance Radix p => Show (Q p) where
  show n = showPrec (precision n) n

instance Radix p => Eq (Q p) where
  a == b = eqPrec (precision a) a b

instance Radix p => Ord (Q p) where
  compare = error "Order is nor defined for p-adics."

instance Radix p => Digital (Q p) where
  type Digits (Q p) = Digits (Z p)
  type LiftedDigits (Q p) = LiftedDigits (Z p)
  radix = fromIntegral . natVal
  digits (Q u v) = replicate v 0 ++ digits u
  fromDigits ds = normalize $ Q (fromDigits ds) 0
  liftedDigits = liftedDigits . unit
  mkUnit ds = normalize $ Q (mkUnit ds) 0

instance Radix p => Padic (Q p) where
  type Unit (Q p) = Z p
  fromUnit (u, v) = Q u v
  splitUnit (Q u v) = (u, v)
  
  inverse n
    | unMod (firstDigit n) `gcd` radix n == 1 = Just (1/n)
    | otherwise = Nothing

normalize :: RealPadic n p  => n -> n
--normalize 0 = 0
normalize n = go (liftedDigits u) v
  where
    (u, v) = splitUnit n
    go _ k | k >= pr = 0
    go (d:ds) k = case getUnitZ p (fromIntegral d) of
      (0, 0) -> go ds (k + ilog p (radix d))
      (d', k')
        | k + k' >= pr -> 0
        | otherwise ->
          let s = fromIntegral (p^k')
          in fromUnit (mkUnit (shiftL s (fromIntegral d':ds)), k + k')
    p = radix n
    pr = precision n

shiftL :: Radix p => Lifted p -> [Lifted p] -> [Lifted p]
shiftL s (d1:d2:ds) = let (q, r) = quotRem d2 s
                          pk = fromIntegral (radix s `div` fromIntegral s)
                      in d1 + r * pk : shiftL s (q : ds)
  
instance Radix p => Num (Q p) where
  fromInteger n = res
    where
      (u, v) = getUnitZ (radix res) n
      pr = precision res
      res | n == 0 = Q 0 pr
          | v >= pr = Q 0 pr
          | otherwise = normalize $ Q (fromInteger u) v
          
  a + b = Q (p ^ (va - v) * unit a + p ^ (vb - v) * unit b) v
    where
      va = valuation a
      vb = valuation b
      v = va `min` vb
      p = radix a
  a * b = Q (unit a * unit b) (valuation a + valuation b)
  negate (Q u v) = Q (negate u) v
  abs = id
  signum 0 = 0
  signum _ = 1

instance Radix p => Fractional (Q p) where
  fromRational 0 = 0
  fromRational x = res
    where
      res = normalize $ Q (fromDigits (series n)) v
      p = radix res
      (q, v) = getUnitQ p x
      (n, d) = (fromIntegral $ numerator q, fromIntegral $ denominator q)
      series 0 = repeat 0
      series n =
        let m = fromIntegral n / fromIntegral d
         in m : series ((n - fromIntegral (unMod m) * d) `div` p)
  a / b = Q res (valuation a - valuation b')
    where
      b' = normalize b
      res =
        case divMaybe (unit a) (unit b') of
          Nothing ->
            error $
            show b ++ " is indivisible in " ++ show (radix a) ++ "-adics!"
          Just r -> r

instance (Radix p) => Real (Q p) where
  toRational 0 = 0
  toRational n = ratDecomposition (precision n) n 

------------------------------------------------------------

getUnitZ :: Integer -> Integer -> (Integer, Int)
getUnitZ _ 0 = (0, 0)
getUnitZ p x = (b, length v)
  where
    (v, b:_) = span (\n -> n `mod` p == 0) $ iterate (`div` p) x

-- | Extracts p-adic unit from a rational number. For radix \(p\) and rational number \(x\) returns
-- pair \((k, r/s)\) such that \(x = r/s \cdot p^k\).
--
-- Examples:
-- >>> getUnitQ 3 (75/157)
-- (1,25 % 157)
-- >>> getUnitQ 5 (75/157)
-- (2,3 % 157)
-- >>> getUnitQ 157 (75/157)
-- (-1,75 % 1)
getUnitQ :: Integral p => p -> Ratio p -> (Ratio p, Int)
getUnitQ _ 0 = (0, 0)
getUnitQ p x = (c, genericLength v2 - genericLength v1)
  where
    (v1, b:_) =
      span (\n -> denominator n `mod` p == 0) $ iterate (* fromIntegral p) x
    (v2, c:_) =
      span (\n -> numerator n `mod` p == 0) $ iterate (/ fromIntegral p) b

-- | Returms 'True' for multiplicatively invertible numbers.
isInvertible n = unMod d `gcd` radix d == 1
  where
    d = firstDigit n

-- | The least significant digit of a p-adic number.
firstDigit n = head (digits n)

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
  
-- | p-Adic solution of the equation via Newton method.
henselLifting ::
     (Eq n, Padic n, Digits n ~ [Mod p], Radix p)
  => (n -> n) -- ^ Function to be vanished.
  -> (n -> n) -- ^ Derivative of the function.
  -> [n] -- ^ The result.
henselLifting f f' = res
  where
    pr = precision (head res)
    mf = firstDigit . f . fromMod
    res = do
      r <- fromMod <$> filter (\x -> mf x == 0) [0..]
      iterateM pr step r
    step x = do
      invf' <- maybeToList (inverse (f' x))
      return (x - f x * invf')

iterateM :: (Eq a, MonadPlus m) => Int -> (a -> m a) -> a -> m a
iterateM n f = go n
  where
    go 0 x = pure x
    go i x = do
      y <- f x
      if x == y then pure x else go (i - 1) y

fromMod :: (Radix p, Num n, Padic n, Digits n ~ [Mod p]) => Mod p -> n
fromMod = fromInteger . fromIntegral . unMod

    
