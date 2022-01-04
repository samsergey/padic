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
{-# OPTIONS_HADDOCK hide, prune, ignore-exports #-}


module Math.NumberTheory.Padic.Integer where

import Data.Constraint (Constraint)
import Data.List
import Data.Ratio
import Data.Maybe (listToMaybe, maybeToList)
import Data.Mod
import GHC.TypeLits hiding (Mod)
import GHC.Prim
import GHC.Integer (smallInteger)
import GHC.Integer (smallInteger)
import GHC.Integer.GMP.Internals
import GHC.Integer.Logarithms (integerLogBase#)

import Math.NumberTheory.Padic.Classes

------------------------------------------------------------

instance (KnownNat p, ValidRadix p) => Digital (Mod p) where
  type Digits (Mod p) = Mod p
  type LiftedDigits (Mod p) = Mod p
  digits = id
  fromDigits = id
  radix = fromIntegral . natVal
  liftedDigits = id
  mkUnit = id


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

-- | Constraint for regular p-adic number.
type family RealPadic n p :: Constraint where
  RealPadic n p =
    ( Padic n
    , Padic (Unit n)
    , Real n
    , Radix p
    , LiftedDigits n ~ [Lifted p]
    , LiftedDigits (Unit n) ~ [Lifted p]
    )
  
------------------------------------------------------------
{- | In order to gain efficiency the p-adic number is internally
represented as an infinite list of /lifted/ digits modulo \(p^k\), where \(k\) is
chosen so that each lifted digit fits in a 'Word'.

\[
x = ...ddddddddddddddd_{(p)} =  ... \underbrace{ddddd}_k\,\underbrace{ddddd}_k\,\underbrace{ddddd}_k{}_{(p^k)}
\]

Sequence of digits modulo \(p\) are used mainly for textual representation and may be obtained by 'digits' function. -}
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

-- | For a given list extracts prefix and a cycle, limiting length of prefix and cycle by @len@.
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
  

fromMod :: (Radix p, Num n, Padic n, Digits n ~ [Mod p]) => Mod p -> n
fromMod = fromInteger . fromIntegral . unMod


pMod :: (Padic n, Radix p, LiftedDigits n ~ [Lifted p]) => n -> Integer -> Integer
pMod n m = res `mod` m
  where
    ds = liftedDigits (n)
    pk = radix (head ds)
    k = 1 + ilog pk m
    res = fromRadix pk (take k (fromIntegral <$> ds))

-- | Returms 'True' for multiplicatively invertible numbers.
isInvertible n = unMod d `gcd` radix d == 1
  where
    d = firstDigit n

------------------------------------------------------------
newtype ZM (p :: Nat) = ZM Integer
  deriving Show

instance (KnownNat p, ValidRadix p) => Fixed (ZM p) where
  precision _ = 20
  showPrec pr (ZM n) = show n
  eqPrec pr x@(ZM a) (ZM b) = a `mod` pk == b `mod` pk
    where
      pk = radix x ^ pr

instance (KnownNat p, ValidRadix p) => Digital (ZM p) where
  type Digits (ZM p) = [Int]
  type LiftedDigits (ZM p) = Integer
  fromDigits ds = res
    where
      res = ZM $ fromRadix p ds
      p = radix res
  digits n = toRadix (radix n) (liftedDigits n)
  radix = fromIntegral . natVal
  liftedDigits (ZM n) = n
  mkUnit = ZM

instance (KnownNat p, ValidRadix p) => Padic (ZM p) where
  type Unit (ZM p) = ZM p
  fromUnit (u, v) = radix u^v * u
  splitUnit n = let (u, v) = getUnitZ (radix n) (liftedDigits n)
                in (ZM u, v)
  inverse n | firstDigit n `gcd` radix n == 1 = Just undefined -- (1 `div` n)
            | otherwise = Nothing

liftedMod :: (Digital a1, Integral a2, Fixed a1) => a1 -> a2
liftedMod n = radix n ^ precision n

instance (KnownNat p, ValidRadix p) => Num (ZM p) where
  fromInteger n = res
    where
      res = ZM $ fromInteger n `mod` liftedMod res
      
  x@(ZM a) + ZM b = ZM $ (a + b) `mod` liftedMod x 
  x@(ZM a) * ZM b = ZM $ (a * b) `mod` liftedMod x 
  negate x@(ZM a) = ZM $ liftedMod x - a
  abs = id
  signum _ = 1

instance (KnownNat p, ValidRadix p) => Enum (ZM p) where

instance (KnownNat p, ValidRadix p) => Real (ZM p) where
  toRational 0 = 0
  toRational n = extEuclid (liftedDigits n, liftedMod n)

instance (KnownNat p, ValidRadix p) => Integral (ZM p) where
  toInteger n = if denominator r == 1
                then numerator r
                else error "not an integer!"
    where r = toRational n
  x@(ZM a) `quotRem` (ZM b)
    | b `gcdInteger` pk == 1 = (ZM (a * recipModInteger b pk), ZM (a - q * b)) 
    | otherwise = error "not divisible!" 
    where
      pk = liftedMod x
      q = a * recipModInteger b pk


instance (KnownNat p, ValidRadix p) => Ord (ZM p) where
  compare = error "ordering is not defined for Z"

instance (KnownNat p, ValidRadix p) => Eq (ZM p) where
  a == b = eqPrec (precision a) a b
