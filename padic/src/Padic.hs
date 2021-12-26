{-|
Module      : Padic
Description : Representation a nd simple algebra for p-adic numbers.
Copyright   : (c) Sergey Samoylenko, 2021
License     : GPL-3
Maintainer  : samsergey@yandex.ru
Stability   : experimental
Portability : POSIX
-}

{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE DerivingVia #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE LambdaCase #-}

module Padic
  ( Radix
  , Digital
  , radix
  , digits
  , fromDigits
  , Padic
  , splitUnit
  , unit
  , valuation
  , Digits
  , LiftedDigits
  , Z
  , Z'
  , divMaybe
  ) where

import Data.Constraint (Constraint)
import Data.List
import Data.Maybe
import Data.Mod
import Data.Ratio
import GHC.TypeLits hiding (Mod)
import GHC.Prim (coerce)

------------------------------------------------------------
-- | Constraint for non-zero natural number which can be a radix.
type family ValidRadix (m :: Nat) :: Constraint where
  ValidRadix 0 = TypeError ('Text "Zero radix!")
  ValidRadix m = ()

-- | Naive type-level log function.
type family Lg p n where
  Lg p 0 = 0
  Lg p n = Lg p (Div n p) + 1

-- | Constraint for valid radix of a number
type Radix m
   = ( ValidRadix (LiftedRadix m)
     , KnownNat (LiftedRadix m)
     , ValidRadix m
     , KnownNat m)

------------------------------------------------------------
-- | Typeclass for digitally representable objects
class Digital n where
  type Digits n -- ^ a digit or a list of digits
  fromDigits :: Digits n -> n -- ^ constructs a number from digits
  digits :: n -> Digits n -- ^ returns digits of a number
  -- | Returns the radix of a number
  --
  -- >>> radix (5 :: Z 13)
  -- 13
  radix :: Integral i => n -> i

-- | Typeclass for p-adic numbers
class Digital n => Padic n where
  type Unit n
  precision :: Integral i => n -> i -- ^ returns precision a number
  splitUnit :: n -> (Unit n, Int) -- ^ returns valuation and unit of a number
  normalize :: n -> n
  
-- | returns the unit of a number
--
-- >>> unit (120 :: Z 10)
-- 12
--
-- >>> unit (75 :: Z 5)
-- 3
unit :: Padic n => n -> Unit n
unit = fst . splitUnit

-- | returns a valuation  of a number
--
-- >>> valuation (120 :: Z 10)
-- 1
--
-- >>> valuation (75 :: Z 5)
-- 2
valuation :: Padic n => n -> Int
valuation = snd . splitUnit

norm :: (Fractional f, Padic n) => n -> f
norm n = fromIntegral (radix n) ^^ (-valuation n)

------------------------------------------------------------
instance (KnownNat p, ValidRadix p) => Digital (Mod p) where
  type Digits (Mod p) = Mod p
  digits = id
  fromDigits = id
  radix = fromIntegral . natVal

type LiftedRadix p = p ^ (Lg p (2 ^ 64) - 1)

newtype Lifted p =
  Lifted
    { unlift :: Mod (LiftedRadix p)
    }

deriving via Mod (LiftedRadix p) instance
         Radix p => Show (Lifted p)

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
  toInteger = fromIntegral . unMod . unlift
  quotRem = undefined

-- | Alias for an infinite list of lifted digits
type LiftedDigits p = [Lifted p]

------------------------------------------------------------
-- |  Integer p-adic number with 20 digits precision
newtype Z p =
  Z (LiftedDigits p)

deriving via (Z' p 20) instance Radix p => Eq (Z p)

deriving via (Z' p 20) instance Radix p => Ord (Z p)

deriving via (Z' p 20) instance Radix p => Show (Z p)

deriving via (Z' p 20) instance Radix p => Enum (Z p)

deriving via (Z' p 20) instance Radix p => Real (Z p)

deriving via (Z' p 20) instance Radix p => Integral (Z p)

deriving via (Z' p 20) instance Radix p => Padic (Z p)

instance Radix p => Digital (Z p) where
  type Digits (Z p) = [Mod p]
  radix = fromIntegral . natVal
  digits (Z n) = unliftDigits n
  fromDigits = Z . liftDigits

liftDigits :: Radix p => Digits (Z p) -> LiftedDigits p
liftDigits ds = res
  where
    res = unfoldr go ds
    go xs =
      let (a, r) = splitAt (ilog p pk) xs
       in Just (fromIntegral $ fromRadix p (unMod <$> a), r)
    p = radix (head ds)
    pk = radix (head res)

unliftDigits :: Radix p => LiftedDigits p -> Digits (Z p)
unliftDigits ds = res
  where
    res = concatMap (take (ilog p pk) . expand) (unMod . unlift <$> ds)
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

-- преобразование целого числа в цифры по указанному основанию
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

-- смена знака на противоположный
negZ :: Radix p => LiftedDigits p -> LiftedDigits p
negZ = go
  where
    go (0:t) = 0 : go t
    go (h:t) = -h : map (\x -> -x - 1) t

-- выделяет из натурального числа перенос на следующий разряд
carry :: (Integral a, Digital b, Num b) => a -> (a, b)
{-# INLINE carry #-}
carry n =
  let d = fromIntegral n
   in (n `div` radix d, d)

-- поразрядное сложение с переносом
addZ :: Radix p => LiftedDigits p -> LiftedDigits p -> LiftedDigits p
{-# INLINE addZ #-}
addZ a b = snd $ mapAccumL step 0 $ zip a b
  where
    step r (x, y) = carry (fromIntegral x + fromIntegral y + r)

-- поразрядное умножение с переносом
mulZ :: Radix p => LiftedDigits p -> LiftedDigits p -> LiftedDigits p
{-# INLINE mulZ #-}
mulZ a = go
  where
    go (b:bs) = addZ (go bs) `apTail` scaleZ b a
    apTail f (h:t) = h : f t

-- поразрядное умножение на цифру с переносом
scaleZ :: Radix p => Lifted p -> LiftedDigits p -> LiftedDigits p
{-# INLINE scaleZ #-}
scaleZ s =
  snd . mapAccumL (\r x -> carry (fromIntegral s * fromIntegral x + r)) 0

divMaybe :: Radix p => Z p -> Z p -> Maybe (Z p)
divMaybe (Z a) (Z b) = Z <$> divZ a b

-- поразрядное деление двух чисел "уголком"
divZ :: Radix p => LiftedDigits p -> LiftedDigits p -> Maybe (LiftedDigits p)
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

instance (KnownNat prec, Radix p) => Real (Z' p prec) where
  toRational = fromIntegral . toInteger

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

------------------------------------------------------------
------------------------------------------------------------
data Q (p :: Nat)
  = Zero
  | Q Int (Z p)

newtype Q' (p :: Nat) (prec :: Nat) =
  Q' (Q p)

deriving via Q p instance Radix p => Num (Q' p prec)

deriving via Q p instance Radix p => Fractional (Q' p prec)

deriving via (Q' p 20) instance Radix p => Digital (Q p)

deriving via (Q' p 20) instance Radix p => Eq (Q p)

deriving via (Q' p 20) instance Radix p => Ord (Q p)

deriving via (Q' p 20) instance Radix p => Show (Q p)

instance (KnownNat prec, Radix p) => Show (Q' p prec) where
  show (Q' Zero) = "0.0"
  show n = si ++ sep ++ "." ++ sep ++ sf
    where
      pr = precision n
      k = valuation n
      ds = digits n
      (f, i) = case compare k 0 of
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

instance (KnownNat prec, Radix p) => Digital (Q' p prec) where
  type Digits (Q' p prec) = Digits (Z' p prec)
  radix (Q' (Q _ n)) = radix n
  digits (Q' x) =
    case x of
      Zero    -> repeat 0
      (Q _ u) -> digits u
  fromDigits ds = Q' (Q 0 (fromDigits ds))

instance (KnownNat prec, Radix p) => Padic (Q' p prec) where
  type Unit (Q' p prec) = Z' p prec
  precision = fromIntegral . natVal

  splitUnit (Q' Zero) = (0, maxBound)
  splitUnit (Q' (Q v u)) = (coerce u, v)

  normalize (Q' Zero) = Q' Zero
  normalize n = Q' $ go 0 (digits n)
    where
      go i _
        | i > precision n = 0
      go i (0:u) = go (i + 1) u
      go i u = Q (valuation n + i) (fromDigits u)

instance Radix p => Padic (Q p) where
  type Unit (Q p) = Z p
  precision _ = 20

  splitUnit Zero = (0, maxBound)
  splitUnit (Q v u) = (u, v)

  normalize Zero = Zero
  normalize n = go 0 (digits n)
    where
      go i _
        | i > 20 = 0
      go i (0:u) = go (i + 1) u
      go i u = Q (valuation n + i) (fromDigits u)


instance (KnownNat prec, Radix p) => Eq (Q' p prec) where
  a == b =
    valuation a == valuation b &&
    and (take pr $ zipWith (==) (digits a) (digits b))
    where
      pr = precision a

instance (KnownNat prec, Radix p) => Ord (Q' p prec) where
  compare = error "ordering is not defined for Q"

instance Radix p => Num (Q p) where
  fromInteger 0 = Zero
  fromInteger n = normalize $ Q 0 (fromInteger n)

  Zero + a = a
  a + Zero = a
  a + b = Q v (p ^ (va - v) * unit a + p ^ (vb - v) * unit b)
    where
      va = valuation a
      vb = valuation b
      v = va `min` vb
      p = radix a

  Zero * _ = Zero
  _ * Zero = Zero
  a * b = Q (valuation a + valuation b) (unit a * unit b)

  negate Zero = Zero
  negate (Q v u) = Q v (negate u)

  abs = id

  signum Zero = 0
  signum _ = 1

instance Radix p => Fractional (Q p)  where
  fromRational 0 = Zero
  fromRational x = normalize res 
    where
      res = Q v (fromDigits (series n))
      p = radix res
      (v, q) = getUnit p x
      (n, d) = ( fromIntegral $ numerator q
               , fromIntegral $ denominator q)
      series 0 = repeat 0
      series n =
        let m = fromIntegral n / fromIntegral d
        in m : series ((n - fromIntegral (unMod m) * d) `div` p)

  a / b = Q (valuation a - valuation b) res
    where
      res =
        case divMaybe (unit a) (unit b) of
          Nothing ->
            error $ show b ++ " is indivisible in " ++ show (radix a) ++ "-adics!"
          Just r -> r

-- extracts p-adic unit from a rational number
getUnit :: Integral i => i -> Ratio i -> (Int, Ratio i)
getUnit p x = (genericLength v2 - genericLength v1, c) 
  where
    (v1,b:_) = span (\n -> denominator n `mod` p == 0) $
               iterate (* fromIntegral p) x
    (v2,c:_) = span (\n -> numerator n `mod` p == 0) $
               iterate (/ fromIntegral p) b
