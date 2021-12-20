{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE DerivingVia #-}
{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE GADTs #-}

module Padic where

import           GHC.TypeLits
import GHC.Integer.GMP.Internals
import           Data.Constraint
import           Data.InfList (InfList(..), (+++))
import qualified Data.InfList as Inf
import           Data.List
import           Data.Word

------------------------------------------------------------

type family NonZeroNat (m :: Nat) :: Constraint where
  NonZeroNat 0 = TypeError ('Text "Zero base!")
  NonZeroNat m = ()

type family ValidBase (m :: Nat) :: Constraint where
  ValidBase m = (NonZeroNat m, KnownNat m)

type family Lg p n where
  Lg p 0 = 0
  Lg p n = Lg p (Div n p) + 1

type Base m = (ValidBase (MaxBase m), ValidBase m)

------------------------------------------------------------

type Digits p = InfList (Digit p)
  
class Digital n where
  digits :: n -> Digits p
  base   :: Integral i => n -> i

class Fixed n where
  precision :: Integral i => n -> i

class Padic n where
  unit :: n -> n
  valuation :: n -> Int
  
------------------------------------------------------------
type N = Word64
type MaxBase p = p ^ (Lg p (2^64) - 1)

newtype Digit (m :: Nat) = Digit N
  deriving (Show, Num, Eq, Ord, Real, Integral) via N

instance ValidBase m => Bounded (Digit m) where
  minBound = 0
  maxBound = let res = base res - 1 in res

instance ValidBase m => Enum (Digit m) where
  toEnum = fromIntegral
  fromEnum = fromIntegral . toInteger
  enumFrom a = [a..maxBound]

instance ValidBase p => Digital (Digit p) where
  digits = undefined
  base = fromIntegral . natVal

------------------------------------------------------------

newtype Z p = Z (Digits (MaxBase p))

deriving via (Z' p 20) instance Base p => Eq (Z p)
deriving via (Z' p 20) instance Base p => Show (Z p)

instance Base p => Digital (Z p) where
  digits n = fromIntegral <$> extractDigits n
  base = fromIntegral . natVal

extractDigits :: Base p => Z p -> Digits p
extractDigits (Z ds) = Inf.concatMap expand ds
  where
    expand d = res
      where
        res | d == 0 = 0 <$ toBase b (base d `div` b)
            | otherwise = toBase b $ fromIntegral d
        b = base (head res)

instance Base p => Num (Z p) where
  fromInteger = toZ
  abs = id
  signum 0 = 0
  signum _ = 1
  Z a + Z b = Z $ addZ a b
  Z a * Z b = Z $ mulZ a b
  negate (Z a) = Z (negZ a)

-- превращает целое число в p-адическое
toZ :: Base p => Integer -> Z p
toZ n | n < 0 = - toZ (- n)
      | otherwise = res 
  where
    res = Z $ toDigits (fromIntegral n) +++ Inf.repeat 0

toDigits :: ValidBase p => Integer -> [Digit p] 
toDigits n = res
  where
    res = toBase (base (head res)) n 

-- преобразование целого числа в цифры по указанному основанию
toBase :: Integral d => Integer -> Integer -> [d]
toBase _ 0 = [0]
toBase b n = unfoldr go n 
  where
    go 0 = Nothing
    go x = let (q, r) = quotRem x b
           in Just (fromIntegral r, q)

-- смена знака на противоположный
negZ :: ValidBase p => Digits p -> Digits p
negZ ds = go ds
  where go (0 ::: t) = 0 ::: go t
        go (h ::: t) = p - h ::: Inf.map (\x -> p - x - 1) t
        p = base (Inf.head ds)

-- выделяет из натурального числа перенос на следующий разряд
carry :: (ValidBase p, Integral i) => i -> (i, Digit p)
carry n = (n `div` b, d)
  where
    b = base d
    d = fromIntegral (n `mod` b)

-- поразрядное сложение с переносом
addZ :: ValidBase p => Digits p -> Digits p -> Digits p
addZ a b = Inf.mapAccumL step 0 $ Inf.zip a b
  where
    step r (x, y) = carry (fromIntegral x + fromIntegral y + r)

-- поразрядное умножение с переносом
mulZ :: ValidBase p => Digits p -> Digits p -> Digits p
mulZ a = go
  where
    go (b ::: bs) = addZ (go bs) `apTail` scaleZ b a
    apTail f (h ::: t) = h ::: f t

-- поразрядное умножение на цифру с переносом
scaleZ :: ValidBase p => Digit p -> Digits p -> Digits p
scaleZ s =
  Inf.mapAccumL (\r x -> carry (fromIntegral s * fromIntegral x + r)) 0

instance Base p => Fractional (Z p) where
  Z a / Z b = case divZ a b of
                Just r -> Z r
                Nothing -> error "undivisible number!"
  fromRational = undefined

-- поразрядное деление двух чисел "уголком"
divZ :: ValidBase p => Digits p -> Digits p -> Maybe (Digits p)
divZ a b = go a <$ invertMod (Inf.head b)
  where
    Just r = invertMod (Inf.head b)
    go (0 ::: xs) = 0 ::: go xs
    go xs =
      let m = Inf.head xs * r
          mulAndSub = addZ xs . negZ . scaleZ m 
      in m ::: go (Inf.tail $ mulAndSub b)

invertMod :: ValidBase p => Digit p -> Maybe (Digit p)
invertMod x@(Digit d)
  | gcd d (base x) == 1 =
      Just (Digit $ fromInteger $ recipModInteger (fromIntegral d) (base x))
  | otherwise = Nothing

------------------------------------------------------------

newtype Z' (p :: Nat) (prec :: Nat) = Z' (Z p)

deriving via Z p instance Base p => Digital (Z' p prec)
deriving via Z p instance Base p => Num (Z' p prec)
deriving via Z p instance Base p => Fractional (Z' p prec)
  
instance KnownNat prec => Fixed (Z' p prec) where
  precision = fromIntegral . natVal

instance (KnownNat prec, Base p) => Eq (Z' p prec) where
  x@(Z' a) == Z' b = Inf.take pr (digits a) == Inf.take pr (digits b)
    where
      pr = precision x

instance (KnownNat prec, Base p) => Show (Z' p prec) where
  show n = process . reverse . Inf.take pr $ digits n
    where
      pr = precision n
      process lst = case dropWhile (== 0) lst of
        [] -> "0"
        l -> ell l ++ intercalate sep (show  <$> l)
      ell l = if length l < pr then "" else "…"
      sep = if base n < 11 then "" else " "

instance (KnownNat prec, Base p) => Ord (Z' p prec) where
  compare = error "ordering is not defined for Z"
