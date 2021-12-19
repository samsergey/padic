{-# LANGUAGE StandaloneDeriving #-}
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

import GHC.TypeLits
import Data.Constraint
import InfList (InfList(..), (+++))
import qualified InfList as Inf
import Data.List
import Data.Ratio
import Data.Word

------------------------------------------------------------

type family NonZeroNat (m :: Nat) :: Constraint where
  NonZeroNat 0 = TypeError ('Text "Zero base!")
  NonZeroNat m = ()

type family Base (m :: Nat) :: Constraint where
  Base m = (NonZeroNat m, KnownNat m)

type family Lg p n where
  Lg p 0 = 0
  Lg p n = Lg p (Div n p) + 1

type family ZBase m :: Constraint where
  ZBase m = (Base m, Base (MaxBase m))

------------------------------------------------------------
  
class Digital n where
  digits :: (Base p, n ~ f p) => n -> InfList (Digit p)
  base :: Integral i => n -> i


class Fixed n where
  precision :: Integral i => n -> i

class Padic n where
  unit :: n -> n
  valuation :: n -> Int
  
------------------------------------------------------------

type N = Word64
type MaxN  = 2^64 :: Nat

type family MaxBase p where
  MaxBase p = p ^ (Lg p MaxN - 1)

newtype Digit (m :: Nat) = Digit N
  deriving (Show, Num, Bounded, Eq, Real, Enum, Ord, Integral) via N

instance Base p => Digital (Digit p) where
  digits = undefined
  base = fromIntegral . natVal

data Z p where
  Z :: ZBase p => InfList (Digit (MaxBase p)) -> Z p

maxBase :: Integral i => i -> i
maxBase p = p ^ ilog p (maxBound :: N)

ilog b x = floor (logBase (fromIntegral b) (fromIntegral x))


toDigits :: Base p => Integral i => i -> [Digit p] 
toDigits n = res
  where
    res = toBase (base (head res)) n 

toBase :: (Integral i, Integral d) => i -> i -> [d]
toBase b 0 = [0]
toBase b n = res 
  where
    res = unfoldr go n
    go 0 = Nothing
    go n = let (q, r) = quotRem n b
           in Just (fromIntegral r, q)

-- превращает целое число в p-адическое
toZ :: (ZBase p, Integral i) => i -> Z p
toZ n | n < 0 = - toZ (- n)
      | otherwise = res 
  where
    res = Z $ toDigits (fromIntegral n) +++ Inf.repeat 0

-- смена знака на противоположный
negZ :: ZBase p => Z p -> Z p
negZ (Z ds) = Z $ go ds
  where go (0 ::: t) = 0 ::: go t
        go (h ::: t) = p - h ::: Inf.map (\x -> p - x - 1) t
        p = base (Inf.head ds)

-- выделяет из натурального числа перенос на следующий разряд
carry :: (Base p, Integral n) => n -> (n, Digit p)
carry n =
  let d = fromIntegral (n `mod` base d)
  in (n `div` base d, d)

-- поразрядное сложение с переносом
--addZ :: (Base p) => Z p -> Z p -> Z p
addZ a b = Inf.mapAccumL step 0 $ Inf.zip a b
  where
    step r (x, y) = carry (fromIntegral x + fromIntegral y + r)

mulZ a b = go b
  where
    go (b ::: bs) = addZ (go bs) `apTail` scaleZ b a
    apTail f (h ::: t) = h ::: f t

--scaleZ :: ZBase p => Mod p -> InfList (Mod p) -> InfList (Mod p)
scaleZ s a =
  Inf.mapAccumL (\r x -> carry (fromIntegral s * fromIntegral x + r)) 0 a

instance ZBase p => Digital (Z p) where
  base = fromIntegral . natVal
  digits (Z ds) = Inf.concatMap expand ds

expand :: ZBase p => Digit (MaxBase p) -> [Digit p]
expand n = res
  where
    b1 = base n
    b2 = base (head res)
    res
     | n == 0 = replicate (ilog b2 b1) 0
     | otherwise = toBase b2  n

instance ZBase p => Num (Z p) where
  fromInteger = toZ
  Z a + Z b = Z $ addZ a b
  Z a * Z b = Z $ mulZ a b
  negate = negZ

newtype Z' (p :: Nat) (prec :: Nat) = Z' (Z p)

instance ZBase p => Num (Z' p prec) where
  fromInteger = Z' . fromInteger

instance ZBase p => Digital (Z' p prec) where
  digits (Z' n) = digits n
  base (Z' n) = base n

instance KnownNat prec => Fixed (Z' p prec) where
  precision = fromIntegral . natVal
