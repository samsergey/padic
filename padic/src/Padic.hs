{-# LANGUAGE FlexibleContexts #-}
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
{-# LANGUAGE GeneralizedNewtypeDeriving #-}

module Padic where

import GHC.TypeLits
import Data.Constraint
import Data.InfList (InfList(..), (+++))
import qualified Data.InfList as Inf
import Data.List
import Data.Word

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
  digits     :: Integral i => n -> InfList i
  fromDigits :: Integral i => InfList i -> n
  base :: Integral i => n -> i



class Fixed n where
  precision :: Integral i => n -> i

class Padic n where
  unit :: n -> n
  valuation :: n -> Int
  
------------------------------------------------------------
type N = Word64

newtype Digit (m :: Nat) = Digit N
  deriving (Show, Num, Bounded, Eq, Real, Enum, Ord, Integral) via N

instance ValidBase p => Digital (Digit p) where
  digits = undefined
  fromDigits = undefined
  base = fromIntegral . natVal

------------------------------------------------------------

type MaxBase p = p ^ (Lg p (2^64) - 1)

newtype Z p = Z (Digits (MaxBase p))

instance ValidBase p => Digital (Z p) where
  digits (Z ds) = fromIntegral <$> ds
  fromDigits = Z . fmap fromIntegral
  base = fromIntegral . natVal

toDigits :: ValidBase p => Integral i => i -> [Digit p] 
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

instance Base p => Num (Z p) where
  fromInteger = toZ
  Z a + Z b = Z $ addZ a b
  Z a * Z b = Z $ mulZ a b
  negate = negZ
  abs = id
  signum _ = 1
  

-- превращает целое число в p-адическое
toZ :: Base p => Integer -> Z p
toZ n | n < 0 = - toZ (- n)
      | otherwise = res 
  where
    res = Z $ toDigits (fromIntegral n) +++ Inf.repeat 0

-- смена знака на противоположный
negZ :: Base p => Z p -> Z p
negZ (Z ds) = Z $ go ds
  where go (0 ::: t) = 0 ::: go t
        go (h ::: t) = p - h ::: Inf.map (\x -> p - x - 1) t
        p = base (Inf.head ds)

-- выделяет из натурального числа перенос на следующий разряд
carry :: ValidBase p => N -> (N, Digit p)
carry n =
  let d = fromIntegral (n `mod` base d)
  in (n `div` base d, d)

-- поразрядное сложение с переносом
addZ :: ValidBase p => Digits p -> Digits p -> Digits p
addZ a b = Inf.mapAccumL step 0 $ Inf.zip a b
  where
    step r (x, y) = carry (fromIntegral x + fromIntegral y + r)

mulZ :: ValidBase p => Digits p -> Digits p -> Digits p
mulZ a = go
  where
    go (b ::: bs) = addZ (go bs) `apTail` scaleZ b a
    apTail f (h ::: t) = h ::: f t

scaleZ :: ValidBase p => Digit p -> Digits p -> Digits p
scaleZ s a =
  Inf.mapAccumL (\r x -> carry (fromIntegral s * fromIntegral x + r)) 0 a

newtype Z' (p :: Nat) (prec :: Nat) = Z' (Z p)
  
instance Base p => Num (Z' p prec) where
  fromInteger = Z' . fromInteger
  Z' a + Z' b = Z' $ a + b
  Z' a * Z' b = Z' $ a * b
  negate (Z' a) = Z' $ negate a
  abs = id
  signum _ = 1

instance Base p => Digital (Z' p prec) where
  digits (Z' n) = digits n
  fromDigits = Z' . fromDigits
  base (Z' n) = base n

instance KnownNat prec => Fixed (Z' p prec) where
  precision = fromIntegral . natVal

digits'' :: (Digital n, Integral i) => n -> InfList i
digits'' n = Inf.concatMap (expand (base n)) $ digits' n
  where
    expand :: (Integral i, ValidBase p) => i -> Digit p -> [i]
    expand b2 d = res
      where
        b1 = base d
        res
          | d == 0 = replicate (ilog b2 b1) 0
          | otherwise = toBase b2 $ fromIntegral d
  
    ilog b x = floor (logBase (fromIntegral b) (fromIntegral x))
