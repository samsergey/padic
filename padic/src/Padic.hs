{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE DerivingVia #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE DataKinds #-}

module Padic where

import           GHC.TypeLits hiding (Mod)
import           Data.Constraint (Constraint)
import           Data.InfList (InfList(..), (+++))
import qualified Data.InfList as Inf
import           Data.List
import           Data.Mod

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

type Digits p = InfList (Mod p)
  
class Digital n where
  type Dig n
  digits :: n -> Dig n
  base   :: Integral i => n -> i

class Fixed n where
  precision :: Integral i => n -> i

class Padic n where
  unit :: n -> n
  valuation :: n -> Int
  
------------------------------------------------------------
type MaxBase p = p ^ (Lg p (2^32) - 1)

instance ValidBase p => Digital (Mod p) where
  type Dig (Mod p) = Mod p
  digits = id
  base = fromIntegral . natVal

instance ValidBase p => Real (Mod p) where
  toRational = undefined

instance ValidBase p => Integral (Mod p) where
  toInteger x = fromIntegral $ unMod x
  quotRem = undefined
------------------------------------------------------------

newtype Z p = Z { getDigits :: Digits (MaxBase p) }

deriving via (Z' p 20) instance Base p => Eq (Z p)
deriving via (Z' p 20) instance Base p => Ord (Z p)
deriving via (Z' p 20) instance Base p => Show (Z p)
deriving via (Z' p 20) instance Base p => Enum (Z p)
deriving via (Z' p 20) instance Base p => Real (Z p)
deriving via (Z' p 20) instance Base p => Integral (Z p)
deriving via (Z' p 20) instance Base p => Fixed (Z p)

instance Base p => Digital (Z p) where
  type Dig (Z p) = Digits p
  digits n = extractDigits n
  base = fromIntegral . natVal

extractDigits :: Base p => Z p -> Digits p
extractDigits (Z ds) = Inf.concatMap expand ds
  where
    expand d = res
      where
        res | d == 0 = 0 <$ toBase b (base d `div` b)
            | otherwise = toBase b (unMod d)
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
    res = Z $ toBase (base res) n +++ Inf.repeat 0

-- преобразование целого числа в цифры по указанному основанию
toBase :: (Integral i, Integral d) => i -> i -> [d]
toBase _ 0 = [0]
toBase b n = unfoldr go n 
  where
    go 0 = Nothing
    go x = let (q, r) = quotRem x b
           in Just (fromIntegral r, q)

-- смена знака на противоположный
negZ :: ValidBase p => Digits p -> Digits p
negZ = go
  where go (0 ::: t) = 0 ::: go t
        go (h ::: t) = - h ::: Inf.map (\x -> - x - 1) t

-- выделяет из натурального числа перенос на следующий разряд
carry :: (ValidBase p, Integral i) => i -> (i, Mod p)
carry n = let d = fromIntegral n in (n `div` base d, d)
    
-- поразрядное сложение с переносом
addZ :: ValidBase p => Digits p -> Digits p -> Digits p
addZ a b = Inf.mapAccumL step 0 $ Inf.zip a b
  where
    step r (x, y) = carry (unMod x + unMod y + r)

-- поразрядное умножение с переносом
mulZ :: ValidBase p => Digits p -> Digits p -> Digits p
mulZ a = go
  where
    go (b ::: bs) = addZ (go bs) `apTail` scaleZ b a
    apTail f (h ::: t) = h ::: f t

-- поразрядное умножение на цифру с переносом
scaleZ :: ValidBase p => Mod p -> Digits p -> Digits p
scaleZ s =
  Inf.mapAccumL (\r x -> carry (unMod s * unMod x + r)) 0

divMaybe :: Base p => Z p -> Z p -> Maybe (Z p)
divMaybe (Z a) (Z b) = Z <$> divZ a b

-- поразрядное деление двух чисел "уголком"
divZ :: ValidBase p => Digits p -> Digits p -> Maybe (Digits p)
divZ a (b ::: bs) = go a <$ invertMod b
  where
    Just r = invertMod b
    go (0 ::: xs) = 0 ::: go xs
    go xs =
      let m = Inf.head xs * r
          mulAndSub = addZ xs . negZ . scaleZ m 
      in m ::: go (Inf.tail $ mulAndSub (b ::: bs))

------------------------------------------------------------

newtype Z' (p :: Nat) (prec :: Nat) = Z' (Z p)

deriving via Z p instance Base p => Digital (Z' p prec)
deriving via Z p instance Base p => Num (Z' p prec)
  
instance KnownNat prec => Fixed (Z' p prec) where
  precision = fromIntegral . natVal

instance (KnownNat prec, Base p) => Eq (Z' p prec) where
  x@(Z' a) == Z' b = Inf.take pr (digits a) == Inf.take pr (digits b)
    where
      pr = precision x

instance (KnownNat prec, Base p) => Ord (Z' p prec) where
  compare = error "ordering is not defined for Z"

instance (KnownNat prec, Base p) => Show (Z' p prec) where
  show n = process . reverse . map unMod . Inf.take pr $ digits n
    where
      pr = precision n
      process lst = case dropWhile (== 0) lst of
        [] -> "0"
        l -> ell l ++ intercalate sep (show  <$> l)
      ell l = if length l < pr then "" else "…"
      sep = if base n < 11 then "" else " "
      -- sub = ("₀₁₂₃₄₅₆₇₈₉" !!) <$> reverse (toBase 10 b)

instance (KnownNat prec, Base p) => Enum (Z' p prec) where
  toEnum = fromIntegral
  fromEnum = fromIntegral . toInteger

instance (KnownNat prec, Base p) => Real (Z' p prec) where
  toRational = fromIntegral . toInteger

instance (KnownNat prec, Base p) => Integral (Z' p prec) where
  toInteger = undefined
  
  div (Z' a) d@(Z' b) = case divMaybe a b of
    Just r -> Z' r
    Nothing -> error $
      show d ++ " is indivisible in " ++ show (base d) ++ "-adics!"

  quotRem = error "quotRem is not defined for p-adics!" 

integerDigits :: (Base p, Integral a) => Z p -> Either [a] [a]
integerDigits n = process [] windows
  where
    b = base n
    chop = floor (logBase (fromIntegral b) (fromIntegral (maxBound :: Int)))
    windows = take (1 + fromIntegral chop) <$> tails (Inf.toList (digits n))
    process r ((x:xs):ws) = case sum xs of
      s | s == 0            -> Right (fromIntegral x:r)
        | s == (b - 1)*chop -> Left (fromIntegral x:r)
        | otherwise         -> process (fromIntegral x:r) ws 
