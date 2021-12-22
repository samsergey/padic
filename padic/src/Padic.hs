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

-- | Constraint for a natural number which can be a radix
type family ValidRadix (m :: Nat) :: Constraint where
  ValidRadix m = (NonZeroNat m, KnownNat m)

type family Lg p n where
  Lg p 0 = 0
  Lg p n = Lg p (Div n p) + 1

type Radix m = (ValidRadix (LiftedRadix m), ValidRadix m)

------------------------------------------------------------

type Digits p = InfList (Mod p)
  
class Digital n where
  type Dig n
  fromDigits :: Dig n -> n
  digits :: n -> Dig n
  base   :: Integral i => n -> i

class Fixed n where
  precision :: Integral i => n -> i

class Digital n => Padic n where
  splitUnit :: n -> (n, Int)

  unit :: n -> n
  unit = fst . splitUnit
  
  valuation :: n -> Int
  valuation = snd . splitUnit
  
------------------------------------------------------------

type LiftedRadix p = p ^ (Lg p (2^32) - 1)

instance ValidRadix p => Digital (Mod p) where
  type Dig (Mod p) = Mod p
  digits = id
  fromDigits = id
  base = fromIntegral . natVal
  
instance ValidRadix p => Real (Mod p) where
  toRational = undefined

instance ValidRadix p => Integral (Mod p) where
  toInteger x = fromIntegral $ unMod x
  quotRem = undefined

------------------------------------------------------------

newtype Z p = Z { getDigits :: Digits (LiftedRadix p) }

deriving via (Z' p 20) instance Radix p => Eq (Z p)
deriving via (Z' p 20) instance Radix p => Ord (Z p)
deriving via (Z' p 20) instance Radix p => Show (Z p)
deriving via (Z' p 20) instance Radix p => Enum (Z p)
deriving via (Z' p 20) instance Radix p => Real (Z p)
deriving via (Z' p 20) instance Radix p => Integral (Z p)
deriving via (Z' p 20) instance Radix p => Fixed (Z p)
deriving via (Z' p 20) instance Radix p => Padic (Z p)

instance Radix p => Digital (Z p) where
  type Dig (Z p) = Digits p
  base = fromIntegral . natVal
  digits n = unliftRadix n
  fromDigits = Z . liftRadix

liftRadix :: Radix p => Digits p -> Digits (LiftedRadix p)
liftRadix ds = res 
  where
    res = Inf.unfoldr go ds
    go xs = let (a, r) = Inf.splitAt k xs
            in (fromRadix b a, r)
    b = base (Inf.head ds)
    k = ilog b (base (Inf.head res))

unliftRadix :: Radix p => Z p -> Digits p
unliftRadix (Z ds) = Inf.concatMap expand ds
  where
    expand d = res
      where
        res | d == 0 = 0 <$ toRadix b (base d `div` b)
            | otherwise = toRadix b (unMod d)
        b = base (head res)

ilog a b = floor (logBase (fromIntegral a) (fromIntegral b))

plog a b | b `mod` a == 0 = 1 + plog a (b `div` a)
         | otherwise = 0

instance Radix p => Num (Z p) where
  fromInteger = toZ
  abs = id
  signum 0 = 0
  signum _ = 1
  Z a + Z b = Z $ addZ a b
  Z a * Z b = Z $ mulZ a b
  negate (Z a) = Z (negZ a)

-- превращает целое число в p-адическое
toZ :: Radix p => Integer -> Z p
toZ n | n < 0 = - toZ (- n)
      | otherwise = Z $ d ::: ds 
  where
    d ::: ds = toRadix (base d) n +++ Inf.repeat 0

-- преобразование целого числа в цифры по указанному основанию
toRadix :: (Integral i, Integral d) => i -> i -> [d]
toRadix _ 0 = [0]
toRadix b n = unfoldr go n 
  where
    go 0 = Nothing
    go x = let (q, r) = quotRem x b
           in Just (fromIntegral r, q)

fromRadix :: (Integral i, Integral d) => i -> [d] -> i
fromRadix b = foldr (\x r -> fromIntegral x + r*b) 0

-- смена знака на противоположный
negZ :: ValidRadix p => Digits p -> Digits p
negZ = go
  where go (0 ::: t) = 0 ::: go t
        go (h ::: t) = - h ::: Inf.map (\x -> - x - 1) t

-- выделяет из натурального числа перенос на следующий разряд
carry :: (ValidRadix p, Integral i) => i -> (i, Mod p)
carry n = let d = fromIntegral n in (n `div` base d, d)
    
-- поразрядное сложение с переносом
addZ :: ValidRadix p => Digits p -> Digits p -> Digits p
addZ a b = Inf.mapAccumL step 0 $ Inf.zip a b
  where
    step r (x, y) = carry (unMod x + unMod y + r)

-- поразрядное умножение с переносом
mulZ :: ValidRadix p => Digits p -> Digits p -> Digits p
mulZ a = go
  where
    go (b ::: bs) = addZ (go bs) `apTail` scaleZ b a
    apTail f (h ::: t) = h ::: f t

-- поразрядное умножение на цифру с переносом
scaleZ :: ValidRadix p => Mod p -> Digits p -> Digits p
scaleZ s =
  Inf.mapAccumL (\r x -> carry (unMod s * unMod x + r)) 0

divMaybe :: Radix p => Z p -> Z p -> Maybe (Z p)
divMaybe (Z a) (Z b) = Z <$> divZ a b

-- поразрядное деление двух чисел "уголком"
divZ :: ValidRadix p => Digits p -> Digits p -> Maybe (Digits p)
divZ a (b ::: bs) = go a <$ invertMod b
  where
    Just r = invertMod b
    go (0 ::: xs) = 0 ::: go xs
    go xs =
      let m = Inf.head xs * r
          mulAndSub = addZ xs . negZ . scaleZ m 
      in m ::: go (Inf.tail $ mulAndSub (b ::: bs))

------------------------------------------------------------

newtype Z' (p :: Nat) (prec :: Nat) = Z' {getZ :: (Z p)}

deriving via Z p instance Radix p => Digital (Z' p prec)
deriving via Z p instance Radix p => Num (Z' p prec)
  
instance KnownNat prec => Fixed (Z' p prec) where
  precision = fromIntegral . natVal

instance (KnownNat prec, Radix p) => Padic (Z' p prec) where
  splitUnit (Z' n) = go p (digits n)
    where
      p = precision n
      go 0 _ = (fromDigits $ Inf.repeat 0, maxBound)
      go k x = case x of
        0 ::: ds -> go (k-1) ds
        _        -> (fromDigits x, p - k)

instance (KnownNat prec, Radix p) => Eq (Z' p prec) where
  x@(Z' a) == Z' b = Inf.take pr (digits a) == Inf.take pr (digits b)
    where
      pr = precision x

instance (KnownNat prec, Radix p) => Ord (Z' p prec) where
  compare = error "ordering is not defined for Z"

instance (KnownNat prec, Radix p) => Show (Z' p prec) where
  show n = process . reverse . map unMod . Inf.take pr $ digits n
    where
      pr = precision n
      process lst = case dropWhile (== 0) lst of
        [] -> "0"
        l -> ell l ++ intercalate sep (show  <$> l)
      ell l = if length l < pr then "" else "…"
      sep = if base n < 11 then "" else " "
      -- sub = ("₀₁₂₃₄₅₆₇₈₉" !!) <$> reverse (toRadix 10 b)

instance (KnownNat prec, Radix p) => Enum (Z' p prec) where
  toEnum = fromIntegral
  fromEnum = fromIntegral . toInteger

instance (KnownNat prec, Radix p) => Real (Z' p prec) where
  toRational = fromIntegral . toInteger

instance (KnownNat prec, Radix p) => Integral (Z' p prec) where
  toInteger n =
    case integerDigits n of
      Right xs -> foldl (\r x -> x + r*base n) 0 xs
      Left xs -> foldl (\r x -> x + 1 + (r - 1)*base n) 0 xs - 1
  
  div (Z' a) d@(Z' b) = case divMaybe a b of
    Just r -> Z' r
    Nothing -> error $
      show d ++ " is indivisible in " ++ show (base d) ++ "-adics!"

  quotRem = error "quotRem is not defined for p-adics!" 

integerDigits :: (KnownNat prec, Radix p, Integral a) => Z' p prec -> Either [a] [a]
integerDigits n = go [] windows
  where
    b = base n
    chop = precision n
    windows = map (take (1 + fromIntegral chop)) $
              tails $ map unMod $ Inf.toList (digits n)
    go r ((x:xs):ws) = case sum xs of
      s | s == 0            -> Right (fromIntegral x:r)
        | s == (b - 1)*chop -> Left (fromIntegral x:r)
        | otherwise         -> go (fromIntegral x:r) ws 
