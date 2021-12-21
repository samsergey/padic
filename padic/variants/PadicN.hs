{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE DerivingVia #-}
{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE GADTs #-}


module PadicN where

import           GHC.TypeLits
import           GHC.Integer.GMP.Internals (recipModInteger)
import           Data.Constraint (Constraint)
import           Data.InfList (InfList(..), (+++))
import qualified Data.InfList as Inf
import           Data.List
import           Data.Word

------------------------------------------------------------

type family NonZeroNat (m :: Nat) :: Constraint where
  NonZeroNat 0 = TypeError ('Text "Zero base!")
  NonZeroNat m = ()

type family Base (m :: Nat) :: Constraint where
  Base m = (NonZeroNat m, KnownNat m)

------------------------------------------------------------

type Digits p = InfList (Digit p)
  
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
type N = Word64

maxBase p = p ^ (ilog p (maxBound :: N) - 1)

ilog a b = floor (logBase (fromIntegral a)(fromIntegral b))
  
newtype Digit (m :: Nat) = Digit N
  deriving (Show, Eq, Ord, Num, Real, Integral) via N

instance Base m => Bounded (Digit m) where
  minBound = 0
  maxBound = let res = base res - 1 in res

instance Base m => Enum (Digit m) where
  toEnum = fromIntegral
  fromEnum = fromIntegral . toInteger
  enumFrom a = [a..maxBound]

instance Base p => Digital (Digit p) where
  digits = undefined
  base = fromIntegral . natVal

------------------------------------------------------------

newtype Z p = Z { getDigits :: Digits p }

deriving via (Z' p 20) instance Base p => Eq (Z p)
deriving via (Z' p 20) instance Base p => Show (Z p)

instance Base p => Digital (Z p) where
  type Dig (Z p) = Digits p
  digits n = extractDigits n
  base = fromIntegral . natVal

extractDigits :: Base p => Z p -> Digits p
extractDigits (Z ds) = Inf.concatMap expand ds
  where
    expand d = res
      where
        res | d == 0 = 0 <$ toBase b (maxBase b `div` b)
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
    res = Z $ toBase (maxBase (base res)) (fromInteger n) +++ Inf.repeat 0


-- преобразование целого числа в цифры по указанному основанию
toBase :: (Integral i, Integral d) => i -> i -> [d]
toBase _ 0 = [0]
toBase b n = unfoldr go n 
  where
    go 0 = Nothing
    go x = let (q, r) = quotRem x b
           in Just (fromIntegral r, q)

-- смена знака на противоположный
negZ :: Base p => Digits p -> Digits p
negZ ds = go ds
  where go (0 ::: t) = 0 ::: go t
        go (h ::: t) = p - h ::: Inf.map (\x -> p - x - 1) t
        p = maxBase (base (Inf.head ds))

-- выделяет из натурального числа перенос на следующий разряд
carry :: (Base p, Integral i) => i -> (i, Digit p)
carry n = (n `div` b, d)
  where
    b = maxBase (base d)
    d = fromIntegral (n `mod` b)

-- поразрядное сложение с переносом
addZ :: Base p => Digits p -> Digits p -> Digits p
addZ a b = Inf.mapAccumL step 0 $ Inf.zip a b
  where
    step r (x, y) = carry (fromIntegral x + fromIntegral y + r)

-- поразрядное умножение с переносом
mulZ :: Base p => Digits p -> Digits p -> Digits p
mulZ a = go
  where
    go (b ::: bs) = addZ (go bs) `apTail` scaleZ b a
    apTail f (h ::: t) = h ::: f t

-- поразрядное умножение на цифру с переносом
scaleZ :: Base p => Digit p -> Digits p -> Digits p
scaleZ s =
  Inf.mapAccumL (\r x -> carry (fromIntegral s * fromIntegral x + r)) 0

instance Base p => Fractional (Z p) where
  Z a / d@(Z b) = case divZ a b of
    Just r -> Z r
    Nothing -> error $ show d ++ " is indivisible in Z " ++ show (base d)
  fromRational = undefined

divMaybe :: Base p => Z p -> Z p -> Maybe (Z p)
divMaybe (Z a) (Z b) = Z <$> divZ a b

-- поразрядное деление двух чисел "уголком"
divZ :: Base p => Digits p -> Digits p -> Maybe (Digits p)
divZ a (b ::: bs) = go a <$ invertMod b
  where
    Just r = invertMod b
    go (0 ::: xs) = 0 ::: go xs
    go xs =
      let m = (Inf.head xs * r) `mod` maxBase (base b)
          mulAndSub = addZ xs . negZ . scaleZ m 
      in m ::: go (Inf.tail $ mulAndSub (b ::: bs))


invertMod :: Base p => Digit p -> Maybe (Digit p)
invertMod x@(Digit d)
  | gcd d b == 1 =
      Just (Digit $ fromInteger $ recipModInteger (fromIntegral d) (fromIntegral b))
  | otherwise = Nothing
  where
    b = maxBase (base x)

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
      b = base n
      process lst = case dropWhile (== 0) lst of
        [] -> "0"
        l -> ell l ++ intercalate sep (show  <$> l)
      ell l = if length l < pr then "" else "…"
      sep = if b < 11 then "" else " "
      -- sub = ("₀₁₂₃₄₅₆₇₈₉" !!) <$> reverse (toBase 10 b)

instance (KnownNat prec, Base p) => Ord (Z' p prec) where
  compare = error "ordering is not defined for Z"
