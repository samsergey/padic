{-# LANGUAGE DerivingVia #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE NoStarIsType #-}

module Math.NumberTheory.Padic.Short where

import GHC.TypeLits hiding (Mod)
import Data.Constraint (Constraint)
import Data.Word
import Data.List

newtype Mod (p :: Nat) = Mod Integer

instance KnownNat p => Show (Mod p) where
  show n@(Mod x) = show (x `mod` p) ++ " mod " ++ show p
    where p = fromIntegral (natVal n)

instance KnownNat p => Num (Mod p) where
  fromInteger n = let res = Mod $ n `mod` natVal res in res
  Mod a + Mod b = let res = Mod $ (a + b) `mod` natVal res in res
  Mod a - Mod b = let res = Mod $ (a - b) `mod` natVal res in res
  Mod a * Mod b = let res = Mod $ (a * b) `mod` natVal res in res
  negate (Mod a) = let res = Mod (natVal res - a) in res
  abs = id
  signum _ = 1

-- Ограничение на допустимые значения основания
type family ValidRadix (m :: Nat) :: Constraint where
  ValidRadix 0 = TypeError ('Text "Zero radix!")
  ValidRadix 1 = TypeError ('Text "Radix should be more then 1!")
  ValidRadix m = ()

-- Основание для внутреннего представления p-адического числа
type family LiftedRadix p prec where
  LiftedRadix p prec = p ^ (2*prec + 1)

-- Ограничение для основания p-адического числа с точностью prec
type family Radix p prec :: Constraint where
  Radix p prec =
    ( KnownNat prec
    , KnownNat p, ValidRadix p
    , KnownNat (LiftedRadix p prec), ValidRadix (LiftedRadix p prec) )

-- Точность, необходимая для восстановления рациональных чисел 
-- с числителем и знаменателем, принадлежащим  типу num
type family SufficientPrecision num (p :: Nat) :: Nat where
  SufficientPrecision Word32 2 = 64
  SufficientPrecision Word32 3 = 43
  SufficientPrecision Word32 5 = 30
  SufficientPrecision Word32 6 = 26
  SufficientPrecision Word32 7 = 24
  SufficientPrecision t p = Div (SufficientPrecision t 2) (Log2 p)

newtype Z' (p :: Nat) (prec :: Nat) = Z' (R prec p)

newtype R (prec :: Nat ) (p :: Nat) = R (Mod (LiftedRadix p prec))

type Z p = Z' p (SufficientPrecision Word32 p)

deriving via (R p prec) instance Radix p prec => Num (Z' p prec)
deriving via (Mod (LiftedRadix p prec)) instance Radix p prec => Num (R p prec)

precision :: (Radix p prec, Integral i) => Z' p prec -> i
precision z = fromIntegral (natVal z)

radix :: (Radix p prec, Integral i) => Z' p prec -> i
radix (Z' r) = fromIntegral (natVal r)

toRadix :: Integer -> Integer -> [Int]
toRadix _ 0 = [0]
toRadix p n = unfoldr go n
  where
    go 0 = Nothing
    go x =
      let (q, r) = quotRem x p
      in Just (fromIntegral r, q)
 
instance Radix p prec => Show (Z' p prec) where
  show n@(Z' (R (Mod x))) = foldMap show $
                            reverse $
                            take (precision n) $
                            toRadix (radix n) x
