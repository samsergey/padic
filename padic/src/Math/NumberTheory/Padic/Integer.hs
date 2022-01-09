{-# OPTIONS_HADDOCK hide, prune, ignore-exports #-}

{-# LANGUAGE DataKinds #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE LambdaCase #-}

module Math.NumberTheory.Padic.Integer where

import Data.List (mapAccumL, intercalate, unfoldr)
import Data.Mod
import Data.Word (Word32)
import Data.Maybe (listToMaybe)
import Data.Ratio
import GHC.TypeLits (Nat, natVal)
import GHC.Integer.GMP.Internals (recipModInteger)
import Math.NumberTheory.Padic.Classes

------------------------------------------------------------
-- |  Integer p-adic number (an element of \(\mathbb{Z}_p\)) with default 20-digit precision.
type Z p = Z' p 20

-- |  Integer p-adic number with explicitly specified precision.
newtype Z' (p :: Nat) (prec :: Nat) = Z' (R prec p)
newtype R (prec :: Nat ) (p :: Nat) = R [Mod (LiftedRadix p prec)]

instance Radix p prec => PadicNum (Z' p prec) where
  type Unit (Z' p prec) = Z' p prec
  type Lifted (Z' p prec) = [Mod (LiftedRadix p prec)]
  type Digit (Z' p prec) = Mod p 

  {-# INLINE precision #-}
  precision = fromIntegral . natVal

  {-# INLINE  radix #-}
  radix (Z' r) = fromIntegral $ natVal r
  
  fromDigits ds = res
    where
      res = mkUnit $ unfoldr go $ ds ++ repeat 0
      go lst = let (a, b) = splitAt (chunks res) lst
               in Just (fromInteger $ fromRadix a, b)
      chunks n = ilog (radix n) (liftedRadix n)
      
  digits (Z' (R ds)) = ds >>= toRadix . lifted

  {-# INLINE lifted #-}
  lifted (Z' (R ds)) = ds

  {-# INLINE mkUnit #-}
  mkUnit = Z' . R 

  {-# INLINE fromUnit #-}
  fromUnit (u, v) = fromIntegral (radix u ^ v) * u

  splitUnit n = go (lifted n) 0
    where
      go _ k | k >= pr = zero
      go (d:ds) k = case getUnitZ p (lifted d) of
        (0, 0) -> go ds (k + ilog p (radix d))
        (d', k')
          | k + k' >= pr -> zero
          | otherwise ->
            let s = fromIntegral (p^k')
            in (mkUnit (shiftL s (fromIntegral d':ds)), k + k')
      p = radix n
      pr = precision n
      zero = (0, pr)
  
  isInvertible n@(Z' (R (d:_))) = (unMod d `mod` p) `gcd` p == 1
    where
      p = radix n
  isInvertible _ = False
  
  inverse n | isInvertible n = Just (1 `div` n)
            | otherwise = Nothing

shiftL :: KnownRadix p => Mod p -> [Mod p] -> [Mod p]
shiftL s (d1:d2:ds) =
  let (q, r) = quotRem (lifted d2) (lifted s)
      pk = fromIntegral (radix s `div` lifted s)
  in d1 + fromIntegral r * pk : shiftL s (fromIntegral q : ds)

instance Radix p prec => Show (Z' p prec) where
  show n = 
     case findCycle pr ds of
       Nothing -> ell ++ toString (take pr ds)
       Just ([],[0]) -> "0"
       Just (pref, [0]) -> toString pref
       Just (pref, cyc)
        | length pref + length cyc <= pr ->
          let sp = toString pref
              sc = toString cyc
           in "(" ++ sc ++ ")" ++ sep ++ sp
        | otherwise -> ell ++ toString (take pr $ pref ++ cyc)
    where
      pr = precision n
      ds = digits n
      showD = show . unMod
      toString = intercalate sep . map showD . reverse
      ell = "…" ++ sep 
      sep
        | radix n < 11 = ""
        | otherwise = " "

instance Radix p prec => Eq (Z' p prec) where
  x@(Z' (R (a:_))) == Z' (R (b:_)) = unMod a `mod` pk == unMod b `mod` pk
    where
      pk = radix x ^ precision x
  _ == _ = False
  
instance Radix p prec => Num (Z' p prec) where
  fromInteger n
    | n < 0 = -fromInteger (-n)
    | otherwise = mkUnit (d:ds)
    where
      d:ds = toRadix  n ++ repeat 0
  abs = id
  signum 0 = 0
  signum _ = 1
  Z' (R a) + Z' (R b) = Z' . R $ addZ a b
  Z' (R a) * Z' (R b) = Z' . R $ mulZ a b
  negate (Z' (R a)) = Z' (R (negZ a))

negZ :: KnownRadix p => [Mod p] -> [Mod p]
{-# INLINE negZ #-}
negZ = go
  where
    go [] = []
    go (0:t) = 0 : go t
    go (h:t) = -h : map (\x -> -x - 1) t

carry :: (KnownRadix p, Integral i) => i -> (i, Mod p)
{-# INLINE carry #-}
carry n =
  let d = fromIntegral n
   in (n `div` fromIntegral (natVal d), d)

addZ :: KnownRadix p => [Mod p] -> [Mod p] -> [Mod p]
{-# INLINE addZ #-}
addZ a b = snd $ mapAccumL step 0 $ zip a b
  where
    step r (x, y) = carry (unMod x + unMod y + r)

mulZ :: KnownRadix p => [Mod p] -> [Mod p] -> [Mod p]
{-# INLINE mulZ #-}
mulZ a = go
  where
    go [] = []
    go (b:bs) = addZ (go bs) `apTail` scaleZ b a
    apTail f (h:t) = h : f t

scaleZ :: KnownRadix p => Mod p -> [Mod p] -> [Mod p]
{-# INLINE scaleZ #-}
scaleZ s =
  snd . mapAccumL (\r x -> carry (unMod s * unMod x + r)) 0


instance Radix p prec  => Enum (Z' p prec) where
  toEnum = fromIntegral
  fromEnum = fromIntegral . toInteger

instance Radix p prec => Real (Z' p prec) where
  toRational 0 = 0
  toRational n@(Z' (R (d:_))) = extEuclid (lifted d, liftedRadix n)
  toRational _ = 0

instance Radix p prec => Integral (Z' p prec) where
  toInteger n@(Z' (R (d:_))) =
    if denominator r == 1
    then numerator r
    else lifted d `mod` (radix n ^ precision n)
    where
      r = toRational n
      
  a `quotRem` b = case divMaybe a b of
    Nothing -> error $ show b ++ " is not insertible mod " ++ show (radix a) 
    Just q -> (q, a - q * b)

-- Division which does not raize exceptions.
divMaybe :: Radix p prec => Z' p prec -> Z' p prec -> Maybe (Z' p prec)
divMaybe (Z' (R a)) (Z' (R b)) = Z' . R <$> divZ a b

divZ :: KnownRadix p => [Mod p] -> [Mod p] -> Maybe [Mod p]
divZ _ [] = Nothing
divZ a (b:bs) = go a <$> invertMod b
  where
    go (0:xs) r = 0 : go xs r
    go xs r =
      let m = head xs * r
          mulAndSub = addZ xs . negZ . scaleZ m
       in m : go (tail $ mulAndSub (b : bs)) r

instance Radix p prec => Ord (Z' p prec) where
  compare = error "ordering is not defined for Z"
