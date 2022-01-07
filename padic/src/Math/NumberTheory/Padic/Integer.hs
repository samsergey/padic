{-# OPTIONS_HADDOCK hide, prune, ignore-exports #-}

{-# LANGUAGE DataKinds #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE UnliftedFFITypes #-}
{-# LANGUAGE NoStarIsType #-}
{-# LANGUAGE LambdaCase #-}

module Math.NumberTheory.Padic.Integer  where

import Data.List
import Data.Mod
import Data.Maybe (listToMaybe)
import Data.Ratio
import GHC.TypeLits hiding (Mod)
import GHC.Integer.GMP.Internals (recipModInteger)
import Data.Constraint (Constraint)

import Math.NumberTheory.Padic.Classes

------------------------------------------------------------
type family Lifted p prec where
  Lifted p prec = p ^ (2*prec + 1)

type family LiftedRadix p prec :: Constraint where
  LiftedRadix p prec =
    ( KnownNat prec
    , KnownNat p
    , ValidRadix p
    , KnownNat (p ^ (2*prec + 1))
    , ValidRadix (p ^ (2*prec + 1))
    )

-- |  Integer p-adic number (an element of \(\mathbb{Z}_p\)) with 20 digits precision.
type Z p = Z' p 20

-- |  Integer p-adic number with explicitly specified precision.
newtype Z' (p :: Nat) (prec :: Nat) = Z' (Z_ prec p)

newtype Z_ (prec :: Nat ) (p :: Nat) = Z_ [Mod (Lifted p prec)]

instance (Radix p, LiftedRadix p prec) => Padic (Z' p prec) where
  type Unit (Z' p prec) = Z' p prec
  type LiftedDigits (Z' p prec) = [Mod (Lifted p prec)]
  type Digit (Z' p prec) = Mod p 

  {-# INLINE precision #-}
  precision = fromIntegral . natVal

  {-# INLINE  radix #-}
  radix (Z' n) = fromIntegral $ natVal n
  
  fromDigits ds = res
    where
      res = mkUnit $ unfoldr go $ ds ++ repeat 0
      go lst = let (a, b) = splitAt (chunks res) lst
               in Just (fromInteger $ fromRadix a, b)
      chunks n = ilog (radix n) (liftedRadix n)
      
  digits (Z' (Z_ ds)) = ds >>= toRadix . lifted

  {-# INLINE lifted #-}
  lifted (Z' (Z_ ds)) = ds

  {-# INLINE mkUnit #-}
  mkUnit = Z' . Z_ 

  {-# INLINE fromUnit #-}
  fromUnit (u, v) = fromIntegral (radix u ^ v) * u

  splitUnit n | n == 0 = (0, precision n)
              | otherwise = (n, 0)
  
  isInvertible n@(Z' (Z_ (d:_))) = (unMod d `mod` p) `gcd` p == 1
    where
      p = radix n
  isInvertible _ = False
  
  inverse n | isInvertible n = Just (1 `div` n)
            | otherwise = Nothing

instance LiftedRadix p prec => Show (Z' p prec) where
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

instance LiftedRadix p prec => Eq (Z' p prec) where
  x@(Z' (Z_ (a:_))) == Z' (Z_ (b:_)) = unMod a `mod` pk == unMod b `mod` pk
    where
      pk = radix x ^ precision x
  _ == _ = False
  
instance LiftedRadix p prec => Num (Z' p prec) where
  fromInteger n
    | n < 0 = -fromInteger (-n)
    | otherwise = mkUnit (d:ds)
    where
      d:ds = toRadix  n ++ repeat 0
  abs = id
  signum 0 = 0
  signum _ = 1
  Z' (Z_ a) + Z' (Z_ b) = Z' . Z_ $ addZ a b
  Z' (Z_ a) * Z' (Z_ b) = Z' . Z_ $ mulZ a b
  negate (Z' (Z_ a)) = Z' (Z_ (negZ a))

negZ :: KnownNat p => [Mod p] -> [Mod p]
{-# INLINE negZ #-}
negZ = go
  where
    go [] = []
    go (0:t) = 0 : go t
    go (h:t) = -h : map (\x -> -x - 1) t

carry :: (KnownNat p, Integral i) => i -> (i, Mod p)
{-# INLINE carry #-}
carry n =
  let d = fromIntegral n
   in (n `div` fromIntegral (natVal d), d)

addZ :: KnownNat p => [Mod p] -> [Mod p] -> [Mod p]
{-# INLINE addZ #-}
addZ a b = snd $ mapAccumL step 0 $ zip a b
  where
    step r (x, y) = carry (unMod x + unMod y + r)

mulZ :: KnownNat p => [Mod p] -> [Mod p] -> [Mod p]
{-# INLINE mulZ #-}
mulZ a = go
  where
    go [] = []
    go (b:bs) = addZ (go bs) `apTail` scaleZ b a
    apTail f (h:t) = h : f t

scaleZ :: KnownNat p => Mod p -> [Mod p] -> [Mod p]
{-# INLINE scaleZ #-}
scaleZ s =
  snd . mapAccumL (\r x -> carry (unMod s * unMod x + r)) 0


instance LiftedRadix p prec  => Enum (Z' p prec) where
  toEnum = fromIntegral
  fromEnum = fromIntegral . toInteger

instance LiftedRadix p prec => Real (Z' p prec) where
  toRational 0 = 0
  toRational n@(Z' (Z_ (d:_))) = extEuclid (lifted d, liftedRadix n)
  toRational _ = 0

instance LiftedRadix p prec => Integral (Z' p prec) where
  toInteger n@(Z' (Z_ (d:_))) =
    if denominator r == 1
    then numerator r
    else lifted d `mod` (radix n ^ precision n)
    where
      r = toRational n
      
  a `quotRem` b = case divMaybe a b of
    Nothing -> error $ show b ++ " is not insertible mod " ++ show (radix a) 
    Just q -> (q, a - q * b)

-- Division which does not raize exceptions.
divMaybe :: LiftedRadix p prec => Z' p prec -> Z' p prec -> Maybe (Z' p prec)
divMaybe (Z' (Z_ a)) (Z' (Z_ b)) = Z' . Z_ <$> divZ a b

divZ :: Radix p => [Mod p] -> [Mod p] -> Maybe ([Mod p])
divZ _ [] = Nothing
divZ a (b:bs) = go a <$> invertMod b
  where
    go (0:xs) r = 0 : go xs r
    go xs r =
      let m = head xs * r
          mulAndSub = addZ xs . negZ . scaleZ m
       in m : go (tail $ mulAndSub (b : bs)) r

instance LiftedRadix p prec => Ord (Z' p prec) where
  compare = error "ordering is not defined for Z"

------------------------------------------------------------

-- | For a given list extracts prefix and a cycle, limiting length of prefix and cycle by @len@.
-- Uses the modified tortiose and hare method.
findCycle :: Eq a => Int -> [a] -> Maybe ([a], [a])
findCycle len lst =
  case tortoiseHare rest of
    Just (a, c) -> test $ clean $ rollback (pref ++ a, c)
    Nothing -> Nothing
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
    test (_, []) = Nothing 
    test (pref, c)
      | and $ zipWith (==) (take (2*len) lst) (pref ++ cycle c) = Just (pref, c)
      | otherwise = Nothing

 
