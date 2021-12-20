{-# LANGUAGE IncoherentInstances #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE DataKinds  #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE UndecidableSuperClasses #-}
module Padic where

import Data.Ratio
import Data.Mod
import Data.List.NonEmpty (NonEmpty(..), fromList, toList)
import Data.List
import GHC.TypeLits hiding (Mod)
import Data.Constraint
import Control.Monad
import Test.QuickCheck

type family CheckBase (m :: Nat) :: Constraint where
  CheckBase 0 = TypeError ('Text "Zero modulo base!")
  CheckBase m = ()

type ModBase m = (CheckBase m, KnownNat m)

instance ModBase m => Real (Mod m) where
   toRational = toRational . fromIntegral . unMod

instance ModBase m => Integral (Mod m) where
   toInteger = fromIntegral . unMod
   quotRem a b = (fromIntegral q, fromIntegral r)
     where
       (q, r) = fromIntegral a `quotRem` fromIntegral b
  
------------------------------------------------------------

class (Num (n m), ModBase m) => Digital n m where
  digitsM     :: n m -> [Mod m]
  fromDigitsM :: [Mod m] -> n m
  base        :: Integral i => n m -> i
  isZero      :: Num (n m)  => n m -> Bool
  
  base = fromIntegral . natVal 
  isZero = all (== 0) . take 20 . digits 

digits :: (Digital n m, Integral i) => n m -> [i]
digits = map fromIntegral . digitsM

fromDigits :: (Digital n m, Integral i) => [i] -> n m
fromDigits = fromDigitsM . map fromIntegral

instance (Num (n m), Digital n m) => Eq (n m) where
  a == b = isZero (a - b)

------------------------------------------------------------

newtype Base (b :: Nat) = Base (NonEmpty (Mod b))

instance ModBase b => Digital Base b where
  digitsM (Base ds) = toList ds 

  fromDigitsM [] = Base . fromList $ repeat 0
  fromDigitsM ds = Base . fromList $ ds ++ repeat (last ds)

instance ModBase m => Show (Base m) where
  show = process . reverse . take 20 . digits
    where
      process lst = case dropWhile (== 0) lst of
        [] -> "0"
        l -> foldMap showDigit l

showDigit n = pure $ (['0'..'9']++['a'..'z']) !! fromIntegral n

instance ModBase b => Num (Base b) where
  fromInteger n | n < 0 = - fromInteger (-n)
                | otherwise = res
    where
      res = fromDigits $ unfoldr go n
      go n = let (q, r) = quotRem n b in Just (fromIntegral r, q)
      b = base res

  a + b = 
    fromDigits $ addDigits (base a) (digits a) (digits b)

  a * b = 
    fromDigits $ mulDigits (base a) (digits a) (digits b)

  negate a = 1 + fromDigits ((base a - 1 -) <$> digits a)

  abs = id
  signum = const 1

instance ModBase m => Enum (Base m) where
  toEnum = fromInteger . fromIntegral
  fromEnum = fromIntegral . toInteger
  enumFrom a = [a..base a - 1]

instance ModBase m => Ord (Base m) where
  compare = error "ordering is not defined for Base"

instance ModBase m => Real (Base m) where
  toRational = toRational . fromIntegral

instance ModBase m => Integral (Base m) where
  toInteger n =
    case integerDigits n of
      Right xs -> foldl (\r x -> x + r*base n) 0 xs
      Left xs -> foldl (\r x -> x + 1 + (r - 1)*base n) 0 xs - 1
      
  quotRem a b = (fromIntegral q, fromIntegral r)
    where
      (q, r) = toInteger a `quotRem` toInteger b

  div a b = fromDigits res
    where
      res = divDigits (base a) (digits a) (digits b) (fromIntegral r)
      r = recip $ head $ digitsM b

integerDigits n = process [] windows
  where
    b = base n
    chop = floor (log (fromIntegral $ (maxBound :: Int)) / log (fromIntegral b))
    windows = take (1 + fromIntegral chop) <$> tails (digits n)
    process r ((x:xs):ws) = case sum xs of
      s | s == 0            -> Right (x:r)
        | s == (b - 1)*chop -> Left (x:r)
        | otherwise         -> process (x:r) ws 

addDigits :: Integral a => a -> [a] -> [a] -> [a]
addDigits m = go 0
  where
    go s (x:xs) (y:ys) =
      let r = x + y + s 
      in r `mod` m : go (r `div` m) xs ys

negDigits :: Integral a => a -> [a] -> [a]
negDigits m (x:xs) = m - x : ((m - 1 -) <$> xs)

scaleDigits :: Integral a => a -> a -> [a] -> [a]
scaleDigits m a = go 0
  where
    go s (b:bs) =
      let (q, r) = (a * b + s) `divMod` m
      in r : go q bs

mulDigits :: Integral a => a -> [a] -> [a] -> [a]
mulDigits m a b = go b
  where
    go (b:bs) =
      let c:cs = scaleDigits m b a
      in c : ((`mod` m) <$> addDigits m (go bs) cs)

fact :: (Digital f m, ModBase m) => [f m]
fact = res
  where
    res = fromIntegral <$> series
    p = base (head res)
    series = scanl (*) 1 $ filter (\x -> x `mod` p /= 0) [1..]

fixedPoint f = limit . take 100 . iterate f

------------------------------------------------------------


data Qp (p :: Nat) = Qp { unit :: Base p
                        , val :: Int }

instance ModBase b => Digital Qp b where
  digitsM = digitsM . unit
  fromDigitsM = mkUnit

instance ModBase p => Show (Qp p) where
  show x@(Qp u v) = i ++ "." ++ f
    where
      (f,i) = case compare v 0 of
        EQ -> ("0", show u)
        LT -> splitAt (-v) (show u)
        GT | v < 20 -> ("0", drop v (show u ++ replicate v '0'))
           | otherwise -> ("0", "0")

-- Constructor for zero value
pZero :: ModBase p => Qp p
pZero = Qp (fromDigits (repeat 0)) maxBound

-- Constructor for p-adic unit
mkUnit :: ModBase p => [Mod p] -> Qp p
mkUnit u = normalize $ Qp (fromDigits u) 0

-- Smart constructor, adjusts trailing zeros with the valuation.
normalize :: ModBase p => Qp p -> Qp p
normalize (Qp u v) = go 0 (digits u)
  where
    go 17 _ = pZero
    go i (0:u) = go (i+1) u
    go i u = Qp (fromDigits u) (v+i)

-- extracts p-adic unit from a rational number
getUnit :: Integral i => i -> Ratio i -> (Int, Ratio i)
getUnit p x = (genericLength v2 - genericLength v1, c) 
  where
    (v1,b:_) = span (\n -> denominator n `mod` p == 0) $
               iterate (* fromIntegral p) x
    (v2,c:_) = span (\n -> numerator n `mod` p == 0) $
               iterate (/ fromIntegral p) b

instance ModBase p => Num (Qp p) where
  fromInteger = fromRational . fromInteger

  Qp a va + Qp b vb = normalize $ Qp u v
    where
      v = va `min` vb
      u = shift (va - v) a + shift (vb - v) b  
      shift i x = fromDigits $ replicate i 0 ++ digits x
      
  negate (Qp u v) = Qp (negate u) v

  Qp a va * Qp b vb = normalize $ Qp (a * b) (va + vb)

  abs = undefined
  signum = undefined
  
instance ModBase p => Fractional (Qp p)  where
  fromRational 0 = pZero
  fromRational x = normalize res 
    where
      res = Qp (fromDigitsM (series n)) v
      p = base res
      (v, q) = getUnit p x
      (n, d) = ( fromIntegral $ numerator q
               , fromIntegral $ denominator q)
      series 0 = repeat 0
      series n =
        let m = fromIntegral n / fromIntegral d
        in m : series ((n - fromIntegral m * d) `div` p)

  a / b = Qp (fromDigits res) (val a - val b)
    where
      res = case invertMod (head (digitsM b)) of
        Nothing -> error "@@@"
        Just r -> divDigits (base a) (digits a) (digits b) (fromIntegral r)

divDigits p a b r = go a
  where
    go [] = []
    go (0:xs) = 0 : go xs
    go (x:xs) =
      let m = (x*r) `mod` p
          s = scaleDigits p m b
          _:zs = addDigits p (x:xs) (negDigits p s)
      in m `mod` p : go zs


newton f df = iterate (\x -> x - f x / df x)

limit (x:y:z) | x == y = Just x
              | otherwise = limit (y:z)
limit _ = Nothing

------------------------------------------------------------

--findCycle :: Eq a => [a] -> ([a], [a])
findCycle len lst = rollback (pref ++ a, c)
  where
    (pref, rest) = splitAt 16 lst
    (a, c) = turlteHare rest
    
    turlteHare lst =
      fmap fst . head $ 
      dropWhile (\(p, (a, b)) -> isCycle a b) $
      zip (inits lst) $
      zipWith splitAt [1..len] $
      zipWith take [4,8..] $
      tails lst

    isCycle a b = concat (replicate 3 a) /= b
    
    rollback (as, bs) = go (reverse as) (reverse bs)
      where
        go [] bs = ([], reverse bs)
        go (a:as) (b:bs)
          | a == b = go as (bs ++ [a])
          | otherwise = (reverse (a:as), reverse (b:bs))

------------------------------------------------------------

intHomo :: Integral a => a -> Integer -> Bool
intHomo t a = let [x,_] = [fromInteger a,t]
              in toInteger x == a

addHomo :: (Eq a, Num a) => a -> Integer -> Integer -> Bool
addHomo t a b = let [x,y,_] = [fromInteger a, fromInteger b, t]
                in x + y == fromInteger (a + b)

mulHomo :: (Eq a, Num a) => a -> Integer -> Integer -> Bool
mulHomo t a b = let [x,y,_] = [fromInteger a, fromInteger b, t]
                in x * y == fromInteger (a * b)

addComm :: (Eq a, Num a) => a -> a -> Bool
addComm a b = a + b == b + a

addAssoc :: (Eq a, Num a) => a -> a -> a -> Bool
addAssoc a b c = a + (b + c) == (a + b) + c

negInvol ::  (Eq a, Num a) => a -> Bool
negInvol a = - (- a) == a

negInvers :: (Eq a, Num a) => a -> Bool
negInvers a = a - a == 0

mulZero :: (Eq a, Num a) => a -> Bool
mulZero a = 0 * a == 0  

mulOne :: (Eq a, Num a) => a -> Bool
mulOne a = 1 * a == a  

mulComm :: (Eq a, Num a) => a -> a -> Bool
mulComm a b = a * b == b * a

mulAssoc :: (Eq a, Num a) => a -> a -> a -> Bool
mulAssoc a b c = a * (b * c) == (a * b) * c

mulDistr :: (Eq a, Num a) => a -> a -> a -> Bool
mulDistr a b c = a * (b + c) == a*b + a*c

mulSign :: (Eq a, Num a) => a -> a -> Bool
mulSign a b = and [ a * (-b) == - (a * b)
                  , (- a) * (-b) == a * b ]

divTest :: (Eq a, Fractional a) => a -> a -> Bool
divTest a b =
  if b /= 0 
  then let r = a / b in  b * r == a
  else True

divHomo :: (Eq a, Fractional a)
        => a -> Integer -> Integer -> Bool
divHomo w a b =
  if b /=0 then x / y == z else True
  where [x,y,z,_] = [ fromInteger a
                    , fromInteger b
                    , fromRational (a % b)
                    , w]
             
instance ModBase m => Arbitrary (Base m) where
  arbitrary = fromInteger <$> arbitrary

testBase = do
  quickCheck (intHomo (0 :: Base 13))
  quickCheck (addHomo (0 :: Base 13))
  quickCheck (mulHomo (0 :: Base 13))
  quickCheck (addComm @(Base 13))
  quickCheck (addAssoc @(Base 13))
  quickCheck (negInvol @(Base 13))
  quickCheck (negInvers @(Base 13))
  quickCheck (mulZero @(Base 13))
  quickCheck (mulOne @(Base 13))
  quickCheck (mulComm @(Base 13))
  quickCheck (mulAssoc @(Base 13))
  quickCheck (mulDistr @(Base 13))
  quickCheck (mulSign @(Base 13))

instance ModBase m => Arbitrary (Qp m) where
  arbitrary = fromRational <$> arbitrary

testQp = do  
  quickCheck (addHomo (0 :: Qp 13))
  quickCheck (mulHomo (0 :: Qp 13))
  quickCheck (divHomo (0 :: Qp 13))
  quickCheck (addComm @(Qp 13))
  quickCheck (addAssoc @(Qp 13))
  quickCheck (negInvol @(Qp 13))
  quickCheck (negInvers @(Qp 13))
  quickCheck (mulZero @(Qp 13))
  quickCheck (mulOne @(Qp 13))
  quickCheck (mulComm @(Qp 13))
  quickCheck (mulAssoc @(Qp 13))
  quickCheck (mulDistr @(Qp 13))
  quickCheck (mulSign @(Qp 13))
  quickCheck (divTest @(Qp 13))

