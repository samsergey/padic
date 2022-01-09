{-# LANGUAGE LambdaCase #-}
{-# OPTIONS_HADDOCK hide, prune, ignore-exports #-}

{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE MagicHash #-}
{-# LANGUAGE NoStarIsType #-}

module Math.NumberTheory.Padic.Classes  where

import Data.Ratio
import Data.List (unfoldr, genericLength, tails, inits,find)
import Data.Maybe (isJust, maybeToList)
import Data.Mod  
import Data.Word  
import GHC.TypeLits hiding (Mod)
import Data.Constraint (Constraint)
import GHC.Integer (smallInteger)
import GHC.Integer.Logarithms ( integerLogBase# )

------------------------------------------------------------
-- | Constraint for non-zero natural number which can be a radix.
type family ValidRadix (m :: Nat) :: Constraint where
  ValidRadix 0 = TypeError ('Text "Zero radix!")
  ValidRadix 1 = TypeError ('Text "Radix should be more then 1!")
  ValidRadix m = ()

-- | Constraint for valid radix of a number
type KnownRadix m = ( ValidRadix m , KnownNat m )
  
-- | Radix of the internal representation of integer p-adic number.
type family LiftedRadix p prec where
  LiftedRadix p prec = p ^ (2*prec + 1)

-- | Constraint for known valid radix of p-adic number as well as it's  lifted radix.
type family Radix p prec :: Constraint where
  Radix p prec =
    ( KnownNat prec
    , KnownRadix p
    , KnownRadix (LiftedRadix p prec)
    )

type family SufficientPrecision t p :: Nat where
  SufficientPrecision Word32 2 = 31
  SufficientPrecision Word32 3 = 20
  SufficientPrecision Word32 5 = 13
  SufficientPrecision Word32 6 = 12
  SufficientPrecision Word32 7 = 11
  SufficientPrecision Word32 10 = 9
  SufficientPrecision Int 2 = 63
  SufficientPrecision Int 3 = 40
  SufficientPrecision Int 5 = 27
  SufficientPrecision Int 6 = 24
  SufficientPrecision Int 7 = 22
  SufficientPrecision Int 10 = 19
  SufficientPrecision Word p = 1 + SufficientPrecision Int p
  SufficientPrecision (Ratio t) p = SufficientPrecision t p
  SufficientPrecision t p = Div (SufficientPrecision t 2) (Log2 p)

-- | Type for p-adic number representing numeric type @num@ with radix @p@.
type family Padic num (p :: Nat) (prec :: Nat)

data Fixed
data Free

------------------------------------------------------------
-- | Typeclass for p-adic numbers objects
class Num n => PadicNum n where
  -- | A type for p-adic unit.
  type Unit n
  -- | A type for digits of p-adic expansion.
  -- Associated type allows to assure that digits will agree with the radix @p@ of the number.
  type Digit n
  -- | Internal representation of p-adic number.
  type Lifted n
  -- | Returns the precision of a number.
  --
  -- Examples:
  --
  -- >>> precision (123 :: Z 2)
  -- 20
  -- >>> precision (123 :: Z' 2 40)
  -- 40
  precision :: Integral i => n -> i
  -- | Returns the radix of a number
  --
  -- Examples:
  --
  -- >>> radix (5 :: Z 13)
  -- 13
  -- >>> radix (-5 :: Q' 3 40)
  -- 3
  radix :: Integral i => n -> i
 
  -- | Constructor for a digital object from it's digits
  fromDigits :: [Digit n] -> n
  -- | Returns digits of a digital object
  --
  -- Examples:
  --
  -- >>> take 5 $ digits (123 :: Z 10)
  -- [(3 `modulo` 10),(2 `modulo` 10),(1 `modulo` 10),(0 `modulo` 10),(0 `modulo` 10)]
  -- >>> take 5 $ digits (-123 :: Z 2)
  -- [(1 `modulo` 2),(0 `modulo` 2),(1 `modulo` 2),(0 `modulo` 2),(0 `modulo` 2)]
  -- >>> take 5 $ digits (1/200 :: Q 10)
  -- [(1 `modulo` 2),(0 `modulo` 2),(1 `modulo` 2),(0 `modulo` 2),(0 `modulo` 2)]
  digits :: n -> [Digit n]
  -- | Returns lifted digits
  --
  -- Examples:
  --
  -- >>> take 3 $ lifted (123 :: Z 10)
  -- [(123 `modulo` 10000000000000000000),(0 `modulo` 10000000000000000000),(0 `modulo` 10000000000000000000)]
  -- >>> take 3 $ lifted (-123 :: Z 2)
  -- [(9223372036854775685 `modulo` 9223372036854775808),(9223372036854775807 `modulo` 9223372036854775808),(9223372036854775807 `modulo` 9223372036854775808)]
  lifted :: n -> Lifted n

  -- | Creates digital object from it's lifted digits.
  mkUnit :: Lifted n -> n

  -- | Creates p-adic number from given unit and valuation.
  --
  -- prop> fromUnit (u, v) = u * p^v
  fromUnit :: (Unit n, Int) -> n
  -- | Splits p-adic number into unit and valuation.
  --
  -- prop> splitUnit (u * p^v) = (u, v)
  splitUnit :: n -> (Unit n, Int)
 
  -- | Returns @True@ for a p-adic number which is multiplicatively invertible.
  isInvertible :: n -> Bool

  -- | Partial multiplicative inverse of p-adic number (defined both for integer or rational p-adics).
  inverse :: n -> Maybe n
  

-- | The least significant digit of a p-adic number.
{-# INLINE firstDigit #-}
firstDigit n = head (digits n)

{- | Returns the unit of a number

Examples:

>>> unit (120 :: Z 10)
12
>>> unit (75 :: Z 5)
3 -}
unit :: PadicNum n => n -> Unit n
{-# INLINE unit #-}
unit = fst . splitUnit

{- | Returns a valuation  of a number

Examples:

>>> valuation (120 :: Z 10)
1
>>> valuation (75 :: Z 5)
2

Valuation of zero is equal to working precision

>>> valuation (0 :: Q 2)
20
>>> valuation (0 :: Q' 2 150)
150 -}
valuation :: PadicNum n => n -> Int
{-# INLINE valuation #-}
valuation = snd . splitUnit

-- | returns a rational norm of a number
--
-- Examples:
--
-- >>> norm (120 :: Z 10)
-- 0.1
-- >>> norm (75 :: Z 5)
-- 4.0e-2
norm :: (Integral i, PadicNum n) => n -> Ratio i
{-# INLINE norm #-}
norm n = (radix n % 1) ^^ (-valuation n)

{- | Adjusts unit and valuation of p-adic number, by removing trailing zeros from the right-side of the unit.

Examples:

>>> λ> x = 2313 + 1387 :: Q 10
>>> x
3700.0
>>> splitUnit x
(3700,0)
>>> splitUnit (normalize x)
(37,2) -}
normalize :: (PadicNum n) => n -> n
normalize x = fromUnit $ splitUnit x


-- | Returns @True@ for a p-adic number which is equal to zero (within it's precision).
isZero :: PadicNum n => n -> Bool
{-# INLINE isZero #-}
isZero n = valuation n >= precision n

instance KnownRadix p => PadicNum (Mod p) where
  type Unit (Mod p) = Mod p
  type Lifted (Mod p) = Integer
  type Digit (Mod p) = Mod p
  radix = fromIntegral . natVal
  precision _ = fromIntegral (maxBound :: Int)
  digits = pure
  fromDigits = head
  lifted = fromIntegral . unMod
  mkUnit = fromInteger
  inverse = invertMod
  isInvertible = isJust . invertMod 
  fromUnit (u, 0) = u
  fromUnit _ = 0
  splitUnit u = (u, 0)

-- | Unfolds a number to a list of digits (integers modulo @p@).  
toRadix :: KnownRadix p => Integer -> [Mod p]
toRadix 0 = [0]
toRadix n = res
  where
    res = unfoldr go n
    p = fromIntegral $ natVal $ head $ 0 : res
    go 0 = Nothing
    go x =
      let (q, r) = quotRem x p
       in Just (fromIntegral r, q)
  
-- | Folds a list of digits (integers modulo @p@) to a number.
fromRadix :: KnownRadix p => [Mod p] -> Integer
fromRadix ds = foldr (\x r -> lifted x + r * p) 0 ds
  where
    p = fromIntegral $ natVal $ head $ 0 : ds

extEuclid :: Integral i => (Integer, Integer) -> Ratio i
extEuclid (n, m) = go (m, 0) (n, 1)
  where
    go (v1, v2) (w1, w2)
      | 2*w1*w1 > abs m =
        let q = v1 `div` w1
         in go (w1, w2) (v1 - q * w1, v2 - q * w2)
      | otherwise = fromRational (w1 % w2)

ilog :: (Integral a, Integral b) => a -> a -> b
ilog a b =
  fromInteger $ smallInteger (integerLogBase# (fromIntegral a) (fromIntegral b))

-- | Extracts p-adic unit from integer number. For radix \(p\) and integer \(n\) returns
-- pair \((u, k)\) such that \(n = u \cdot p^k\).
--
-- Examples:
-- 
-- >>> getUnitQ 3 (75/157)
-- (1,25 % 157)
-- >>> getUnitQ 5 (75/157)
-- (2,3 % 157)
-- >>> getUnitQ 157 (75/157)
-- (-1,75 % 1)
getUnitZ :: Integer -> Integer -> (Integer, Int)
getUnitZ _ 0 = (0, 0)
getUnitZ p x = (b, length v)
  where
    (v, b:_) = span (\n -> n `mod` p == 0) $ iterate (`div` p) x

-- | Extracts p-adic unit from a rational number. For radix \(p\) and rational number \(x\) returns
-- pair \((r/s, k)\) such that \(x = r/s \cdot p^k\).
--
-- Examples:
--
-- >>> getUnitQ 3 (75/157)
-- (1,25 % 157)
-- >>> getUnitQ 5 (75/157)
-- (2,3 % 157)
-- >>> getUnitQ 157 (75/157)
-- (-1,75 % 1)
getUnitQ :: Integral p => p -> Ratio p -> (Ratio p, Int)
getUnitQ _ 0 = (0, 0)
getUnitQ p x = (c, genericLength v2 - genericLength v1)
  where
    (v1, b:_) =
      span (\n -> denominator n `mod` p == 0) $ iterate (* fromIntegral p) x
    (v2, c:_) =
      span (\n -> numerator n `mod` p == 0) $ iterate (/ fromIntegral p) b

liftedRadix :: (PadicNum n, Integral a) => n -> a
{-# INLINE liftedRadix #-}
liftedRadix n = radix n ^ (2*precision n + 1)

{- | For given radix \(p\) and natural number \(m\) returns precision sufficient for rational
reconstruction of fractions with numerator and denominator not exceeding \(m\).

Examples:

>>> sufficientPrecision 2 (maxBound :: Int)
64
>>> sufficientPrecision 3 (maxBound :: Int)
41
>>> sufficientPrecision 10 (maxBound :: Int)
20
-}
sufficientPrecision :: (Integral a) => Integer -> a -> Integer
sufficientPrecision p m = ilog p (2 * fromIntegral m) + 1

  
{- | Returns p-adic solution of the equation \(f(x) = 0\) by Hensel lifting solutions of \(f(x) = 0\ \mathrm{mod}\ p\).

Examples:

>>> henselLifting (\x -> x*x - 2) (\x -> 2*x) :: [Z 7]
[…64112011266421216213,…02554655400245450454]
>>> henselLifting (\x -> x*x - x) (\x -> 2*x-1) :: [Q 10]
[0,1,…92256259918212890625,…07743740081787109376]
-}
henselLifting ::
     (Eq n, PadicNum n, KnownRadix p, Digit n ~ Mod p)
  => (n -> n) -- ^ Function to be vanished.
  -> (n -> n) -- ^ Derivative of the function.
  -> [n] -- ^ The result.
henselLifting f f' = res
  where
    pr = precision (head res)
    res = findSolutionMod f >>= iterateM pr step
    step x = do
      invf' <- maybeToList (inverse (f' x))
      return (x - f x * invf')

{- | Returns solution of the equation \(f(x) = 0\ \mathrm{mod}\ p\) in p-adics.

>>> findSolutionMod (\x -> x*x - 2) :: [Z 7]
[3,4]
>>> findSolutionMod (\x -> x*x - x) :: [Q 10]
[0.0,1.0,5.0,6.0]
-}
findSolutionMod :: (PadicNum n, KnownRadix p, Digit n ~ Mod p)
                => (n -> n) -> [n]
findSolutionMod f = [ fromMod d | d <- [0..], fm d == 0 ]
  where
    fm = firstDigit . f . fromMod
    fromMod x = fromDigits [x]

iterateM :: (Eq a, Monad m) => Int -> (a -> m a) -> a -> m a
iterateM n f = go n
  where
    go 0 x = pure x
    go i x = do
      y <- f x
      if x == y then pure x else go (i - 1) y
   
------------------------------------------------------------

-- | For a given list extracts prefix and a cycle, limiting length of prefix and cycle by @len@.
-- Uses the modified tortiose and hare method.
findCycle :: Eq a => Int -> [a] -> Maybe ([a], [a])
findCycle len lst =
  find test [ rollback (a, c)
            | (a, cs) <- tortoiseHare len lst
            , c <- take 1 [ c | c <- tail (inits cs)
                              , and $ zipWith (==) cs (cycle c) ] ]
  where
    rollback (as, bs) = go (reverse as, reverse bs)
      where
        go =
          \case
            ([], ys) -> ([], reverse ys)
            (x:xs, y:ys)
              | x == y -> go (xs, ys ++ [x])
            (xs, ys) -> (reverse xs, reverse ys)
    test (_, []) = False
    test (pref, c) = and $ zipWith (==) (take len lst) (pref ++ cycle c)

tortoiseHare :: Eq a => Int -> [a] -> [([a], [a])]
tortoiseHare l x =
  map (fmap fst) $
  filter (\(_, (a, b)) -> concat (replicate 3 a) == b) $
  zip (inits x) $
  zipWith splitAt [1 .. l] $ zipWith take [4, 8 ..] $ tails x
