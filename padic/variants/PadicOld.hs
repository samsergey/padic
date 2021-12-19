{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE DerivingVia #-}
{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE DataKinds #-}

module Padic where

import GHC.TypeLits hiding (Mod)
import Data.Mod
import Data.Constraint
import InfList (InfList(..), (+++))
import qualified InfList as Inf
import Data.List
import Data.Ratio

------------------------------------------------------------

type family NonZeroNat (m :: Nat) :: Constraint where
  NonZeroNat 0 = TypeError ('Text "Zero base!")
  NonZeroNat m = ()

type Base m = (NonZeroNat m, KnownNat m)

instance Base m => Digital (Mod m) where
  base = fromIntegral . natVal
  digits x = fromIntegral (unMod x) ::: Inf.repeat undefined
  fromDigits = fromIntegral . Inf.head

------------------------------------------------------------
  
class Digital n where
  base       :: Integral i => n -> i
  digits     :: Integral d => n -> InfList d
  fromDigits :: Integral d => InfList d -> n

firstDigit :: (Digital n, Integral a) => n -> a
firstDigit = Inf.head . digits

class Fixed n where
  precision :: Integral i => n -> i

class Padic n where
  unit :: n -> n
  valuation :: n -> Int
  
------------------------------------------------------------

newtype Z' (p :: Nat) (prec :: Nat) = Z' (Z p)
  deriving (Num, Digital, Padic) via (Z p)

instance KnownNat prec => Fixed (Z' p prec) where
  precision = fromIntegral . natVal

instance (KnownNat prec, Base p) => Eq (Z' p prec) where
  a == b = Inf.take pr (digits a) == Inf.take pr (digits b)
    where
      pr = precision a

instance (KnownNat prec, Base p) => Show (Z' p prec) where
  show n = process . reverse . Inf.take pr $ digits n
    where
      pr = precision n
      process lst = case dropWhile (== 0) lst of
        [] -> "0"
        l -> ell l ++ intercalate sep (show  <$> l)
      ell l = if length l < pr then "" else "…"
      sep = if base n < 11 then "" else " "

instance (KnownNat prec, Base p) => Enum (Z' p prec) where
  toEnum = fromInteger . fromIntegral
  fromEnum = fromIntegral . toInteger
  enumFrom a = [a..base a - 1]

instance (KnownNat prec, Base p) => Ord (Z' p prec) where
  compare = error "ordering is not defined for Z"

instance (KnownNat prec, Base p) => Real (Z' p prec) where
  toRational = toRational . fromIntegral

instance (KnownNat prec, Base p) => Integral (Z' p prec) where
  toInteger n =
    case integerDigits n of
      Nothing -> error "number seems not to be integer"
      Just (Right xs) -> foldl (\r x -> x + r*b) 0 xs
      Just (Left xs) -> foldl (\r x -> x + 1 + (r - 1)*b) 0 xs - 1
    where
      b = base n

  div (Z' a) (Z' b) = case divZ a b of
    Nothing -> error $ show b ++ " is not invertible!"
    Just r -> Z' r
    
  quotRem = error "quotRem is not defined fo p-adics"
  divMod  = error "divMod is not defined fo p-adics"
  mod     = error "divMod is not defined fo p-adics"

-- выделение целой части числа (до известной точности)
integerDigits n = process [] windows
  where
    b = base n
    prec = precision n
    -- последовательность окон ширины prec, уходящая вправо
    windows = Inf.take (fromIntegral prec + 1) $
              Inf.map (Inf.take (1 + fromIntegral prec)) $
              Inf.tails (digits n)
    -- поиск хвоста из нулей или "девяток", целиком заполняющих окно
    process _ [] = Nothing
    process r ((x:xs):ws) = case sum xs of
      s | s == 0            -> Just $ Right (x:r)
        | s == (b - 1)*prec -> Just $ Left (x:r)
        | otherwise         -> process (x:r) ws

------------------------------------------------------------

newtype Z (p :: Nat) = Z (InfList (Mod p))
  deriving ( Eq, Show, Enum, Ord
           , Real, Integral, Fixed) via (Z' p 20)

instance Padic (Z p) where
  unit = id
  valuation = const 0

instance Base p => Digital (Z p) where
  digits (Z ds) = fromIntegral . unMod <$> ds 
  fromDigits ds = Z $ fromIntegral <$> ds
  base = fromIntegral . natVal

instance Base p => Num (Z p) where
  fromInteger = toZ
  Z a + Z b = Z $ addZ a b
  Z a * Z b = Z $ mulZ a b 
  negate (Z a) = Z $ negZ a
  signum _ = 1
  abs = id

-- превращает целое число в p-адическое
toZ :: (Base p, Integral i) => i -> Z p
toZ n | n < 0 = - toZ (- n)
      | otherwise = res
  where
    res = fromDigits $ Inf.unfoldr go n
    go n = let (q, r) = quotRem n (base res) in (r, q)

-- выделяет из натурального числа перенос на следующий разряд
carry n =
  let d = fromIntegral n in (n `div` base d, d)

-- поразрядное сложение с переносом
addZ a b = Inf.mapAccumL step 0 $ Inf.zip a b
  where
    step r (x, y) = carry (unMod x + unMod y + r)

-- смена знака на противоположный
negZ (0 ::: t) = 0 ::: negZ t
negZ (h ::: t) = - h ::: Inf.map (\x -> - x - 1) t
    
-- поразрядное умножение с переносом
mulZ a b = go b
  where
    go (b ::: bs) = addZ (go bs) `apTail` scaleZ b a
    apTail f (h ::: t) = h ::: f t

-- поразрядное умножение на цифру с переносом
scaleZ :: Base p => Mod p -> InfList (Mod p) -> InfList (Mod p)
scaleZ s a =
  Inf.mapAccumL (\r x -> carry (unMod s * unMod x + r)) 0 a

-- поразрядное деление двух чисел "уголком"
divZ :: Base p => Z p -> Z p -> Maybe (Z p)
divZ (Z a) d@(Z b) =
  const (Z $ go a) <$> invertMod (Inf.head b)
  where
    r = recip (Inf.head b)
    go (0 ::: xs) = 0 ::: go xs
    go xs =
      let m = Inf.head xs * r
          mulAndSub = addZ xs . negZ . scaleZ m 
      in m ::: go (Inf.tail $ mulAndSub b)

------------------------------------------------------------

cycleForm :: (KnownNat prec, Base p) => Z' p prec -> String
cycleForm n =
  case findCycle len (Inf.toList (digits n)) of
    Just (pref, cyc) -> let
      sp = intercalate (sep n) $ show <$> reverse pref
      sc = intercalate (sep n) $ show <$> reverse cyc
      in "(" ++ sc ++ ")" ++ sp
    Nothing -> show n
  where
    len = fromIntegral $ natVal n
    sep (Z' z) = if base z < 11 then "" else " "

findCycle len lst =
  case turlteHare rest of
    [(a, c)] -> Just $ rollback (pref ++ a, c)
    [] -> Nothing
  where
    (pref, rest) = splitAt 20 lst
    
    turlteHare lst =
      map (fmap fst) . take 1 $ 
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

newtype Q' (p :: Nat) (prec :: Nat) = Q' (Q p)
  deriving (Digital, Padic) via (Q p)

instance KnownNat prec => Fixed (Q' p prec) where
  precision = fromIntegral . natVal

normalize :: (KnownNat prec, Base p) => Q' p prec -> Q' p prec
normalize (Q' Zero) = 0
normalize n = Q' $ go 0 (digits n)
  where
    go i _ | i > precision n = 0
    go i (0 ::: u) = go (i+1) u
    go i u = Q (valuation n + i) (fromDigits u)

instance (KnownNat prec, Base p) => Num (Q' p prec) where
  fromInteger 0 = Q' Zero
  fromInteger n = normalize $ Q' $ Q 0 (fromInteger n)

instance (KnownNat prec, Base p) => Show (Q' p prec) where
  show (Q' Zero) = "0.0"
  show n = ell ++ zer si ++ "." ++ zer sf
    where
      p = precision n
      k = valuation n    
      ds = Inf.take (precision n - k) (digits n)
      (f, i) = splitAt (-k) ds
      sf = intercalate sep $ map show $ reverse f
      li = dropWhile (== 0) $ reverse i ++ replicate k 0
      si = intercalate sep $ map show li
      zer s = if null s then "0" else s   
      sep = if base n < 11 then "" else " "   
      ell = if length li < p then "" else "…"
      

data Q (p :: Nat) = Zero | Q Int (Z p)
  deriving (Show, Fixed, Num) via (Q' p 20)

instance Base p => Padic (Q p) where
  unit Zero = Zero
  unit (Q _ u) = Q 0 u

  valuation Zero = maxBound
  valuation (Q v _) = v

instance Base p => Digital (Q p) where
  digits Zero = Inf.repeat 0
  digits (Q _ u) = digits u
  
  fromDigits ds = Q 0 (fromDigits ds)

  base = fromIntegral . natVal


------------------------------------------------------------

-- минимальная фиксированная точка функции
fixedPoint maxSteps f = limit . take maxSteps . iterate f

-- предел последовательности
limit (x:y:z) | x == y = Just x
              | otherwise = limit (y:z)
limit _ = Nothing

newton f df x = x - f x `div` df x

-- корень в кольце Z/pZ
sqrtMod :: Base p => Mod p -> Maybe (Mod p)
sqrtMod x = find (\d -> d*d == x) [1..]

-- корень в кольце Z p
sqrtZ :: Base p => Z p -> Maybe (Z p)
sqrtZ n@(Z (d ::: _)) = do
  x0 <- fromIntegral . unMod <$> sqrtMod d
  fixedPoint 100 (\x -> (x + n `div` x) `div` 2) x0

