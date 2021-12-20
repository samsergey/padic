{-# LANGUAGE DataKinds #-}
{-# LANGUAGE DerivingVia #-}
{-# LANGUAGE KindSignatures #-}
import GHC.TypeLits hiding (Mod)
import GHC.Natural
import InfList (InfList(..), (+++))
import qualified InfList as I
import Data.List
import Data.Mod

newtype Digit (m :: Nat) = Digit Natural
  deriving (Eq, Ord, Show) via Natural

toDigit :: KnownNat m => Integer -> Digit m
toDigit n =
  let res = Digit $ fromInteger $ n `mod` natVal res
  in res

base :: (KnownNat m, Integral i) => f m -> i
base = fromInteger . natVal

instance KnownNat m => Num (Digit m) where
  fromInteger = toDigit
  m@(Digit a) + Digit b = Digit $ (a + b) `mod` base m
  m@(Digit a) * Digit b = Digit $ (a * b) `mod` base m
  negate m@(Digit a) = Digit (base m - a `mod` base m)
  abs = id
  signum 0 = 0
  signum _ = 1

instance KnownNat m => Bounded (Digit m) where
  minBound = 0
  maxBound = let res = Digit (base res - 1) in res

instance KnownNat m => Enum (Digit m) where
  toEnum = fromInteger . fromIntegral
  fromEnum = fromIntegral . toInteger
  enumFrom a = [a..maxBound]

instance KnownNat m => Real (Digit m) where
  toRational = toRational . toInteger

instance KnownNat m => Integral (Digit m) where
  toInteger (Digit d) = toInteger d

  quotRem a b = (fromIntegral q, fromIntegral r)
     where
       (q, r) = fromIntegral a `quotRem` fromIntegral b


------------------------------------------------------------

newtype Base (m :: Nat) = Base (InfList (Digit m))

digits :: (KnownNat m, Integral i) => Base m -> InfList i
digits (Base ds) = fromIntegral <$> ds 

fromDigits :: (KnownNat m, Integral i) => InfList i -> Base m
fromDigits ds = Base $ fromIntegral <$> ds

toBase :: (Integral b, KnownNat m) => b -> Base m
toBase n = res
  where
    res = fromDigits $ I.unfoldr go n
    go n = let (q, r) = quotRem n (base res) in (r, q)

instance KnownNat m => Show (Base m) where
  show = process . reverse . I.take 20 . digits
    where
      process lst = case dropWhile (== 0) lst of
        [] -> "0"
        l -> foldMap showDigit l

showDigit n = pure $ (['0'..'9']++['a'..'z']) !! fromIntegral n


instance KnownNat p => Num (Base p) where
  fromInteger = toBase
  Base a + Base b = Base $ addBase a b
  Base a * Base b = Base $ mulBase a b 
  negate (Base a) = Base (I.map (\x -> - x - 1) a) + 1
  signum _ = 1
  abs = id

-- выделяет из числа перенос на следующий разряд
carry n =
  let d = fromIntegral n in (n `div` base d, d)

-- поразрядное сложение с переносом
addBase a b = I.mapAccumL step 0 $ I.zip a b
  where
    step r (Digit x, Digit y) = carry (x + y + r)

-- поразрядное умножение с переносом
mulBase a b = go b
  where
    go (b ::: bs) = addBase (go bs) `apTail` scaleBase b a
    apTail f (h ::: t) = h ::: f t

scaleBase :: KnownNat m
        => Digit m -> InfList (Digit m)
        -> InfList (Digit m)
scaleBase (Digit s) a =
  I.mapAccumL (\r (Digit x) -> carry (s * x + r)) 0 a



instance Eq (Base m) where
  Base a == Base b = I.take 20 a == I.take 20 b

invDigit :: KnownNat m => Digit m -> Digit m
invDigit a = case find (\x -> a * x == 1) [1..] of
  Nothing -> error $
    "undivisible number modulo " ++ show (base a)
  Just r -> r
  
divBase :: KnownNat m => Base m -> Base m -> Base m
divBase (Base a) (Base b) = fromDigits $ go a
  where
    r = invDigit (I.head b)
    go xs =
      let m = I.head xs * r
          s = scaleBase m b
      in m ::: go (I.tail $ addBase xs (neg s))

    neg (h:::t) = - h ::: I.map (\x -> - x - 1) t

-------------------------------------------------------------

fixedPoint f = limit . take 100 . iterate f

newton a x = (x + a `divBase` x) `divBase` 2

limit (x:y:z) | x == y = Just x
              | otherwise = limit (y:z)
limit _ = Nothing


