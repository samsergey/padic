module Padic where

import Data.Ratio
import Data.Maybe (fromMaybe)
import Data.List (find)
import Control.Monad (guard)

data Padic = Padic { pBase :: Int
                   , pUnit :: [Int]
                   , pOrder :: Int }

-- Smart constructor, adjusts trailing zeros with the order.
mkPadic :: (Integral p, Integral i) => p -> [i] -> Int -> Padic
mkPadic p u k = go 0 (fromIntegral <$> u)
  where
    go 17 _ = pZero (fromIntegral p)
    go i (0:u) = go (i+1) u
    go i u = Padic (fromIntegral p) u (k-i)

-- Constructor for p-adic unit
mkUnit :: (Integral p, Integral i) => p -> [i] -> Padic
mkUnit p u = mkPadic p u 0

-- Constructor for zero value
pZero :: Int -> Padic
pZero p = mkUnit p []

-- Zero test (up to 1/p^17)
isZero :: Padic -> Bool
isZero (Padic _ u _) = all (== 0) (take 17 u)

-- p-adic norm
pNorm :: Padic -> Ratio Int
pNorm (Padic p _ k) = fromIntegral p ^^ (-k)

-- p-adics are shown with 1/p^17 precision
instance Show Padic where
  show (Padic p u k) =
    show p ++ "-adic: " ++
    (case si of {[] -> "0"; _ -> si})
    ++ "." ++
    (case f of {[] -> "0"; _ -> sf})
    where
      (f,i) = case compare k 0 of
        LT -> ([], replicate (-k) 0 ++ u)
        EQ -> ([], u)
        GT -> splitAt k (u ++ repeat 0)
      sf = foldMap showD $ reverse $ take 17 f
      si = foldMap showD $ dropWhile (== 0) $ reverse $ take 17 i
      el s = if length s > 16 then "…" else ""
      showD n = [(['0'..'9']++['a'..'z']) !! n]

--------------------------------------------------------------------------------
-- basic arythmetic

instance Eq Padic where
  a == b = isZero (a - b)

instance Num Padic where
  fromInteger _ = undefined

  Padic p a ka + Padic _ b kb = mkPadic p s k
    where
      k = ka `max` kb
      s = addMod p (replicate (k-ka) 0 ++ a) (replicate (k-kb) 0 ++ b)

  Padic p a ka * Padic _ b kb =  mkPadic p (mulMod p a b) (ka + kb)

  negate (Padic p u k) =
    case map (\x -> p - 1 - x) u of
      n:ns -> Padic p ((n+1):ns) k
      [] -> pZero p

  abs p = pAdic (pBase p) (pNorm p)

  signum = undefined

instance Fractional Padic where
  fromRational = undefined
  recip x@(Padic p u k)
    | isZero x = error "zero denominator!"
    | gcd p (sigDigit x) /= 1 = error $ show x ++ " is not invertible." 
    | otherwise = mkPadic p (go (pAdic p 1)) (-k)
    where
      Just r = recipMod p (sigDigit x)
      unit = mkUnit p u
      go y
        | isZero y = repeat 0
        | otherwise =
            let m = (sigDigit y * r) `mod` p
            in m : go (pShift (y - (pAdic p (m % 1) * unit)))
         
      sigDigit (Padic _ [] _) = 0
      sigDigit (Padic _ (u:_) _) = u

      pShift (Padic p u k) = mkPadic p u (k+1)

--------------------------------------------------------------------------------
-- conversion between rationals and p-adics

pAdic :: Int -> Ratio Int -> Padic
pAdic p 0 = pZero p
pAdic p x = mkPadic p (series n) k
  where
    (k, q) = getUnit p x
    (n, d) = (numerator q, denominator q)
    r = fromMaybe
          (error $ concat [show x, " can't be represented as "
                          , show p, "-adic."])
          (recipMod p d)
    series n
      | n == 0 = repeat 0
      | n `mod` p == 0 = 0 : series (n `div` p)
      | otherwise =
          let m = (n * r) `mod` p
          in m : series ((n - m * d) `div` p)

-- rational reconstruction
toRat :: Padic -> Ratio Int
toRat x@(Padic p s k) =
  (fromBase p (pUnit i) * (p^(- pOrder i))) % length d
  where
    (d, i:_) = break isInteger $ iterate (x +) $ pZero p
    fromBase p = foldr (\x r -> r*p + x) 0 . take 20

-- extracts p-adic unit from a rational number
getUnit :: Int -> Ratio Int -> (Int, Ratio Int)
getUnit p x = (length k1 - length k2, c) 
  where
    (k1,b:_) = span (\n -> denominator n `mod` p == 0) $
               iterate (* fromIntegral p) x
    (k2,c:_) = span (\n -> numerator n `mod` p == 0) $
               iterate (/ fromIntegral p) b

-- naive test for an integerness up to p^-17
isInteger :: Padic -> Bool
isInteger (Padic p s k) = case splitAt k s of
  ([],i) -> length (takeWhile (==0) $ reverse (take 20 i)) > 3
  _ -> False

add x = x : x + x : add (x+x+x)


--------------------------------------------------------------------------------
-- helper functions
    
-- Reciprocal of a number modulo p (extended Euclidean algorythm).
-- For non-prime p returns Nothing non-inverible element of the ring.
recipMod :: Integral i => i -> i -> Maybe i
recipMod p 1 = Just 1
recipMod p a | gcd p a == 1 = Just $ go 0 1 p a
             | otherwise = Nothing
  where
    go t _ _ 0 = t `mod` p
    go t nt r nr =
      let q = r `div` nr
      in go nt (t - q*nt) nr (r - q*nr)

-- Addition of two sequences modulo p
addMod p = go 0
  where
    go 0 [] ys = ys
    go 0 xs [] = xs
    go s [] ys = go 0 [s] ys
    go s xs [] = go 0 xs [s]
    go s (x:xs) (y:ys) =
      let (q, r) = (x + y + s) `divMod` p
      in r : go q xs ys

subMod p a b = addMod p a (scaleMod p (p-1) b)

-- Multiplication of sequence by a number modulo p
scaleMod p a = go 0
  where
    go s [] = [s]
    go s (b:bs) =
      let (q, r) = (a * b + s) `divMod` p
      in r : go q bs

-- Multiplication of two sequences modulo p
mulMod p as = go
  where
    go [] = []
    go (b:bs) =
      let c:cs = scaleMod p b as
      in c : addMod p (go bs) cs

longDivMod p a (b:bs) = go a
  where
    Just r = recipMod p b
    go [] = []
    go (x:xs) =
      let
        m = x*r `mod` p
        zs = subMod p xs (tail (scaleMod p m (b:bs)))
      in m : go zs 

eqMod :: Integral a => a -> a -> a -> Bool
eqMod p a b = a `mod` p == b `mod` p

lsolveMod :: Integral a => a -> a -> a -> [a]
lsolveMod p a b = case recipMod p a of
  Just r -> [(r * b) `mod` p]
  Nothing ->
    case gcd p (gcd a b) of
      1 -> []
      m -> [ (x + (p `div` m) * i) `mod` p
           | x <- lsolveMod (p `div` m) (a `div` m) (b `div` m)
           , i <- [0.. m - 1] ]


--pSqrt :: Integer -> Rational -> Maybe Padic
pSqrt p r = mkUnit p <$> res
  where
    (a, b) = (numerator r, denominator r)
    res = case p of
      2 -> do
        guard $ eqMod 8 a 1
        let go pk x =
              let q = ((b*x*x - a) `div` pk) `mod` 2
              in q : go (2*pk) (x + q * (pk `div` 2))
        return $ 1:0:go 8 1

      p -> do
        y <- find (\x -> eqMod p (b*x*x) a) [1..p-1]
        df <- recipMod p (2*b*y)
        let go pk x =
              let f = (b*x*x - a) `div` pk
                  d = (f * (p - df)) `mod` p
              in x `div` (pk `div` p) : go (p*pk) (x + d*pk)
        return $ go p y
    

------------------------------------------------------------


-- toBaseI :: Integer -> Integer -> [Integer]
-- toBaseI p = unfoldr go
--   where go n = case n `divMod` p of
--                  (0,0) -> Nothing
--                  (q, r) -> Just (r, q)

-- toBaseF :: Integer -> Ratio Int -> [Integer]
-- toBaseF p = unfoldr go
--   where go n = case properFraction (fromIntegral p*n) of
--                  (0, 0) -> Nothing
--                  (i, f) -> Just (i, f)


-- bezoutEq :: Integer -> Integer -> (Integer, Integer)
-- bezoutEq a b =
--   let r = fromContFrac $ init $ contFrac (a % b)
--       d = denominator r
--       n = numerator r
--       s = signum (d*a - n*b)
--   in (s*d, -s*n)

-- contFrac :: Ratio Int -> [Int]
-- contFrac = unfoldr go
--   where
--     go r = case properFraction r of
--       (0,0) -> Nothing
--       (i, 0) -> Just (i, 0)
--       (i, f) -> Just (i, recip f)

-- fromContFrac :: [Int] -> Ratio Int
-- fromContFrac = foldr1 (\x r -> recip r + x) . map fromIntegral

-- findCycle :: Int -> [Int] -> ([Int], Maybe [Int])
-- findCycle len lst =
--   case find cyclicChunk (zip (inits lst) turtleHare) of
--     Just (a,(b,_)) -> rollBack (reverse a) (reverse b)
--     Nothing -> (take len lst, Nothing)
--   where
--     cyclicChunk (i, (a,b)) = concat (replicate 3 a) == b

--     turtleHare = zipWith splitAt [1..len] $
--                  zipWith take [4,8..] (tails lst)

--     rollBack [] bs = ([], reduceCycle (reverse bs))
--     rollBack (a:as) (b:bs)
--       | a == b = rollBack as (bs ++ [b])
--       | otherwise = (reverse (a:as), reduceCycle (reverse (b:bs)))

--     reduceCycle [] = Just  []
--     reduceCycle c =
--       case splitAt (length c `div` 2) c of
--         (a, b) | a == b -> reduceCycle a
--                | all (== head c) c -> Just [head c] 
--                | otherwise -> Just c

-- fromBase b lst = foldr (\x r -> r*b + x) 0 lst

-- toRat' x = case findCycle 100 $ pUnit x of
--   (s, Nothing) -> Nothing
--   (s, Just c) -> let
--     l = length c
--     y = x * pAdic 3 (3^l) - x
--     (n, _) = findCycle 100 $ pUnit y
--     in Just $ fromBase (pBase x) n % (3^l - 1)
    
