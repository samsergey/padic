{-# language TypeApplications #-}
{-# language DataKinds #-}
{-# language TypeFamilies #-}
{-# language TypeOperators #-}
{-# language FlexibleContexts #-}

import Criterion.Main
import Math.NumberTheory.Padic
import Data.Maybe
import Data.List (transpose)

addBench :: (Show n, Num n) => n -> Int -> String
addBench w n = show (w + sum (take n (fib 0 1)))

mulBench :: (Show n, Num n) => n -> Integer -> String
mulBench w n = let M ((x:_):_) = fibM n in show (w + x)

divBench :: (Show a, Num a) => a -> a -> Int -> String
divBench r w n = show (product $ take n $ logistic r w)

fib a b = a : fib b (a + b)
 
fibM 0 = I
fibM n = M [[1,1],[1,0]] <> fibM (n-1)

logistic r = iterate (\x -> r*x*(1-x))
  

divMaybe a b | isInvertible b = Just (a `div` b)
             | otherwise = Nothing

fracMaybe a b | isInvertible b = Just (a / b)
              | otherwise = Nothing

data M a = I | M [[a]]

dot a b = sum $ zipWith (*) a b                 

instance Num a => Semigroup (M a) where
  I <> x = x
  x <> I = x
  M a <> M b = M $ [ [ dot x y | y <- transpose b ] | x <- a ]

instance Num a => Monoid (M a) where
    mempty = I
    
suite :: [Benchmark]
suite =
  [ bgroup
      "add"
      [ bench "Integer" $ whnf (addBench (0 :: Integer)) 200
      , bench "Z 2" $ whnf (addBench (0 :: Z' 2 20)) 200
      , bench "Z 3" $ whnf (addBench (0 :: Z' 3 20)) 200 
      , bench "Z 13" $ whnf (addBench (0 :: Z' 13 20)) 200
      , bench "Z 251" $ whnf (addBench (0 :: Z' 251 20)) 200
      , bench "Q 2" $ whnf (addBench (0 :: Q' 2 20)) 200
      , bench "Q 3" $ whnf (addBench (0 :: Q' 3 20)) 200
      , bench "Q 13" $ whnf (addBench (0 :: Q' 13 20)) 200
      , bench "Q 251" $ whnf (addBench (0 :: Q' 251 20)) 200]
  , bgroup
      "mul"
      [ bench "Integer" $ whnf (mulBench (0 :: Integer)) 200
      , bench "Z 2" $ whnf (mulBench (0 :: Z' 2 20)) 200
      , bench "Z 3" $ whnf (mulBench (0 :: Z' 3 20)) 200 
      , bench "Z 13" $ whnf (mulBench (0 :: Z' 13 20)) 200
      , bench "Z 251" $ whnf (mulBench (0 :: Z' 251 20)) 200
      , bench "Q 2" $ whnf (mulBench (0 :: Q' 2 20)) 200
      , bench "Q 3" $ whnf (mulBench (0 :: Q' 3 20)) 200
      , bench "Q 13" $ whnf (mulBench (0 :: Q' 13 20)) 200
      , bench "Q 251" $ whnf (mulBench (0 :: Q' 251 20)) 200]
  , bgroup
      "div"
      [ bench "Double" $ whnf (divBench (13 / 5) (4 / 3 :: Double)) 200
      , bench "Z 2" $ whnf (divBench (13 `div` 5) (4 `div` 3 :: Z 2)) 200
      , bench "Z 3" $ whnf (divBench (13 `div` 4) (7 `div` 5 :: Z 3)) 200
      , bench "Z 13" $ whnf (divBench (13 `div` 4) (4 `div` 3 :: Z 13)) 200
      , bench "Z 251" $ whnf (divBench (13 `div` 4) (4 `div` 3 :: Z 251)) 200
      , bench "Q 2" $ whnf (divBench (13 / 4) (4 / 3 :: Q 2)) 200
      , bench "Q 3" $ whnf (divBench (13 / 5) (7 / 5 :: Q 3)) 200
      , bench "Q 13" $ whnf (divBench (13 / 4) (4 / 3 :: Q 13)) 200
      , bench "Q 251" $ whnf (divBench (13 / 4) (4 / 3 :: Q 251)) 200
      ]
  ]

main :: IO ()
main = defaultMain suite
