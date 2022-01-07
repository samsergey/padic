{-# language TypeApplications #-}
{-# language DataKinds #-}
{-# language TypeFamilies #-}
{-# language TypeOperators #-}
{-# language FlexibleContexts #-}

import Criterion.Main
import qualified Math.NumberTheory.Padic.Fixed as F
import Math.NumberTheory.Padic
import Data.Maybe
import Data.Mod
import Data.List (transpose)

addBench :: (Show n, Num n) => n -> Int -> Int
addBench w n = length $ show (w + sum (take n (fib 0 1)))

mulBench :: (Show n, Num n) => n -> Integer -> Int
mulBench w n = let M ((x:_):_) = fibM n in length (show (w + x))

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

data M a = I | M ![[a]]

dot a b = sum $! zipWith (*) a b                 

instance Num a => Semigroup (M a) where
  I <> x = x
  x <> I = x
  M a <> M b = M $ [ [ dot x y | y <- transpose b ] | x <- a ]

instance Num a => Monoid (M a) where
    mempty = I

addN = 400
mulN = 400
divN = 100
    
suite :: [Benchmark]
suite =
  [ bgroup
      "add"
      [ bench "Integer" $ whnf (addBench (0 :: Integer)) addN
      , bench "Mod 2^20" $ whnf (addBench (0 :: Mod 2199023255552)) addN
      , bench "Z 2" $ whnf (addBench (0 :: Z' 2 20)) addN
      , bench "Z 13" $ whnf (addBench (0 :: Z' 13 20)) addN
      , bench "Z 251" $ whnf (addBench (0 :: Z' 251 20)) addN
      , bench "F.Z 2" $ whnf (addBench (0 :: F.Z' 2 20)) addN
      , bench "F.Z 2 100" $ whnf (addBench (0 :: F.Z' 2 1000)) addN
      , bench "F.Z 13" $ whnf (addBench (0 :: F.Z' 13 20)) addN
      , bench "F.Z 251" $ whnf (addBench (0 :: F.Z' 251 20)) addN
      , bench "Q 2" $ whnf (addBench (0 :: Q' 2 20)) addN
      , bench "Q 2 100" $ whnf (addBench (0 :: Q' 2 100)) addN
      , bench "Q 13" $ whnf (addBench (0 :: Q' 13 20)) addN
      , bench "Q 251" $ whnf (addBench (0 :: Q' 251 20)) addN
      , bench "F.Q 2" $ whnf (addBench (0 :: F.Q' 2 20)) addN
      , bench "F.Q 2 100" $ whnf (addBench (0 :: F.Q' 2 100)) addN
      , bench "F.Q 13" $ whnf (addBench (0 :: F.Q' 13 20)) addN
      , bench "F.Q 251" $ whnf (addBench (0 :: F.Q' 251 20)) addN
     ]
  , bgroup
      "mul"
      [ bench "Integer" $ whnf (mulBench (0 :: Integer)) mulN
      , bench "Mod 2^20" $ whnf (mulBench (0 :: Mod 2199023255552)) mulN
      , bench "Z 2" $ whnf (mulBench (0 :: Z' 2 20)) mulN
      , bench "Z 2 100" $ whnf (mulBench (0 :: Z' 2 100)) mulN
      , bench "Z 13" $ whnf (mulBench (0 :: Z' 13 20)) mulN
      , bench "Z 251" $ whnf (mulBench (0 :: Z' 251 20)) mulN
      , bench "F.Z 2" $ whnf (mulBench (0 :: F.Z' 2 20)) mulN
      , bench "F.Z 2 100" $ whnf (mulBench (0 :: F.Z' 2 100)) mulN
      , bench "F.Z 13" $ whnf (mulBench (0 :: F.Z' 13 20)) mulN
      , bench "F.Z 251" $ whnf (mulBench (0 :: F.Z' 251 20)) mulN
      , bench "Q 2" $ whnf (mulBench (0 :: Q' 2 20)) mulN
      , bench "Q 2 100" $ whnf (mulBench (0 :: Q' 2 100)) mulN
      , bench "Q 13" $ whnf (mulBench (0 :: Q' 13 20)) mulN
      , bench "Q 251" $ whnf (mulBench (0 :: Q' 251 20)) mulN
      , bench "F.Q 2" $ whnf (mulBench (0 :: F.Q' 2 20)) mulN
      , bench "F.Q 2 100" $ whnf (mulBench (0 :: F.Q' 2 100)) mulN
      , bench "F.Q 13" $ whnf (mulBench (0 :: F.Q' 13 20)) mulN
      , bench "F.Q 251" $ whnf (mulBench (0 :: F.Q' 251 20)) mulN
      ]
  , bgroup
      "div"
      [ bench "Double" $ whnf (divBench (13 / 5) (4 / 3 :: Double)) divN
      , bench "Z 2" $ whnf (divBench (13 `div` 5) (5 `div` 3 :: Z 2)) divN
      , bench "Z 17" $ whnf (divBench (13 `div` 4) (4 `div` 3 :: Z 17)) divN
      , bench "Z 251" $ whnf (divBench (13 `div` 4) (4 `div` 3 :: Z 251)) divN
      , bench "F.Z 2" $ whnf (divBench (13 `div` 5) (4 `div` 3 :: F.Z 2)) divN
      , bench "F.Z 13" $ whnf (divBench (13 `div` 4) (4 `div` 3 :: F.Z 13)) divN
      , bench "F.Z 251" $ whnf (divBench (13 `div` 4) (4 `div` 3 :: F.Z 251)) divN
      , bench "Q 2" $ whnf (divBench (13 / 4) (4 / 3 :: Q 2)) divN
      , bench "Q 13" $ whnf (divBench (13 / 4) (4 / 3 :: Q 13)) divN
      , bench "Q 251" $ whnf (divBench (13 / 4) (4 / 3 :: Q 251)) divN
      , bench "F.Q 2" $ whnf (divBench (13 / 4) (4 / 3 :: F.Q 2)) divN
      , bench "F.Q 13" $ whnf (divBench (13 / 4) (4 / 3 :: F.Q 13)) divN
      , bench "F.Q 251" $ whnf (divBench (13 / 4) (4 / 3 :: F.Q 251)) divN
      ]
  ]

main :: IO ()
main = defaultMain suite
