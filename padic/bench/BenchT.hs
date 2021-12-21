{-# language TypeApplications #-}
{-# language DataKinds #-}
import Criterion.Main
import PadicD (Base)
import qualified PadicD as D
import qualified PadicM as M
import qualified Padic as N
import Data.Maybe

addBench :: (Num (f p), Base p) => f p -> Int -> f p
addBench w n = w + sum (fromIntegral <$> [1..n])

mulBench :: (Num (f p), Base p) => f p -> Int -> f p
mulBench w n = w + product (fromIntegral <$> [1..n])

divBench :: (Num (f p), Base p) => (f p -> f p -> Maybe (f p)) -> f p -> Int -> f p
divBench d w n = w + sum s
  where
    s = catMaybes [ d a b | a <- fromIntegral <$> [1..n]
                          , b <- fromIntegral <$> [1..n] ]

suite :: [Benchmark]
suite =
  [ bgroup
      "add"
      [ bench "D 2" $ whnf (addBench (0 :: D.Z 2)) 4000
      , bench "D 13" $ whnf (addBench (0 :: D.Z 13)) 4000
      , bench "D 251" $ whnf (addBench (0 :: D.Z 251)) 4000
      , bench "M 2" $ whnf (addBench (0 :: M.Z 2)) 4000
      , bench "M 13" $ whnf (addBench (0 :: M.Z 13)) 4000
      , bench "M 251" $ whnf (addBench (0 :: M.Z 251)) 4000
      , bench "N 2" $ whnf (addBench (0 :: N.Z 2)) 4000
      , bench "N 13" $ whnf (addBench (0 :: N.Z 13)) 4000
      , bench "N 251" $ whnf (addBench (0 :: N.Z 251)) 4000]
  , bgroup
      "mul"
      [ bench "D 2" $ whnf (mulBench (0 :: D.Z 2)) 4000
      , bench "D 13" $ whnf (mulBench (0 :: D.Z 13)) 4000
      , bench "D 251" $ whnf (mulBench (0 :: D.Z 251)) 4000
      , bench "M 2" $ whnf (mulBench (0 :: M.Z 2)) 4000
      , bench "M 13" $ whnf (mulBench (0 :: M.Z 13)) 4000
      , bench "M 251" $ whnf (mulBench (0 :: M.Z 251)) 4000
      , bench "N 2" $ whnf (mulBench (0 :: N.Z 2)) 4000
      , bench "N 13" $ whnf (mulBench (0 :: N.Z 13)) 4000
      , bench "N 251" $ whnf (mulBench (0 :: N.Z 251)) 4000]
  ]

main :: IO ()
main = defaultMain suite
