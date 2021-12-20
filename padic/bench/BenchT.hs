{-# language TypeApplications #-}
{-# language DataKinds #-}
import Criterion.Main
import Padic

addBench :: Base p => Z p -> Int -> Z p
addBench w n = w + sum (fromIntegral <$> [1..n])

mulBench :: Base p => Z p -> Int -> Z p
mulBench w n = w + product (fromIntegral <$> [1..n])

suite :: [Benchmark]
suite =
  [ bgroup
      "addition"
      [ bench "Z 2 1000" $ whnf (addBench (0 :: Z 13)) 1000
      , bench "Z 2 2000" $ whnf (addBench (0 :: Z 13)) 2000
      , bench "Z 2 3000" $ whnf (addBench (0 :: Z 13)) 3000
      , bench "Z 2 4000" $ whnf (addBench (0 :: Z 13)) 4000 ]
  , bgroup
      "multiplication"
      [ bench "Z 2 1000" $ whnf (mulBench (0 :: Z 13)) 1000
      , bench "Z 2 2000" $ whnf (mulBench (0 :: Z 13)) 2000
      , bench "Z 2 3000" $ whnf (mulBench (0 :: Z 13)) 3000
      , bench "Z 2 4000" $ whnf (mulBench (0 :: Z 13)) 4000 ]
  ]

main :: IO ()
main = defaultMain suite
