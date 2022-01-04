{-# language TypeApplications #-}
{-# language DataKinds #-}
{-# language FlexibleContexts #-}

import Criterion.Main
import Padic
import qualified PadicL as L
import Data.Maybe

addBench :: (Num (f p), Radix p) => f p -> Int -> f p
addBench w n = w + sum (fromIntegral <$> [1..n])

mulBench :: (Num (f p), Radix p) => f p -> Int -> f p
mulBench w n = w + product (fromIntegral <$> [1..n])


--divBench :: (Num (f p), Radix p) => (f p -> f p -> Maybe (f p)) -> f p -> Int -> f p
divBench d w n = w + sum s
  where
    s = catMaybes [ d a b | a <- fromIntegral <$> [1..n]
                          , b <- fromIntegral <$> [1..n] ]


suite :: [Benchmark]
suite =
  [ bgroup
      "add"
      [ bench "Z 2" $ whnf (addBench (0 :: Z 2)) 4000
      , bench "Z 3" $ whnf (addBench (0 :: Z 3)) 4000 
      , bench "Z 13" $ whnf (addBench (0 :: Z 13)) 4000
      , bench "Z 251" $ whnf (addBench (0 :: Z 251)) 4000
      , bench "L.Z 2" $ whnf (addBench (0 :: L.Z 2)) 4000
      , bench "L.Z 3" $ whnf (addBench (0 :: L.Z 3)) 4000
      , bench "L.Z 13" $ whnf (addBench (0 :: L.Z 13)) 4000
      , bench "L.Z 251" $ whnf (addBench (0 :: L.Z 251)) 4000]
  , bgroup
      "mul"
      [ bench "Z 2" $ whnf (mulBench (0 :: Z 2)) 4000
      , bench "Z 3" $ whnf (mulBench (0 :: Z 3)) 4000 
      , bench "Z 13" $ whnf (mulBench (0 :: Z 13)) 4000
      , bench "Z 251" $ whnf (mulBench (0 :: Z 251)) 4000
      , bench "L.Z 2" $ whnf (mulBench (0 :: L.Z 2)) 4000
      , bench "L.Z 3" $ whnf (mulBench (0 :: L.Z 3)) 4000
      , bench "L.Z 13" $ whnf (mulBench (0 :: L.Z 13)) 4000
      , bench "L.Z 251" $ whnf (mulBench (0 :: L.Z 251)) 4000]
  , bgroup
      "div"
      [ bench "Z 2" $ whnf (divBench divMaybe (0 :: Z 2)) 60
      , bench "Z 3" $ whnf (divBench divMaybe (0 :: Z 3)) 60 
      , bench "Z 13" $ whnf (divBench divMaybe (0 :: Z 13)) 60
      , bench "Z 251" $ whnf (divBench divMaybe (0 :: Z 251)) 60
      , bench "L.Z 2" $ whnf (divBench L.divMaybe (0 :: L.Z 2)) 60
      , bench "L.Z 3" $ whnf (divBench L.divMaybe (0 :: L.Z 3)) 60
      , bench "L.Z 13" $ whnf (divBench L.divMaybe (0 :: L.Z 13)) 60
      , bench "L.Z 251" $ whnf (divBench L.divMaybe (0 :: L.Z 251)) 60]  ]

main :: IO ()
main = defaultMain suite
