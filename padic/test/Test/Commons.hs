{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}

module Test.Commons (testSuite) where

import Math.NumberTheory.Padic
import GHC.TypeLits hiding (Mod)
import Test.Tasty
import Test.Tasty.HUnit
import Test.Tasty.QuickCheck
import Test.QuickCheck
import Data.Mod
import Data.Ratio

instance KnownRadix m => Arbitrary (Mod m) where
  arbitrary = fromInteger <$> arbitrary

newtype AnyRadix = AnyRadix Integer
  deriving (Show, Eq, Num)
  
instance Arbitrary AnyRadix where
  arbitrary = AnyRadix <$> arbitrary `suchThat` (> 1)
 

a @/= b = assertBool "" (a /= b)

------------------------------------------------------------

cycleTest :: TestTree
cycleTest = testGroup "findCycle tests"
  [ testCase "1" $ findCycle 10 [1..5] @?= Nothing
  , testCase "2" $ findCycle 10 [1] @?= Nothing
  , testCase "3" $ findCycle 10 (repeat 1) @?= Just ([],[1])
  , testCase "4" $ findCycle 10 ([1..5] ++ repeat 1) @?= Just ([1..5],[1])
  , testCase "5" $ findCycle 10 ([1..15] ++ repeat 1) @?= Nothing
  , testCase "6" $ findCycle 10 ([1,1,1] ++ repeat 1) @?= Just ([],[1])
  , testCase "7" $ findCycle 10 ([2,1,1] ++ repeat 1) @?= Just ([2],[1])
  , testCase "8" $ findCycle 10 ([1,2,3] ++ cycle [1,2,3]) @?= Just ([],[1,2,3])
  , testCase "9" $ findCycle 10 ([2,3] ++ cycle [1,2,3]) @?= Just ([],[2,3,1])
  , testCase "10" $ findCycle 10 ([0,1,2,3] ++ cycle [1,2,3]) @?= Just ([0],[1,2,3])
  , testCase "11" $ findCycle 10 ([0,2,3] ++ cycle [1,2,3]) @?= Just ([0],[2,3,1])
  , testCase "12" $ findCycle 200 ([1..99] ++ cycle [100..200]) @?= Just ([1..99],[100..200])  ]

------------------------------------------------------------

radixTest :: KnownRadix p => Mod p -> Positive Integer -> Bool
radixTest m (Positive n) =
  let ds = tail (m : toRadix n)
      n' = fromRadix ds 
  in n' == n && toRadix n' == ds

radixTests = testGroup "Conversion to and from digits"
  [ testProperty "2" $ radixTest (0 :: Mod 2)
  , testProperty "10" $ radixTest (0 :: Mod 10)
  , testProperty "65536" $ radixTest (0 :: Mod 65536)
  ]
  
------------------------------------------------------------
getUnitTests = testGroup "p-adic units."
  [ testGroup "Integers"
    [ testCase "2" $ getUnitZ 2 (4) @?= (1, 2)
    , testCase "7(2)" $ getUnitZ 2 (28) @?= (7, 2)
    , testCase "7(7)" $ getUnitZ 7 (28) @?= (4, 1)
    , testProperty "0" $ \(AnyRadix p) -> getUnitZ p 0 === (0, 0)
    , testProperty "1" $ \(AnyRadix p) -> getUnitZ p 1 === (1, 0)
    , testProperty "p" $
      \(AnyRadix p) r -> let (u, k) = getUnitZ p r
                         in r === fromIntegral p ^ k * u
    ]
  , testGroup "Rationals"
    [ testCase "2" $ getUnitQ 2 (4%7) @?= (1 % 7, 2)
    , testCase "7" $ getUnitQ 7 (4%7) @?= (4 % 1, -1)
    , testProperty "0" $ \(AnyRadix p) -> getUnitQ p 0 === (0, 0)
    , testProperty "1" $ \(AnyRadix p) -> getUnitQ p 1 === (1, 0)
    , testProperty "p" $
      \(AnyRadix p) r -> let (u, k) = getUnitQ p r
                         in r === fromIntegral p^^k * u
    ]
  ]
 
------------------------------------------------------------
testSuite = testGroup "Commons"
  [ cycleTest
  , radixTests
  , getUnitTests ]
