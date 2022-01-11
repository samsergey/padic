{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}

module Test.Analysis (testSuite) where

import Math.NumberTheory.Padic
import Test.Base
import GHC.TypeLits hiding (Mod)
import Test.Tasty
import Test.Tasty.HUnit
import Test.Tasty.QuickCheck
import Test.QuickCheck
import Data.Mod
import Data.Ratio

a @/= b = assertBool "" (a /= b)

------------------------------------------------------------
mulSqrt :: (Eq n, Show n, PadicNum n, Fractional n, KnownRadix p, Digit n ~ Mod p) => n -> n -> Bool
mulSqrt w a = and $ do
  x <- pSqrt a
  return $ x*x == a

testSqrt = testGroup "pSqrt properties" $
  [
    testProperty "Q 2" $ mulSqrt (0 :: Q 2)
  , testProperty "Q 7" $ mulSqrt (0 :: Q 7)
  ]

mulExp :: (Eq n, Show n, PadicNum n, Fractional n) => n -> n -> n -> Bool
mulExp w a b = either (const True) id $ do
  x <- pExp a
  y <- pExp b
  z <- pExp (a + b)
  return $ x*y == z

testExp = testGroup "pExp properties" $
  [
    testProperty "multiplication" $ mulExp (0 :: Q 2)
  , testProperty "multiplication" $ mulExp (0 :: Q 7)
  ]

testSuite = testGroup "Analysis" $
  [
    testSqrt 
  ]
