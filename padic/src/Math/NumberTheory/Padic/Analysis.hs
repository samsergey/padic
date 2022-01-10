{-# LANGUAGE FlexibleContexts #-}
{-# OPTIONS_HADDOCK hide, prune, ignore-exports #-}

{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE NoStarIsType #-}

module Math.NumberTheory.Padic.Analysis where

import Math.NumberTheory.Padic.Types
import Data.Mod
import Data.Maybe
import GHC.TypeLits hiding (Mod)
  
{- | Returns p-adic solutions (if any) of the equation \(f(x) = 0\) using Hensel lifting method.
First, solutions of \(f(x) = 0\ \mathrm{mod}\ p\) are found, then by Newton's method this solution is get lifted to p-adic number (up to specified precision).

Examples:

>>> henselLifting (\x -> x*x - 2) (\x -> 2*x) :: [Z 7]
[…64112011266421216213,…02554655400245450454]
>>> henselLifting (\x -> x*x - x) (\x -> 2*x-1) :: [Q 10]
[0,1,…92256259918212890625,…07743740081787109376]
-}
henselLifting ::
     (Eq n, PadicNum n, KnownRadix p, Digit n ~ Mod p)
  => (n -> n) -- ^ Function to be vanished.
  -> (n -> n) -- ^ Derivative of the function.
  -> [n] -- ^ The result.
henselLifting f f' = res
  where
    pr = precision (head res)
    res = findSolutionMod f >>= iterateM pr step
    step x = do
      invf' <- maybeToList (inverse (f' x))
      return (x - f x * invf')

{- | Returns solution of the equation \(f(x) = 0\ \mathrm{mod}\ p\) in p-adics.
Used as a first step if `henselLifting` function and is usefull for introspection.

>>> findSolutionMod (\x -> x*x - 2) :: [Z 7]
[3,4]
>>> findSolutionMod (\x -> x*x - x) :: [Q 10]
[0.0,1.0,5.0,6.0]
-}
findSolutionMod :: (PadicNum n, KnownRadix p, Digit n ~ Mod p)
                => (n -> n) -> [n]
findSolutionMod f = [ fromMod d | d <- [0..], fm d == 0 ]
  where
    fm = firstDigit . f . fromMod
    fromMod x = fromDigits [x]

iterateM :: (Eq a, Monad m) => Int -> (a -> m a) -> a -> m a
iterateM n f = go n
  where
    go 0 x = pure x
    go i x = do
      y <- f x
      if x == y then pure x else go (i - 1) y
   
-------------------------------------------------------------

{- | Returns p-adic exponent function, calculated via Taylor series.
For given radix \(p\) converges for numbers which satisfy inequality:

\[|x|_p < p^\frac{1}{1-p}.\]

-}
pExp :: (Eq n, PadicNum n, Fractional n) => n -> Either String n
pExp x | fromRational (norm x) > p ** (-1/(p-1)) = Left "exp does not converge!"
       | otherwise = go (2 * precision x) 0 1 1
  where
    p = fromIntegral (radix x)
    go n s t i
      | n <= 0 = Left "exp failed to converge within precision!"
      | t == 0 = Right s
      | otherwise = go (n - 1) (s + t) (t*x/i) (i+1)

{- | Returns p-adic logarithm function, calculated via Taylor series.
For given radix \(p\) converges for numbers which satisfy inequality:

\[|x|_p < 1.\]

-}
pLog :: (Eq b, PadicNum b, Fractional b) => b -> Either String b
pLog x' | fromRational (norm (x' - 1)) >= 1 = Left "log does not converge!"
        | otherwise = f (x' - 1)
  where
    f x = go (2 * precision x) 0 x 1
      where
        nx = negate x
        go n s t i
          | n <= 0 = Left "log failed to converge within precision!"
          | t == 0 = Right s
          | otherwise = go (n - 1) (s + t/i) (nx*t) (i+1)

{- | Returns p-adic hyperbolic sine function, calculated via Taylor series.
For given radix \(p\) converges for numbers which satisfy inequality:

\[|x|_p < p^\frac{1}{1-p}.\]

-}
pSinh :: (PadicNum b, Fractional b) => b -> Either [Char] b
pSinh x
  | fromRational (norm x) > p ** (-1/(p-1)) = Left "sinh does not converge!"
  | otherwise = go (2 * precision x) 0 x 2
  where
    p = fromIntegral (radix x)
    x2 = x*x
    go n s t i
      | n <= 0 = Left "sinh failed to converge within precision!"
      | t == 0 = Right s
      | otherwise = go (n - 1) (s + t) (t*x2/(i*(i+1))) (i+2)

{- | Returns p-adic inverse hyperbolic sine function, calculated as

\[\mathrm{sinh}^{ -1} x = \log(x + \sqrt{x^2+1})\]

with convergence, corresponding to `pLog` and `pPow` functions.
-}
pAsinh :: (PadicNum b, Fractional b) => b -> Either String b
pAsinh x = do y <- pPow (x*x + 1) (1/2)
              pLog (x + y)

{- | Returns p-adic hyperbolic cosine function, calculated via Taylor series.
For given radix \(p\) converges for numbers which satisfy inequality:

\[|x|_p < p^\frac{1}{1-p}.\]

-}
pCosh :: (PadicNum b, Fractional b) => b -> Either [Char] b
pCosh x
  | fromRational (norm x) > p ** (-1/(p-1)) = Left "cosh does not converge!"
  | otherwise = go (2 * precision x) 0 1 1
  where
    p = fromIntegral (radix x)
    x2 = x*x
    go n s t i
      | n <= 0 = Left "cosh failed to converge within precision!"
      | t == 0 = Right s
      | otherwise = go (n - 1) (s + t) (t*x2/(i*(i+1))) (i+2)

{- | Returns p-adic inverse hyperbolic cosine function, calculated as

\[\mathrm{cosh}^{ -1}\ x = \log(x + \sqrt{x^2-1}),\]

with convergence, corresponding to `pLog` and `pPow` functions.

-}
pAcosh :: (PadicNum b, Fractional b) => b -> Either String b
pAcosh x = do y <- pPow (x*x - 1) (1/2)
              pLog (x + y)

{- | Returns p-adic hyperbolic tan function, calculated as

\[\mathrm{tanh}\ x = \frac{\mathrm{sinh}\ x}{\mathrm{cosh}\ x},\]

with convergence, corresponding to `pSinh` and `pCosh` functions.
-}
pTanh :: (Fractional b, PadicNum b) => b -> Either [Char] b
pTanh x = (/) <$> pSinh x <*> pCosh x

{- | Returns p-adic inverse hyperbolic tan function, calculated as

\[\mathrm{tanh}^{ -1 }\ x = \frac{1}{2} \log\left(\frac{x + 1}{x - 1}\right)\]

with convergence, corresponding to `pLog` function.
-}
pAtanh :: (PadicNum b, Fractional b) => b -> Either String b
pAtanh x = do y <- pLog ((x + 1) / (x - 1))
              return $ y / 2


{- | Returns p-adic hyperbolic cosine function, calculated via Taylor series.
For given radix \(p\) converges for numbers which satisfy inequality:

\[|x|_p < p^\frac{1}{1-p}.\]

-}
pSin :: (PadicNum b, Fractional b) => b -> Either [Char] b
pSin x
  | fromRational (norm x) > p ** (-1/(p-1)) = Left "sin does not converge!"
  | otherwise = go (2 * precision x) 0 x 2
  where
    p = fromIntegral (radix x)
    x2 = negate x*x
    go n s t i
      | n <= 0 = Left "sin failed to converge within precision!"
      | t == 0 = Right s
      | otherwise = go (n - 1) (s + t) (t*x2/(i*(i+1))) (i+2)

{- | Returns p-adic cosine function, calculated via Taylor series.
For given radix \(p\) converges for numbers which satisfy inequality:

\[|x|_p < p^\frac{1}{1-p}.\]

-}
pCos :: (PadicNum b, Fractional b) => b -> Either [Char] b
pCos x
  | fromRational (norm x) > p ** (-1/(p-1)) = Left "cos does not converge!"
  | otherwise = go (2 * precision x) 0 1 1
  where
    p = fromIntegral (radix x)
    x2 = negate x*x
    go n s t i
      | n <= 0 = Left "cos failed to converge within precision!"
      | t == 0 = Right s
      | otherwise = go (n - 1) (s + t) (t*x2/(i*(i+1))) (i+2)

{- | Returns p-adic arcsine function, calculated via Taylor series.
For given radix \(p\) converges for numbers which satisfy inequality:

\[|x|_p < 1.\]

-}
pAsin x | norm x >= 1 = Left "asin does not converge!"
        | otherwise = Right $
          sum $ takeWhile (\t -> valuation t < pr) $
          take (2*pr) $ zipWith (*) xs cs
  where
    pr = precision x
    x2 = x*x
    xs = iterate (x2 *) x
    cs = zipWith (/) (zipWith (/) n2f nf2) [2*n+1 | n <- fromInteger <$> [0..]]
    n2f = scanl (*) 1 [n*(n+1) | n <- fromInteger <$> [1,3..]]
    nf2 = scanl (*) 1 [4*n^2 | n <- fromInteger <$> [1..]]

{- | Returns p-adic square root, calculated for odd radix via Hensel lifting,
and for \(p=2\) by recurrent product.
-}
pSqrt ::
     ( Fractional n
     , PadicNum n
     , KnownRadix p
     , Digit n ~ Mod p
     , PadicNum (Unit n)
     , Lifted (Unit n) ~ Integer
     )
  => n -> [n]
pSqrt x
  | odd (radix x) && isSquareResidue x =
    henselLifting (\y -> y * y - x) (2 *)
  | lifted (unit x) `mod` 4 /= 3 && lifted (unit x) `mod` 8 == 1 =
      let r = pSqrt2 x in [r, -r]
  | otherwise = []

pSqrt2 :: (PadicNum a, Fractional a) => a -> a
pSqrt2 a = product $
           takeWhile (/= 1)
           $ take (2*precision a)
           $ go ((a - 1) / 8)
  where
    go x = (1 + 4*x) : go ((-2)*(x / (1 + 4*x))^2)

{- | Exponentiation for p-adic numbers, calculated as

\[ x^y = e^{y \log x}, \]

with convergence, corresponding to `pExp` and `pLog` functions.
-}
pPow :: (PadicNum p, Fractional p) => p -> p -> Either String p
pPow x y = case pLog x >>= \z -> pExp (z*y) of
      Right res -> Right res
      Left _ -> Left "exponentiation doesn't converge!"

{- | Returns @True@ for p-adics with square residue as a first digit.
-}
isSquareResidue :: (PadicNum n, KnownRadix p, Digit n ~ Mod p) => n -> Bool
isSquareResidue x = any (\m -> m*m == firstDigit x) [0..]

