{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}

import GHC.TypeLits hiding (Mod)
import Data.Mod

newtype a % (prec :: Nat) = Prec a

newtype Z (p :: Nat) = Z [Mod p]

class Fixed a where
  precision :: Integral i => a -> i

instance Fixed (Z p) where
  precision  _ = 20

instance (KnownNat prec, Fixed a) => Fixed (a % prec) where
  precision = fromIntegral . natVal

class Digital a where
  type Digits a
  base :: Integral i => a -> i

instance KnownNat p => Digital (Z p) where
  type Digits (Z p) = [Mod p]
  base = fromIntegral . natVal

instance Digital a => Digital (a % prec) where
  type Digits (a % prec) = Digits a
  base (Prec x) = base x
