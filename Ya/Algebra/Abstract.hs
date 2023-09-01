{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE UndecidableInstances #-}
module Ya.Algebra.Abstract where

newtype Identity i = Identity i

newtype U_I_I u i = U_I_I (u i i)

newtype U_I_II u i ii = U_I_II (u i ii)

newtype U_II_I u i ii = U_II_I (u ii i)

type Arrow = (->)

type Mono = U_I_I

type Flat = U_I_II

type Dual = U_II_I

type family Supertype e where
	Supertype (Identity i) = i

class Castable direction morphism e where
	cast :: (direction morphism e) (Supertype e)

class (Castable Dual to f, Castable Flat to f) => Wrapper to f where
deriving instance (Castable Dual to f, Castable Flat to f) => Wrapper to f