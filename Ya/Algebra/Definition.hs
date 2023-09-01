{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE UndecidableInstances #-}
module Ya.Algebra.Definition where

import Ya.Algebra.Abstract

class Transformation v from into f g where
	transformation :: v from s t -> into (f s) (g t)

transform :: forall v from into f g s t .
	Transformation v from into f g =>
	Castable Dual Arrow (v from s t) =>
	Supertype (v from s t) -> into (f s) (g t)
transform from = transformation @v @from @into @f @g @s @t (wrap @Arrow from)

{- [LAW] Associativity: compose f (compose g) ≡ compose (compose f g) -}
class
	( forall i . Transformation Flat from Arrow (U_I_II from i) (U_I_II from i)
	, forall i . Transformation Dual from Arrow (U_II_I from i) (U_II_I from i)
	) => Semigroupoid from where
	compose :: from s t -> from i s -> from i t
	compose post pre = let U_I_II y = transform @Flat post (U_I_II pre) in y

deriving instance
	( forall i . Transformation Flat from Arrow (U_I_II from i) (U_I_II from i)
	, forall i . Transformation Dual from Arrow (U_II_I from i) (U_II_I from i)
	) => Semigroupoid from

{- [LAW] Left identity: identity . f ≡ f -}
{- [LAW] Right identity: f . identity ≡ f -}
class Semigroupoid from => Category from where
	identity :: from s s

instance Transformation Flat Arrow Arrow (U_I_II Arrow s) (U_I_II Arrow s)
	where transformation (U_I_II from) (U_I_II between) = U_I_II (\x -> from (between x))

instance Transformation Dual Arrow Arrow (U_II_I Arrow t) (U_II_I Arrow t)
	where transformation (U_II_I from) (U_II_I between) = U_II_I (\x -> between (from x))

instance Category Arrow where
	identity = \x -> x

type Kleisli = U_I_T_II