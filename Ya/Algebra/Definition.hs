{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE UndecidableSuperClasses #-}
module Ya.Algebra.Definition where

import Ya.Algebra.Abstract

class Transformation v from into f g where
	transformation :: v from s t -> into (f s) (g t)

transform :: forall v from into f g s t .
	Transformation v from into f g =>
	Castable Dual Arrow (v from s t) =>
	Supertype (v from s t) -> into (f s) (g t)
transform from = transformation @v @from @into @f @g @s @t (wrap @Arrow from)

component :: forall v from into f g t .
	Category from =>
	(Supertype (v from t t) ~ from t t) =>
	Castable Dual Arrow (v from t t) =>
	Transformation v from into f g =>
	into (f t) (g t)
component = transformation @v @from @into @f @g @_ @t (wrap @Arrow identity)

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

class (m from, mm into, Transformation v from into f f) => Mapping m mm v f from into where
deriving instance (m from, mm into, Transformation v from into f f) => Mapping m mm v f from into

{- [LAW] Composition preserving: transformation (f . g) ≡ transformation f . transformation g -}
type Semifunctor = Mapping Semigroupoid Semigroupoid

semifunctor :: forall v from into f s t .
	Semifunctor v f from into =>
	Castable Dual Arrow (v from s t) =>
	Supertype (v from s t) -> into (f s) (f t)
semifunctor = transform @v @from @into @f @f @s @t

{- [LAW] Identity preserving: transformation identity ≡ identity -}
{- [LAW] Composition preserving: transformation (f . g) ≡ transformation f . transformation g -}
type Functor = Mapping Category Category

functor :: forall v from into f s t .
	Functor v f from into =>
	Castable Dual Arrow (v from s t) =>
	Supertype (v from s t) -> into (f s) (f t)
functor = transform @v @from @into @f @f @s @t

class (t v from into f g, f' v f from into, g' v g from into) => Compositional t v f' g' f g from into where
deriving instance (t v from into f g, f' v f from into, g' v g from into) => Compositional t v f' g' f g from into

{- LAW: transformation @g @g morphism . component @f @g = component @f @g . transformation morphism @f @f -}
type Natural t = Compositional t Flat Functor Functor

type Infranatural t = Compositional t Dual Functor Functor

type Covariant f = f Flat

type Contravariant f = f Dual

type Kleisli = U_I_T_II

instance Transformation Flat Arrow Arrow (U_I_II Arrow s) (U_I_II Arrow s)
	where transformation (U_I_II from) (U_I_II between) = U_I_II (\x -> from (between x))

instance Transformation Dual Arrow Arrow (U_II_I Arrow t) (U_II_I Arrow t)
	where transformation (U_II_I from) (U_II_I between) = U_II_I (\x -> between (from x))

instance Category Arrow where
	identity = \x -> x

data Void

data Unit = Unit

type family Representation t where
	Representation Identity = Unit
	Representation (U_I_II Arrow i) = i
	Representation (T_TT_I t tt) =
		Representation t `And` Representation tt
	Representation (T_TT_TTT_I t tt ttt) =
		Representation t `And` Representation tt `And` Representation ttt
	Representation (U_I_I And) = Unit `Or` Unit

-- TODO: there is no proof of natural isomorphism
type Representable v f t hom into =
	( f v t into into
	, Transformation v into into t (v hom (Representation t))
	, Transformation v into into (v hom (Representation t)) t
	)