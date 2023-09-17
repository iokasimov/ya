{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE UndecidableSuperClasses #-}
module Ya.Algebra.Definition where

import Ya.Algebra.Abstract

class Transformation v f g from into where
	transformation :: v from s t -> into (f s) (g t)

transform :: forall v from into f g s t .
	Transformation v f g from into =>
	Castable Dual Arrow (v from s t) =>
	Supertype (v from s t) -> into (f s) (g t)
transform from = transformation @v @f @g @from @into @s @t (wrap @Arrow from)

component :: forall v from into f g t .
	Category from =>
	(Supertype (v from t t) ~ from t t) =>
	Castable Dual Arrow (v from t t) =>
	Transformation v f g from into =>
	into (f t) (g t)
component = transformation @v @f @g @from @into @_ @t (wrap @Arrow identity)

{- [LAW] Associativity: compose f (compose g) ≡ compose (compose f g) -}
class
	( forall i . Transformation Flat (U_I_II from i) (U_I_II from i) from Arrow
	, forall i . Transformation Dual (U_II_I from i) (U_II_I from i) from Arrow
	) => Semigroupoid from where
	compose :: from s t -> from i s -> from i t
	compose post pre = let U_I_II y = transform @Flat post (U_I_II pre) in y

deriving instance
	( forall i . Transformation Flat (U_I_II from i) (U_I_II from i) from Arrow
	, forall i . Transformation Dual (U_II_I from i) (U_II_I from i) from Arrow
	) => Semigroupoid from

{- [LAW] Left identity: identity . f ≡ f -}
{- [LAW] Right identity: f . identity ≡ f -}
class Semigroupoid from => Category from
	where identity :: from s s

class (m from, mm into, Transformation v f f from into)
	=> Mapping m mm v from into f
deriving instance (m from, mm into, Transformation v f f from into)
	=> Mapping m mm v from into f

{- [LAW] Composition preserving: transformation (f . g) ≡ transformation f . transformation g -}
type Semifunctor = Mapping Semigroupoid Semigroupoid

semifunctor :: forall v from into f s t .
	Semifunctor v from into f =>
	Castable Dual Arrow (v from s t) =>
	Supertype (v from s t) -> into (f s) (f t)
semifunctor = transform @v @from @into @f @f @s @t

{- [LAW] Identity preserving: transformation identity ≡ identity -}
{- [LAW] Composition preserving: transformation (f . g) ≡ transformation f . transformation g -}
type Functor = Mapping Category Category

functor :: forall v from into f s t .
	Functor v from into f =>
	Castable Dual Arrow (v from s t) =>
	Supertype (v from s t) -> into (f s) (f t)
functor = transform @v @from @into @f @f @s @t

-- TODO: turn into a type family so it should work with Monoidal Functor as well
type Semi v functor = Mapping Semigroupoid Semigroupoid v

-- Doesn't work with Semi Functor declarations 
type Endo v functor into = functor v into into

class (t v f g from into, f' v from into f, g' v from into g)
	=> Compositional f' g' t v f g from into
deriving instance (t v f g from into, f' v from into f, g' v from into g) 
	=> Compositional f' g' t v f g from into

{- LAW: transformation @g @g morphism . component @f @g = component @f @g . transformation morphism @f @f -}
type Natural = Compositional Functor Functor

type Covariant f = f Flat

type Contravariant f = f Dual

type Kleisli = U_I_T_II

instance Transformation Flat (U_I_II Arrow s) (U_I_II Arrow s) Arrow Arrow
	where transformation (U_I_II from) (U_I_II between) = U_I_II (\x -> from (between x))

instance Transformation Dual (U_II_I Arrow t) (U_II_I Arrow t) Arrow Arrow
	where transformation (U_II_I from) (U_II_I between) = U_II_I (\x -> between (from x))

instance Category Arrow where
	identity = \x -> x

type family Representation t where
	Representation I = Unit
	Representation (U_I_II Arrow i) = i
	Representation (T_TT_I t tt) =
		Representation t /\ Representation tt
	Representation (T_TT_TTT_I t tt ttt) =
		Representation t /\ Representation tt /\ Representation ttt
	Representation (U_I_I (/\)) = Unit \/ Unit

class
	 ( Compositional x x Transformation v t (v hom (Representation t)) from into
	 , Compositional x x Transformation v (v hom (Representation t)) t from into
	 ) => Representable hom v x from into t

-- TODO: define these instances in Algebra module
deriving instance
	( Compositional x x Transformation v t (v hom (Representation t)) from into
	, Compositional x x Transformation v (v hom (Representation t)) t from into
	) => Representable hom v x from into t

type family Neutral p where
	Neutral (/\) = Unit
	Neutral (\/) = Void

type Day = U_UU_UUU_UUUU_T_TT_I_II_III (/\)

class
	( Transformation v (Day (v from) p pp f f i ii) f from into
	, Transformation v (Day (v from) p pp I f i ii) f from into
	, Transformation v (Day (v from) p pp f I i ii) f from into
	, Transformation v (v from (Neutral p)) f from into
	) => Monoidal v f p pp from into i ii  
