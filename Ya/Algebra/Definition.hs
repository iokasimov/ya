{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE UndecidableSuperClasses #-}
module Ya.Algebra.Definition where

import Ya.Algebra.Abstract

class Dumb x
instance Dumb x

class Mapping v from into f g where
	mapping :: v from s t -> into (f s) (g t)

map :: forall v from into f g s t .
	Mapping v from into f g =>
	Castable Dual Arrow (v from s t) =>
	Supertype (v from s t) -> into (f s) (g t)
map from = mapping @v @from @into @f @g @s @t (wrap @Arrow from)

type Component v = Transformation v Category

component :: forall v from into f g t .
	Component v from into f g =>
	(Supertype (v from t t) ~ from t t) =>
	Castable Dual Arrow (v from t t) =>
	into (f t) (g t)
component = mapping @v @from @into @f @g @_ @t (wrap @Arrow identity)

{- [LAW] Associativity: compose f (compose g) ≡ compose (compose f g) -}
class
	( forall i . Mapping Flat from Arrow (U_I_II from i) (U_I_II from i)
	, forall i . Mapping Dual from Arrow (U_II_I from i) (U_II_I from i)
	) => Precategory from where
	compose :: from s t -> from i s -> from i t
	compose post pre = let U_I_II y = map @Flat post (U_I_II pre) in y

deriving instance
	( forall i . Mapping Flat from Arrow (U_I_II from i) (U_I_II from i)
	, forall i . Mapping Dual from Arrow (U_II_I from i) (U_II_I from i)
	) => Precategory from

{- [LAW] Left identity: identity . f ≡ f -}
{- [LAW] Right identity: f . identity ≡ f -}
class Precategory from => Category from
	where identity :: from s s

{- [LAW] Identity preserving: mapping identity ≡ identity -}
{- [LAW] Composition preserving: mapping (f . g) ≡ mapping f . mapping g -}
class (Category from, Category into, Mapping v from into f f) => Functor v from into f
deriving instance (Category from, Category into, Mapping v from into f f) => Functor v from into f

functor :: forall v from into f s t .
	Functor v from into f =>
	Castable Dual Arrow (v from s t) =>
	Supertype (v from s t) -> into (f s) (f t)
functor = map @v @from @into @f @f @s @t

{- [LAW] Composition preserving: mapping (f . g) ≡ mapping f . mapping g -}

class
	( Precategory from, Precategory into
	, Mapping v from into f f
	, Dumb (x v from into f)
	) => Semi v x from into f

deriving instance
	( Precategory from, Precategory into
	, Mapping v from into f f
	, Dumb (Functor v from into f)
	) => Semi v Functor from into f

semifunctor :: forall v from into f s t .
	Semi v Functor from into f =>
	Castable Dual Arrow (v from s t) =>
	Supertype (v from s t) -> into (f s) (f t)
semifunctor = map @v @from @into @f @f @s @t

type Endo v x c into = x v c into into

{- LAW: mapping @g @g morphism . component @f @g = component @f @g . mapping morphism @f @f -}
{- LAW: mapping @g @g morphism . component @f @g = component @f @g . mapping morphism @f @f -}
class
	( m from, m into
	, Mapping v from into f g
	, Mapping v from into f f
	, Mapping v from into g g
	) => Transformation v m from into f g

-- TODO: actually, this is wrong, we cannot define Dinatural transformations this way
deriving instance
	( m from, m into
	, Mapping v from into f g
	, Mapping v from into f f
	, Mapping v from into g g
	) => Transformation v m from into f g

type Natural = Flat

type Covariant f = f Flat

type Contravariant f = f Dual

type Kleisli = U_I_T_II

class
	( Dumb (x v from Arrow f)
	, Mapping v from Arrow f (UU_V_U_I_II_T_II v from into f t)
	) => Yoneda v x from into f t where
		yoneda :: forall p s .
			Castable Dual Arrow (v from s p) =>
			Supertype (v from s p) -> f s -> into (v from p t) (f t)
		yoneda from x = unwrap (map @v @from @Arrow
			@f @(UU_V_U_I_II_T_II v from into f t) from x)

deriving instance
	( Dumb (x v from Arrow f)
	, Mapping v from Arrow f (UU_V_U_I_II_T_II v from into f t)
	) => Yoneda v x from into f t

type family Representation t where
	Representation I = Unit
	Representation (U_I_II Arrow i) = i
	Representation (T_TT_I t tt) =
		Representation t /\ Representation tt
	Representation (T_TT_TTT_I t tt ttt) =
		Representation t /\ Representation tt /\ Representation ttt
	Representation (U_I_I (/\)) = Unit \/ Unit

class
	 ( Transformation v x from into t (v hom (Representation t))
	 , Transformation v x from into (v hom (Representation t)) t
	 ) => Representable hom v x from into t

deriving instance
	( Transformation v x from into t (v hom (Representation t))
	, Transformation v x from into (v hom (Representation t)) t
	) => Representable hom v x from into t

type family Neutral p where
	Neutral (/\) = Unit
	Neutral (\/) = Void

type Day = U_V_UU_UUU_UUUU_T_TT_I_II_III (/\)

class 
	( x v into from f
	, x v from into g
	, x v from into I
	, x v into from I
	, x v into from (T_TT_I f g)
	, x v from into (T_TT_I g f)
	, Mapping Flat into from (T_TT_I f g) I
	, Mapping Flat from into I (T_TT_I g f)
	) => Adjoint v x f g from into

deriving instance
	( x v into from f
	, x v from into g
	, x v from into I
	, x v into from I
	, x v into from (T_TT_I f g)
	, x v from into (T_TT_I g f)
	, Mapping Flat into from (T_TT_I f g) I
	, Mapping Flat from into I (T_TT_I g f)
	) => Adjoint v x f g from into

class
	( Mapping v from Arrow (Day v from u uu f f i ii) f
	, Mapping v from Arrow (v from (Neutral u)) f
	, Dumb (x v from Arrow f)
	) => Monoidal v x u uu from i ii f where

deriving instance
	( Mapping v from Arrow (Day v from p pp f f i ii) f
	, Mapping v from Arrow (v from (Neutral p)) f
	, Dumb (x v from Arrow f)
	) => Monoidal v Functor p pp from i ii f

monoidal :: forall v from into f u uu s t i ii .
	Monoidal v Functor u uu from i ii f =>
	Covariant Functor into (->) (U_I_II (/\) (f i /\ f ii)) =>
	Covariant Adjoint Functor
		(U_I_II (/\) (u (f i) (f ii)))
		(U_I_II (->) (u (f i) (f ii)))
		(->) into =>
	Castable Dual Arrow (v from s t) =>
	Castable Flat into (T_TT_I
		(U_I_II (->) (u (f i) (f ii)))
		(U_I_II (/\) (u (f i) (f ii)))
		(v from (uu i ii) s)) =>
	Castable Dual into (v from (uu i ii) s) =>
	Castable Dual into (I (v from (uu i ii) s)) =>
	Castable Flat into (U_I_II (->) (u (f i) (f ii)) (f t)) =>
	Castable Dual (->) (Day v from u uu f f i ii s) =>
	Castable Flat (->) (U_I_II (/\) (u (f i) (f ii)) (v from (uu i ii) s)) =>
	Supertype (v from s t) -> into
		(Supertype (v from (uu i ii) s))
		(u (f i) (f ii) -> f t)
monoidal from = unwrap @into @(U_I_II _ _ _)
	`compose` semifunctor @Flat 
		(map @v @from @(->) @(Day v from u uu f f i ii) @f from
			`compose` wrap @(->) `compose` unwrap @(->) @(U_I_II (/\) _ _))
	`compose` unwrap @into
	`compose` component @Flat @(->) @into @I @(_ `T_TT_I` _)
	`compose` wrap @into
	`compose` wrap @into @(v from (uu i ii) s)
