{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE UndecidableSuperClasses #-}
module Ya.Algebra.Definition where

import Ya.Algebra.Abstract

class Dumb x
instance Dumb x

class Mapping v vv from into f tt where
	mapping :: v from a o -> vv into (f a) (tt o)

instance Mapping Flat Flat from into t tt => Mapping Dual Dual from into tt t
	where mapping (U_II_I from) = U_II_I (map @Flat @Flat @from @into @t @tt from)

instance Mapping Dual Flat from into t tt => Mapping Flat Dual from into tt t
	where mapping (U_I_II from) = U_II_I (map @Dual @Flat @from @into @t @tt from)

map :: forall v vv from into t tt a o .
	Mapping v vv from into t tt =>
	Castable Dual Arrow (v from a o) =>
	Castable Flat Arrow (vv into (t a) (tt o)) =>
	Supertype (v from a o) -> Supertype (vv into (t a) (tt o))
map from = unwrap @Arrow (mapping @v @vv @from @into @t @tt @a @o (wrap @Arrow from))

type Component v = Transformation v Functor

component :: forall v from into t tt o .
	Component v from into t tt =>
	(Supertype (v from o o) ~ from o o) =>
	Castable Dual Arrow (v from o o) =>
	into (t o) (tt o)
component = unwrap @Arrow (mapping @v @Flat @from @into @t @tt @_ @o (wrap @Arrow identity))

{- [LAW] Associativity: compose f (compose g) ≡ compose (compose f g) -}
class
	( forall e . Mapping Flat Flat from Arrow (U_I_II from e) (U_I_II from e)
	, forall e . Mapping Dual Flat from Arrow (U_II_I from e) (U_II_I from e)
	) => Precategory from where
	compose :: from a o -> from e a -> from e o
	compose post pre = let U_I_II y = map @Flat @Flat post (U_I_II pre) in y

deriving instance
	( forall e . Mapping Flat Flat from Arrow (U_I_II from e) (U_I_II from e)
	, forall e . Mapping Dual Flat from Arrow (U_II_I from e) (U_II_I from e)
	) => Precategory from

{- [LAW] Left identity: identity . f ≡ f -}
{- [LAW] Right identity: f . identity ≡ f -}
class Precategory from => Category from
	where identity :: from a a

{- [LAW] Identity preserving: mapping identity ≡ identity -}
{- [LAW] Composition preserving: mapping (f . g) ≡ mapping f . mapping g -}
class (Category from, Category into, Mapping v Flat from into t t) => Functor v from into t
deriving instance (Category from, Category into, Mapping v Flat from into t t) => Functor v from into t

functor :: forall v from into t a o .
	Functor v from into t =>
	Castable Dual Arrow (v from a o) =>
	Supertype (v from a o) -> into (t a) (t o)
functor = map @v @Flat @from @into @t @t @a @o

{- [LAW] Composition preserving: mapping (f . g) ≡ mapping f . mapping g -}

class
	( Precategory from, Precategory into
	, Mapping v Flat from into t t
	, Dumb (x v from into t)
	) => Semi v x from into t

deriving instance
	( Precategory from, Precategory into
	, Mapping v Flat from into t t
	, Dumb (Functor v from into t)
	) => Semi v Functor from into t

semifunctor :: forall v from into t a o .
	Semi v Functor from into t =>
	Castable Dual Arrow (v from a o) =>
	Supertype (v from a o) -> into (t a) (t o)
semifunctor = map @v @Flat @from @into @t @t @a @o

type Endo v x c into = x v c into into

{- LAW: mapping @tt @tt morphism . component @t @tt = component @t @tt . mapping morphism @t @t -}
{- LAW: mapping @tt @tt morphism . component @t @tt = component @t @tt . mapping morphism @t @t -}
class
	( Mapping v Flat from into t tt
	, x v from into t
	, x v from into tt
	) => Transformation v x from into t tt

deriving instance
	( Mapping v Flat from into t tt
	, x v from into t
	, x v from into tt
	) => Transformation v x from into t tt

type Natural = Flat

type Dinatural = Dual

type Covariant t = t Flat

type Contravariant t = t Dual

type Kleisli u t = U_I_T_II t u

class (forall r . Transformation v x from Arrow t (UU_V_U_I_II_T_II v from into t r)) =>
	Yoneda v x from into t where
	yoneda :: forall a r .
		Category from =>
		Precategory into =>
		(Supertype (v from a a) ~ from a a) =>
		Castable Dual Arrow (v from a a) =>
		Castable Dual into (v from a r) =>
		t a -> into (Supertype (v from a r)) (t r)
	yoneda x = unwrap
		(map @v @Flat @from @Arrow @t @(UU_V_U_I_II_T_II v from into t r) identity x)
		`compose` wrap @into @(v from a r)

deriving instance
	(forall e . Transformation v x from Arrow t
		(UU_V_U_I_II_T_II v from into t e)) =>
	Yoneda v x from into t 

type family Representation t where
	Representation I = Unit
	Representation (U_I_II Arrow a) = a
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

type family Co x where Co (x Flat) = x Dual

type family Object diagram = r | r -> diagram where
	Object (Both (Flat Arrow)) = (/\)
	Object (Both (Dual Arrow)) = (\/)

type family Neutral p where
	Neutral (/\) = Unit
	Neutral (\/) = Void

class
	( forall e . Mapping v v from into (This u e) I
	, forall e . Mapping v v from into (That u e) I
	) => Cone v from into u

deriving instance
	( forall e . Mapping v v from into (This u e) I
	, forall e . Mapping v v from into (That u e) I
	) => Cone v from into u

this :: forall v from into a o e .
	Cone v from into (Object (Both (v into))) =>
	Castable Dual Arrow (v from a o) =>
	Castable Flat Arrow (v into (This (Object (Both (v into))) e a) (I o)) =>
	Supertype (v from a o) -> Supertype (v into (This (Object (Both (v into))) e a) (I o))
this from = map @v @v @from @into @(This (Object (Both (v into))) e) @I @a @o from

that :: forall v from into a t e .
	Cone v from into (Object (Both (v into))) =>
	Castable Dual Arrow (v from a t) =>
	Castable Flat Arrow (v into (That (Object (Both (v into))) e a) (I t)) =>
	Supertype (v from a t) -> Supertype (v into (That (Object (Both (v into))) e a) (I t))
that from = map @v @v @from @into @(That (Object (Both (v into))) e) @I @a @t from

type Limit v from into =
	( Cone v from into (Object (Both (v into)))
	, Mapping v v from into I (Both (Object (Both (v into))))
	)

type Product into = Object (Both (Flat into))

type Sum into = Object (Both (Dual into))

type Terminal o into a = o Flat into U_ a a

type Initial o into a = o Dual into U_ a a

-- TODO: generalize via colimits
absurd :: Void -> a
absurd x = case x of {}

type Day = U_V_UU_UUU_UUUU_T_TT_I_II_III (/\)

class 
	( x Flat into from t
	, x Flat from into tt
	, Transformation Flat x into from (T_TT_I t tt) I
	, Transformation Flat x from into I (T_TT_I tt t)
	) => Adjoint x from into t tt

deriving instance
	( x Flat into from t
	, x Flat from into tt
	, Transformation Flat x into from (T_TT_I t tt) I
	, Transformation Flat x from into I (T_TT_I tt t)
	) => Adjoint x from into t tt

class
	( forall e ee . Mapping v Flat from Arrow (Day v from u uu t t e ee) t
	, Mapping v Flat from Arrow (v Arrow (Neutral uu)) t
	, x v from Arrow t
	) => Monoidal v x from u uu t where

deriving instance
	( forall e ee . Mapping v Flat from Arrow (Day v from u uu t t e ee) t
	, Mapping v Flat from Arrow (v Arrow (Neutral uu)) t
	, x v from Arrow t
	) => Monoidal v x from u uu t

monoidal :: forall v from t u uu a o e ee .
	Monoidal v Functor from u uu t =>
	Castable Dual Arrow (v from a o) =>
	Castable Dual Arrow (v from (uu e ee) a) =>
	Supertype (v from a o)
		-> Supertype (v from (uu e ee) a)
		-> u (t e) (t ee) -> t o
monoidal from t x = map @v @Flat @from @(->)
	@(Day v from u uu t t e ee) @t from
	(U_V_UU_UUU_UUUU_T_TT_I_II_III (These x (wrap @Arrow @(v from (uu e ee) a) t)))

-- TODO: generalize
point :: forall t o .
	Monoidal Flat Functor Arrow (/\) (/\) t =>
	o -> t o
point x = component @Flat @Arrow @(->) @(Flat (->) Unit) @t (U_I_II (\_ -> x))

-- TODO: generalize
empty :: forall t o .
	Monoidal Flat Functor Arrow (/\) (\/) t =>
	t o
empty = component @Flat @Arrow @(->) @(Flat (->) Void) @t (U_I_II absurd)

rewrap :: forall into a o .
	Precategory into =>
	Castable Dual into o => 
	Castable Flat into a =>
	into (Supertype a) (Supertype o) -> into a o
rewrap f = wrap `compose` f `compose` unwrap

wrapped :: forall into a o .
	Precategory into =>
	Castable Flat into o =>
	Castable Dual into a =>
	into a o -> into (Supertype a) (Supertype o)
wrapped f = unwrap `compose` f `compose` wrap

i_ :: forall into u a t e .
	Precategory into =>
	Castable Dual into (U_II_I u e a) =>
	Castable Flat into (U_II_I u e t) =>
	into (U_II_I u e a) (U_II_I u e t) -> into (u a e) (u t e)
i_ f = unwrap @into @(U_II_I _ _ _) `compose` f `compose` wrap @into @(U_II_I _ _ _)

_i :: forall into u a t e .
	Precategory into =>
	Castable Dual into (U_I_II u e a) =>
	Castable Flat into (U_I_II u e t) =>
	into (U_I_II u e a) (U_I_II u e t) -> into (u e a) (u e t)
_i f = unwrap @into @(U_I_II _ _ _) `compose` f `compose` wrap @into @(U_I_II _ _ _)
