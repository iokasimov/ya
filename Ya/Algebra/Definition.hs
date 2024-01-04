{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE UndecidableSuperClasses #-}
module Ya.Algebra.Definition where

import Ya.Algebra.Abstract

class Dumb x
instance Dumb x

class Mapping v vv from into f tt where
	mapping :: v from a o -> vv into (f a) (tt o)

instance Mapping Straight Straight from into t tt => Mapping Opposite Opposite from into tt t
	where mapping (U_II_I from) = U_II_I (map @Straight @Straight @from @into @t @tt from)

instance Mapping Opposite Straight from into t tt => Mapping Straight Opposite from into tt t
	where mapping (U_I_II from) = U_II_I (map @Opposite @Straight @from @into @t @tt from)

map :: forall v vv from into t tt a o .
	Mapping v vv from into t tt =>
	Castable Opposite Arrow (v from a o) =>
	Castable Straight Arrow (vv into (t a) (tt o)) =>
	Supertype (v from a o) -> Supertype (vv into (t a) (tt o))
map from = rw @Arrow (mapping @v @vv @from @into @t @tt @a @o (wrap @Arrow from))

type Component v = Transformation v Functor

component :: forall v from into t tt o .
	Component v from into t tt =>
	(Supertype (v from o o) ~ from o o) =>
	Castable Opposite Arrow (v from o o) =>
	into (t o) (tt o)
component = rw @Arrow (mapping @v @Straight @from @into @t @tt @_ @o (wrap @Arrow identity))

{- [LAW] Associativity: compose f (compose g) ≡ compose (compose f g) -}
class
	( forall e . Mapping Straight Straight from Arrow (U_I_II from e) (U_I_II from e)
	, forall e . Mapping Opposite Straight from Arrow (U_II_I from e) (U_II_I from e)
	) => Precategory from where
	compose :: from a o -> from e a -> from e o
	compose post pre = let U_I_II y = map @Straight @Straight post (U_I_II pre) in y

deriving instance
	( forall e . Mapping Straight Straight from Arrow (U_I_II from e) (U_I_II from e)
	, forall e . Mapping Opposite Straight from Arrow (U_II_I from e) (U_II_I from e)
	) => Precategory from

{- [LAW] Left identity: identity . f ≡ f -}
{- [LAW] Right identity: f . identity ≡ f -}
class Precategory from => Category from
	where identity :: from a a

{- [LAW] Identity preserving: mapping identity ≡ identity -}
{- [LAW] Composition preserving: mapping (f . g) ≡ mapping f . mapping g -}
class (Category from, Category into, Mapping v Straight from into t t) => Functor v from into t
deriving instance (Category from, Category into, Mapping v Straight from into t t) => Functor v from into t

{- [LAW] Composition preserving: mapping (f . g) ≡ mapping f . mapping g -}

class
	( Precategory from, Precategory into
	, Mapping v Straight from into t t
	, Dumb (x v from into t)
	) => Semi v x from into t

deriving instance
	( Precategory from, Precategory into
	, Mapping v Straight from into t t
	, Dumb (Functor v from into t)
	) => Semi v Functor from into t

type Endo v x c into = x v c into into

{- LAW: mapping @tt @tt morphism . component @t @tt = component @t @tt . mapping morphism @t @t -}
{- LAW: mapping @tt @tt morphism . component @t @tt = component @t @tt . mapping morphism @t @t -}
class
	( Mapping v Straight from into t tt
	, x v from into t
	, x v from into tt
	) => Transformation v x from into t tt

deriving instance
	( Mapping v Straight from into t tt
	, x v from into t
	, x v from into tt
	) => Transformation v x from into t tt

type Natural = Straight

type Dinatural = Opposite

type Covariant t = t Straight

type Contravariant t = t Opposite

type Kleisli u t = U_I_T_II t u

class (forall r . Transformation v x from Arrow t (UU_V_U_I_II_T_II v from into t r)) =>
	Yoneda v x from into t where
	yoneda :: forall a r .
		Category from =>
		Precategory into =>
		(Supertype (v from a a) ~ from a a) =>
		Castable Opposite Arrow (v from a a) =>
		Castable Opposite into (v from a r) =>
		t a -> into (Supertype (v from a r)) (t r)
	yoneda x = rw
		(map @v @Straight @from @Arrow @t @(UU_V_U_I_II_T_II v from into t r) identity x)
		`compose` wrap @into @(v from a r)

deriving instance
	(forall e . Transformation v x from Arrow t
		(UU_V_U_I_II_T_II v from into t e)) =>
	Yoneda v x from into t 

type family Representation t where
	Representation I = ()
	Representation (U_I_II Arrow a) = a
	Representation (T_TT_I t tt) =
		Representation t `LM` Representation tt
	Representation (T_TTT_TT_I t ttt tt) =
		Representation t `LM` Representation tt `LM` Representation ttt
	Representation (U_I_I LM) = () `ML` ()

class
	 ( Transformation v x from into t (v hom (Representation t))
	 , Transformation v x from into (v hom (Representation t)) t
	 ) => Representable hom v x from into t

deriving instance
	( Transformation v x from into t (v hom (Representation t))
	, Transformation v x from into (v hom (Representation t)) t
	) => Representable hom v x from into t

rep :: forall into hom t i .
	Category (->) =>
	Covariant Endo Semi Functor (->) (Straight hom (Representation t)) =>
	Covariant (Representable hom) Functor into into t =>
	Component Natural (->) (->)
		(T_TT_I (Straight into (t i)) (Straight hom (Representation t)))
		(TT_T_I (Straight into (t i)) (Straight hom (Representation t))) =>
	Castable Straight into (Straight hom (Representation t) i) =>
	hom (Representation t) (into (t i) i)
rep = unwrap `compose` map @Straight @Straight @_ @(->) @(Straight hom (Representation t)) @(Straight hom (Representation t)) unwrap / wrapped
	(component @Straight @(->) @(->)
		@(T_TT_I (Straight into _) (Straight hom (Representation t)))
		@(TT_T_I (Straight into _) (Straight hom (Representation t))))
	(wrap @(->) @(U_I_II into _ _) / component @Straight @into @into @t @(Straight hom (Representation t)))

type family Co x where Co (x Straight) = x Opposite

type family Object diagram = r | r -> diagram where
	Object (Both (Straight Arrow)) = LM
	Object (Both (Opposite Arrow)) = ML

type family Neutral p where
	Neutral LM = ()
	Neutral ML = Void

class
	( forall e . Mapping v v from into (This u e) I
	, forall e . Mapping v v from into (That u e) I
	) => Cone v from into u

deriving instance
	( forall e . Mapping v v from into (This u e) I
	, forall e . Mapping v v from into (That u e) I
	) => Cone v from into u

left :: forall v from into a o e .
	Cone v from into (Object (Both (v into))) =>
	Castable Opposite Arrow (v from a o) =>
	Castable Straight Arrow (v into (This (Object (Both (v into))) e a) (I o)) =>
	Supertype (v from a o) -> Supertype (v into (This (Object (Both (v into))) e a) (I o))
left from = map @v @v @from @into @(This (Object (Both (v into))) e) @I @a @o from

right :: forall v from into a t e .
	Cone v from into (Object (Both (v into))) =>
	Castable Opposite Arrow (v from a t) =>
	Castable Straight Arrow (v into (That (Object (Both (v into))) e a) (I t)) =>
	Supertype (v from a t) -> Supertype (v into (That (Object (Both (v into))) e a) (I t))
right from = map @v @v @from @into @(That (Object (Both (v into))) e) @I @a @t from

type Limit v from into =
	( Cone v from into (Object (Both (v into)))
	, Mapping v v from into I (Both (Object (Both (v into))))
	)

type Product into = Object (Both (Straight into))

type Sum into = Object (Both (Opposite into))

type Terminal o into a = o Straight into U_ a a

type Initial o into a = o Opposite into U_ a a

-- TODO: generalize via colimits
absurd :: Void -> a
absurd x = case x of {}

type Day = U_V_UU_UUU_UUUU_T_TT_I_II_III LM

class 
	( x Straight into from t
	, x Straight from into tt
	, Transformation Straight x into from (T_TT_I t tt) I
	, Transformation Straight x from into I (T_TT_I tt t)
	) => Adjoint x from into t tt

deriving instance
	( x Straight into from t
	, x Straight from into tt
	, Transformation Straight x into from (T_TT_I t tt) I
	, Transformation Straight x from into I (T_TT_I tt t)
	) => Adjoint x from into t tt

class
	( forall e ee . Mapping v Straight from Arrow (Day v from u uu t t e ee) t
	, Mapping v Straight from Arrow (v Arrow (Neutral uu)) t
	, x v from Arrow t
	) => Monoidal v x from u uu t where

deriving instance
	( forall e ee . Mapping v Straight from Arrow (Day v from u uu t t e ee) t
	, Mapping v Straight from Arrow (v Arrow (Neutral uu)) t
	, x v from Arrow t
	) => Monoidal v x from u uu t

day :: forall v from t u uu a o e ee .
	Mapping v Straight from (->) (Day v from u uu t t e ee) t =>
	Castable Opposite Arrow (v from a o) =>
	Castable Opposite Arrow (v from (uu e ee) a) =>
	Supertype (v from a o)
		-> Supertype (v from (uu e ee) a)
		-> u (t e) (t ee) -> t o
day from t x = map @v @Straight @from @(->)
	@(Day v from u uu t t e ee) @t from
	(U_V_UU_UUU_UUUU_T_TT_I_II_III (These x (wrap @Arrow @(v from (uu e ee) a) t)))

monoidal_ :: forall v from into t u uu a o e ee .
	Adjoint Functor (->) into
		(That LM (u (t e) (t ee)))
		(That into (u (t e) (t ee))) =>
	Monoidal v Functor from u uu t =>
	Castable Opposite Arrow (v from a o) =>
	Castable Opposite into ((That into (u (t e) (t ee)) `T_TT_I` That LM (u (t e) (t ee))) a) =>
	Castable Straight into ((That into (u (t e) (t ee)) `T_TT_I` That LM (u (t e) (t ee))) (v from (uu e ee) a)) =>
	Castable Straight into (That into (u (t e) (t ee)) (t o)) =>
	Castable Opposite into (I (v from (uu e ee) a)) =>
	Supertype (v from a o) -> into (v from (uu e ee) a) (into (u (t e) (t ee)) (t o))
monoidal_ from =
	rw @into @(That into _ _)
	`compose` map @Straight @Straight @(->) @into
		@(That into (u (t e) (t ee))) @(That into (u (t e) (t ee)))
		((map @v @Straight @from @(->) @(Day v from u uu t t e ee) @t from `compose` wrap)
		`compose` rw @(->) @(That LM _ _))
	`compose` rw @into @(T_TT_I _ _ _)
	`compose` component @Straight @(->) @into @I @(That into _ `T_TT_I` That LM _)
	`compose` wrap @into

-- TODO: generalize
empty :: forall t . Monoidal Straight Functor (->) LM ML t => t Void
empty = component @Straight @(->) @(->) @(Straight (->) Void) @t (U_I_II identity)

-- TODO: generalize so I can use Attribute here
enter :: forall t . Monoidal Straight Functor (->) LM LM t => t ()
enter = component @Straight @(->) @(->) @(Straight (->) ()) @t (U_I_II identity)

rwr :: forall o into a .
	Precategory into =>
	Castable Opposite into o => 
	Castable Straight into a =>
	into (Supertype a) (Supertype o) -> into a o
rwr f = wrap `compose` f `compose` rw

rewrap :: forall o a .
	Precategory (->) =>
	Castable Opposite (->) o => 
	Castable Straight (->) a =>
	(Supertype a -> Supertype o) -> a -> o
rewrap f = wrap `compose` f `compose` rw

wrapped :: forall into a o .
	Precategory into =>
	Castable Straight into o =>
	Castable Opposite into a =>
	into a o -> into (Supertype a) (Supertype o)
wrapped f = rw `compose` f `compose` wrap

i_ :: forall into u a o e .
	Precategory into =>
	Castable Opposite into (U_II_I u e a) =>
	Castable Straight into (U_II_I u e o) =>
	into (U_II_I u e a) (U_II_I u e o) -> into (u a e) (u o e)
i_ f = rw @into @(U_II_I _ _ _) `compose` f `compose` wrap @into @(U_II_I _ _ _)

_i :: forall into u a o e .
	Precategory into =>
	Castable Opposite into (U_I_II u e a) =>
	Castable Straight into (U_I_II u e o) =>
	into (U_I_II u e a) (U_I_II u e o) -> into (u e a) (u e o)
_i f = rw @into @(U_I_II _ _ _) `compose` f `compose` wrap @into @(U_I_II _ _ _)

cata :: forall into t e .
	Covariant Endo Semi Functor into t =>
	Castable Straight into (Recursive t) =>
	into (t e) e -> into (Recursive t) e
cata into = into `compose`
	map @Straight @Straight (cata into) `compose`
	(let U_I_II x = cast in x)

ana :: forall into t e .
	Covariant Endo Semi Functor into t =>
	Castable Opposite into (Recursive t) =>
	into e (t e) -> into e (Recursive t)
ana into = wrap `compose` map @Straight @Straight (ana into) `compose` into
