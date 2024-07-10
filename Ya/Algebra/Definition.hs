{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE UndecidableSuperClasses #-}
module Ya.Algebra.Definition where

import Ya.Algebra.Abstract

infixl 8 `TI`, `LM`, `ML`, `JT`
infixl 7 `TII`

infixr 7 `ARR`
infixr 6 `ARRR`
infixr 5 `ARRRR`
infixr 4 `ARRRRR`
infixr 3 `ARRRRRR`
infixr 2 `ARRRRRRR`
infixr 1 `ARRRRRRRR`

infixl 9 `e`
infixl 8 `wr`
infixl 0 /

type ARR = (->)
type ARRR = (->)
type ARRRR = (->)
type ARRRRR = (->)
type ARRRRRR = (->)
type ARRRRRRR = (->)
type ARRRRRRRR = (->)

type TI t i = t i

type TII t i = t i

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
map from = unwrap @Arrow (mapping @v @vv @from @into @t @tt @a @o (wrap from))

type Component v = Transformation v Functor

component :: forall v from into t tt o .
	Component v from into t tt =>
	(Supertype (v from o o) ~ from o o) =>
	Castable Opposite Arrow (v from o o) =>
	into (t o) (tt o)
component = unwrap @Arrow (mapping @v @Straight @from @into @t @tt @_ @o (wrap identity))

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

class (Category from, forall r . Mapping v Straight from Arrow t (UU_V_U_I_II_T_II v from into t r)) =>
	Yoneda v from into t where
	yoneda :: forall a r .
		Category from =>
		Precategory into =>
		(Supertype (v from a a) ~ from a a) =>
		Castable Opposite Arrow (v from a a) =>
		Castable Opposite into (v from a r) =>
		t a -> into (Supertype (v from a r)) (t r)
	yoneda x = unwrap
		(map @v @Straight @from @Arrow @t @(UU_V_U_I_II_T_II v from into t r) identity x)
		`compose` wr @into @(v from a r)

deriving instance
	(Category from, forall r . Mapping v Straight from Arrow t (UU_V_U_I_II_T_II v from into t r)) =>
	Yoneda v from into t

type family Representation t where
	Representation Identity = ()
	Representation (U_I_II Arrow a) = a
	Representation (T_TT_I t tt) =
		Representation t `LM` Representation tt
	Representation (T_TTT_TT_I t ttt tt) =
		Representation t `LM` Representation tt `LM` Representation ttt
	Representation (U_I_I LM) = () `ML` ()

class
	 ( Mapping v Straight from into t (v hom (Representation t))
	 , Mapping v Straight from into (v hom (Representation t)) t
	 ) => Representable hom v from into t

deriving instance
	( Mapping v Straight from into t (v hom (Representation t))
	, Mapping v Straight from into (v hom (Representation t)) t
	) => Representable hom v from into t

type family Co x where Co (x Straight) = x Opposite

data family Object (v :: (* -> * -> *) -> * -> * -> *) (diagram :: * -> * -> *) e ee
data instance Object Straight Arrow e ee = These e ee
data instance Object Opposite Arrow e ee = This e | That ee

type LM = Object Straight Arrow
type ML = Object Opposite Arrow

type family Neutral p where
	Neutral LM = ()
	Neutral ML = Void

class
	( forall e . Mapping v v from into (This u e) Identity
	, forall e . Mapping v v from into (That u e) Identity
	) => Cone v from into u

deriving instance
	( forall e . Mapping v v from into (This u e) Identity
	, forall e . Mapping v v from into (That u e) Identity
	) => Cone v from into u

left :: forall v from into a o e .
	Cone v from into (Object v into) =>
	Castable Opposite Arrow (v from a o) =>
	Castable Straight Arrow (v into ((This (Object v into)) e a) (Identity o)) =>
	Supertype (v from a o) -> Supertype (v into (This (Object v into) e a) (Identity o))
left from = map @v @v @from @into @(This (Object v into) e) @Identity @a @o from

right :: forall v from into a t e .
	Cone v from into (Object v into) =>
	Castable Opposite Arrow (v from a t) =>
	Castable Straight Arrow (v into (That (Object v into) e a) (Identity t)) =>
	Supertype (v from a t) -> Supertype (v into (That (Object v into) e a) (Identity t))
right from = map @v @v @from @into @(That (Object v into) e) @Identity @a @t from

type Limit v from into =
	( Cone v from into (Object v into)
	, Mapping v v from into Identity (Both (Object v into))
	)

type Product into = Object Straight into

type Sum into = Object Opposite into

type Terminal o into a = o Straight into U_ a a

type Initial o into a = o Opposite into U_ a a

-- TODO: generalize via colimits
absurd :: Void -> a
absurd x = case x of {}

type Day = U_V_UU_UUU_UUUU_T_TT_I_II_III LM

class 
	( x Straight into from t
	, x Straight from into tt
	, Transformation Straight x into from (T_TT_I t tt) Identity
	, Transformation Straight x from into Identity (T_TT_I tt t)
	) => Adjoint x from into t tt

deriving instance
	( x Straight into from t
	, x Straight from into tt
	, Transformation Straight x into from (T_TT_I t tt) Identity
	, Transformation Straight x from into Identity (T_TT_I tt t)
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
	(U_V_UU_UUU_UUUU_T_TT_I_II_III (These x (wrap @(v from (uu e ee) a) t)))

monoidal_ :: forall v from into t u uu a o e ee .
	Adjoint Functor (->) into
		(That LM (u (t e) (t ee)))
		(That into (u (t e) (t ee))) =>
	Monoidal v Functor from u uu t =>
	Castable Opposite Arrow (v from a o) =>
	Castable Opposite into ((That into (u (t e) (t ee)) `T_TT_I` That LM (u (t e) (t ee))) a) =>
	Castable Straight into ((That into (u (t e) (t ee)) `T_TT_I` That LM (u (t e) (t ee))) (v from (uu e ee) a)) =>
	Castable Straight into (That into (u (t e) (t ee)) (t o)) =>
	Castable Opposite into (Identity (v from (uu e ee) a)) =>
	Supertype (v from a o) -> into (v from (uu e ee) a) (into (u (t e) (t ee)) (t o))
monoidal_ from =
	unwrap @into @(That into _ _)
	`compose` map @Straight @Straight @(->) @into
		@(That into (u (t e) (t ee))) @(That into (u (t e) (t ee)))
		((map @v @Straight @from @(->) @(Day v from u uu t t e ee) @t from `compose` wrap)
		`compose` unwrap @(->) @(That LM _ _))
	`compose` unwrap @into @(T_TT_I _ _ _)
	`compose` component @Straight @(->) @into @Identity @(That into _ `T_TT_I` That LM _)
	`compose` wr @into

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
rwr f = wr `compose` f `compose` unwrap

rewrap :: forall o a .
	Precategory (->) =>
	Castable Opposite (->) o => 
	Castable Straight (->) a =>
	(Supertype a -> Supertype o) -> a -> o
rewrap f = wr `compose` f `compose` unwrap

wrapped :: forall into a o .
	Precategory into =>
	Castable Straight into o =>
	Castable Opposite into a =>
	into a o -> into (Supertype a) (Supertype o)
wrapped f = unwrap `compose` f `compose` wr

i_ :: forall into u a o e .
	Precategory into =>
	Castable Opposite into (U_II_I u e a) =>
	Castable Straight into (U_II_I u e o) =>
	into (U_II_I u e a) (U_II_I u e o) -> into (u a e) (u o e)
i_ f = unwrap @into @(U_II_I _ _ _) `compose` f `compose` wr @into @(U_II_I _ _ _)

_i :: forall into u a o e .
	Precategory into =>
	Castable Opposite into (U_I_II u e a) =>
	Castable Straight into (U_I_II u e o) =>
	into (U_I_II u e a) (U_I_II u e o) -> into (u e a) (u e o)
_i f = unwrap @into @(U_I_II _ _ _) `compose` f `compose` wr @into @(U_I_II _ _ _)

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
ana into = wr `compose` map @Straight @Straight (ana into) `compose` into

type family Unlabeled t where
	Unlabeled (Labeled label t) = t
	Unlabeled t = t

class Unlabelable into t where
	unlabel :: into (t e) (Unlabeled t e)

instance {-# OVERLAPPABLE #-} (Category into, Unlabeled t ~ t)
	=> Unlabelable into t where unlabel = identity

instance {-# OVERLAPS #-} (forall e . Wrapper into (Labeled label t e))
	=> Unlabelable into (Labeled label t) where unlabel = unwrap

type family JT effect where
 JT (U_I_II (->) e) = T_TT_I (U_I_II (->) e)
 JT (U_I_II (W_I_I_II (U_I_UU_II_III (->) LM)) e) = T_TTT_TT_I (U_I_II (->) e) (U_I_II LM e)

-- type family Unjointed effect unknown e where
-- 	Unjointed (U_I_II (W_I_I_II (U_I_UU_II_III (->) LM)) state) unknown e =
-- 		state -> unknown (state `LM` e)

class Unjointable effect unknown where
 tnj :: effect `JT` unknown `TI` result `ARR` effect `TI` unknown result

instance Unjointable (U_I_II (W_I_I_II (U_I_UU_II_III (->) LM)) e) (U_I_II ML ee) where
 tnj (T_TTT_TT_I (U_I_II f)) = U_I_II (W_I_I_II
  (U_I_UU_II_III (\e -> case unwrap (f e) of { This x -> These e (U_I_II (This x)); That (U_I_II (These y x)) -> These y (U_I_II (That x))})))

this :: e `LM` ee -> e
this (These x _) = x

that :: e `LM` ee -> ee
that (These _ x) = x

constant :: e -> ee -> e
constant x _ = x

but :: e -> ee -> e
but x _ = x

type MLM = U_U_I_II_UU_I_II ML LM

instance Wrapper (->) x
	=> Castable Straight (W_I_II_II (U_I_UU_III_U_II_I (->) LM)) x where
	cast = U_I_II (W_I_II_II (U_I_UU_III_U_II_I (\x -> These (unwrap x) wrap)))

instance Wrapper (->) x
	=> Castable Opposite (W_I_II_II (U_I_UU_III_U_II_I (->) LM)) x where
	cast = U_II_I (W_I_II_II (U_I_UU_III_U_II_I (\x -> These (wrap x) unwrap)))

class Setoid e where
	e :: e `ARR` e `ARR` e `LM` e `ML` e

(/) :: (i -> o) -> i -> o
(/) f x = f x

wr :: Castable Opposite into i => into (Supertype i) i
wr = let U_II_I x = cast in x
