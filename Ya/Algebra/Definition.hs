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

type Component v = Transformation v Functor

component :: forall v from into f g t .
	Component v from into f g =>
	(Supertype (v from t t) ~ from t t) =>
	Castable Dual Arrow (v from t t) =>
	into (f t) (g t)
component = mapping @Flat @from @into @f @g @_ @t (wrap @Arrow identity)

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
	( Mapping Flat from into f g
	, x v from into f
	, x v from into g
	) => Transformation v x from into f g

deriving instance
	( Mapping Flat from into f g
	, x v from into f
	, x v from into g
	) => Transformation v x from into f g

type Natural = Flat

type Dinatural = Dual

type Covariant f = f Flat

type Contravariant f = f Dual

type Kleisli = U_I_T_II

class (forall t . Transformation v x Arrow Arrow f (UU_V_U_I_II_T_II v from into f t)) =>
	Yoneda v x from into f where
	yoneda :: forall s t .
		Category Arrow =>
		Precategory into =>
		(Supertype (v Arrow s s) ~ Arrow s s) =>
		Castable Dual into (v from s t) =>
		f s -> into (Supertype (v from s t)) (f t)
	yoneda x = unwrap
		(map @Flat @Arrow @Arrow @f @(UU_V_U_I_II_T_II v from into f t) identity x)
		`compose` wrap @into @(v from s t)

deriving instance
	(forall t . Transformation v x Arrow Arrow f
		(UU_V_U_I_II_T_II v from into f t)) =>
	Yoneda v x from into f 

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
	, Transformation v x into from (T_TT_I f g) I
	, Transformation v x from into I (T_TT_I g f)
	) => Adjoint v x from into f g

deriving instance
	( x v into from f
	, x v from into g
	, Transformation v x into from (T_TT_I f g) I
	, Transformation v x from into I (T_TT_I g f)
	) => Adjoint v x from into f g

class
	( Mapping v from Arrow (Day v from u uu f f i ii) f
	, Mapping v from Arrow (v from (Neutral u)) f
	, x v from Arrow f
	) => Monoidal v x from u uu i ii f where

deriving instance
	( Mapping v from Arrow (Day v from p pp f f i ii) f
	, Mapping v from Arrow (v from (Neutral p)) f
	, x v from Arrow f
	) => Monoidal v x from p pp i ii f

monoidal :: forall v from f u uu s t i ii .
	Monoidal v Functor from u uu i ii f =>
	Castable Dual Arrow (v from s t) =>
	Castable Dual Arrow (v from (uu i ii) s) =>
	Supertype (v from s t)
		-> Supertype (v from (uu i ii) s)
		-> u (f i) (f ii) -> f t
monoidal from f x = map @v @from @(->)
	@(Day v from u uu f f i ii) @f from
	(U_V_UU_UUU_UUUU_T_TT_I_II_III (These x (wrap @Arrow @(v from (uu i ii) s) f)))

rewrap :: forall into i ii .
	Precategory into =>
	Castable Dual into ii => 
	Castable Flat into i =>
	into (Supertype i) (Supertype ii) -> into i ii
rewrap f = wrap `compose` f `compose` unwrap
