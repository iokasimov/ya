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

type Component v = Transformation v Category

type Covariant f = f Flat

type Contravariant f = f Dual

type Kleisli = U_I_T_II

-- TODO: define these instances in another module
instance Mapping Flat Arrow Arrow (U_I_II Arrow s) (U_I_II Arrow s)
	where mapping (U_I_II from) (U_I_II between) = U_I_II (\x -> from (between x))

instance Mapping Dual Arrow Arrow (U_II_I Arrow t) (U_II_I Arrow t)
	where mapping (U_II_I from) (U_II_I between) = U_II_I (\x -> between (from x))

instance Category Arrow where
	identity = \x -> x

class Transformation v m from Arrow
	f (UU_V_U_I_II_T_II v from into f t)
	=> Yoneda m v from into f t where
		yoneda :: forall p s .
			Castable Dual Arrow (v from s p) =>
			Supertype (v from s p) -> f s -> into (v from p t) (f t)
		yoneda from = unwrap `compose` map @v @from @Arrow
			@f @(UU_V_U_I_II_T_II v from into f t) from

deriving instance Transformation v m from Arrow
	f (UU_V_U_I_II_T_II v from into f t)
	=> Yoneda m v from into f t

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

type Day = U_UU_UUU_UUUU_T_TT_I_II_III (/\)

class
	( Mapping v from into (Day (v from) p pp f f i ii) f
	, Mapping v from into (v from (Neutral p)) f
	) => Monoidal x v p pp from into i ii f

deriving instance
	( Mapping v from into (Day (v from) p pp f f i ii) f
	, Mapping v from into (v from (Neutral p)) f
	) => Monoidal Functor v p pp from into i ii f
