{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE UndecidableSuperClasses #-}
module Ya.Algebra.Definition where

import Ya.Algebra.Abstract

infixr 8 /\, \/

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
	( Mapping v from into f g
	, x v from into f
	, x v from into g
	) => Transformation v x from into f g

deriving instance
	( Mapping v from into f g
	, x v from into f
	, x v from into g
	) => Transformation v x from into f g

type Natural = Flat

type Dinatural = Dual

type Covariant f = f Flat

type Contravariant f = f Dual

type Kleisli u t = U_I_T_II t u

class (forall t . Transformation v x Arrow Arrow f (UU_V_U_I_II_T_II v from into f t)) =>
	Yoneda v x from into f where
	yoneda :: forall s t .
		Category Arrow =>
		Precategory into =>
		(Supertype (v Arrow s s) ~ Arrow s s) =>
		Castable Dual into (v from s t) =>
		Castable Dual Arrow (v Arrow s s) =>
		f s -> into (Supertype (v from s t)) (f t)
	yoneda x = unwrap
		(map @v @Arrow @Arrow @f @(UU_V_U_I_II_T_II v from into f t) identity x)
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

class Ordered v (vv :: (* -> * -> *) -> * -> * -> *) from into t tt

deriving instance Mapping vv from into t tt
	=> Ordered Flat vv from into t tt

deriving instance Mapping vv from into tt t
	=> Ordered Dual vv from into t tt

class
	( Ordered v Flat from into I (diagram (Object v into diagram))
	, forall e . Ordered v Flat from into (U_I_II (Object v into diagram) e) I
	, forall e . Ordered v Flat from into (U_II_I (Object v into diagram) e) I
	) => Factor v from into diagram where
	data Object v into diagram i ii
	factor :: Supertype (v from any i) -> Supertype (v from any ii)
		-> Supertype (v into any (Object v into diagram i ii))

type Limit = Factor Flat

type Product o into = o Flat into U_I_I

type (/\) = Product Object Arrow

project :: forall p from into e s t .
	Limit from into U_I_I =>
	Transformation Natural Functor from into (p (Product Object into) e) I =>
	Castable Dual into (p (Product Object into) e s) =>
	Castable Flat into (I t) =>
	from s t -> into (Supertype (p (Product Object into) e s)) t
project from = wrapped @into (map @Flat @from @into @(p (Product Object into) e) @I from)

(/\) :: Limit from into U_I_I =>
	Supertype (Flat from any i) ->
	Supertype (Flat from any ii) ->
	Supertype (Flat into any (Object Flat into U_I_I i ii))
(/\) = factor @Flat

type Sum o into = o Dual into U_I_I

type (\/) = Sum Object Arrow

inject :: forall p from into e s t .
	Co Limit into into U_I_I =>
	Transformation Natural Functor from into I (p (Sum Object into) e) =>
	Castable Flat into (p (Sum Object into) e t) =>
	Castable Dual into (I s) =>
	from s t -> into s (Supertype (p (Sum Object into) e t))
inject from = wrapped @into (map @Flat @from @into @I @(p (Sum Object into) e) from)

(\/) :: Co Limit from into U_I_I =>
	Supertype (Dual from any i) ->
	Supertype (Dual from any ii) ->
	Supertype (Dual into any (Object Dual into U_I_I i ii))
(\/) = factor @Dual

type Terminal o into i = o Flat into U_ i i

type Initial o into i = o Dual into U_ i i

instance Mapping Flat Arrow Arrow I (U_I_I (/\))
	where mapping (U_I_II from) (I x) = U_I_I (These (from x) (from x))

instance Mapping Flat Arrow Arrow (U_I_II (/\) e) I
	where mapping (U_I_II from) (U_I_II (These e x)) = I (from x)

instance Mapping Flat Arrow Arrow (U_II_I (/\) e) I
	where mapping (U_I_II from) (U_II_I (These x e)) = I (from x)

instance Factor Flat Arrow Arrow U_I_I where
	data Object Flat Arrow U_I_I i ii = These i ii
	factor this that x = These (this x) (that x)

instance Mapping Flat Arrow Arrow (U_I_I (\/)) I
	where mapping (U_I_II from) = \case
		U_I_I (This x) -> I (from x)
		U_I_I (That x) -> I (from x)

instance Mapping Flat Arrow Arrow I (U_I_II (\/) e)
	where mapping (U_I_II from) (I x) = U_I_II (That (from x))

instance Mapping Flat Arrow Arrow I (U_II_I (\/) e)
	where mapping (U_I_II from) (I x) = U_II_I (This (from x))

instance Factor Dual Arrow Arrow U_I_I where
	data Object Dual Arrow U_I_I i ii = This i | That ii
	factor this that x = case x of
		This i -> this i
		That ii -> that ii

-- instance Factor Flat Arrow U_ where
	-- data Object Flat Arrow U_ i ii = Unit'
	-- factor _ _ _ = Unit'

-- instance Factor Dual Arrow U_ where
	-- data Object Dual Arrow U_ i ii

-- TODO: generalize via colimits
absurd :: Void -> i
absurd x = case x of {}

type family Neutral p where
	Neutral (/\) = Unit
	Neutral (\/) = Void

type family Co x where
	Co (x Flat) = x Dual

type Day = U_V_UU_UUU_UUUU_T_TT_I_II_III (/\)

class 
	( x Flat into from f
	, x Flat from into g
	, Transformation Flat x into from (T_TT_I f g) I
	, Transformation Flat x from into I (T_TT_I g f)
	) => Adjoint x from into f g

deriving instance
	( x Flat into from f
	, x Flat from into g
	, Transformation Flat x into from (T_TT_I f g) I
	, Transformation Flat x from into I (T_TT_I g f)
	) => Adjoint x from into f g

class
	( forall i ii . Mapping v from Arrow (Day v from u uu f f i ii) f
	, Mapping v from Arrow (v Arrow (Neutral uu)) f
	, x v from Arrow f
	) => Monoidal v x from u uu f where

deriving instance
	( forall i ii . Mapping v from Arrow (Day v from u uu f f i ii) f
	, Mapping v from Arrow (v Arrow (Neutral uu)) f
	, x v from Arrow f
	) => Monoidal v x from u uu f

monoidal :: forall v from f u uu s t i ii .
	Monoidal v Functor from u uu f =>
	Castable Dual Arrow (v from s t) =>
	Castable Dual Arrow (v from (uu i ii) s) =>
	Supertype (v from s t)
		-> Supertype (v from (uu i ii) s)
		-> u (f i) (f ii) -> f t
monoidal from f x = map @v @from @(->)
	@(Day v from u uu f f i ii) @f from
	(U_V_UU_UUU_UUUU_T_TT_I_II_III (These x (wrap @Arrow @(v from (uu i ii) s) f)))

-- TODO: generalize
point :: forall f t .
	Monoidal Flat Functor Arrow (/\) (/\) f =>
	t -> f t
point x = component @Flat @Arrow @(->) @(Flat (->) Unit) @f (U_I_II (\_ -> x))

-- TODO: generalize
empty :: forall f t .
	Monoidal Flat Functor Arrow (/\) (\/) f =>
	f t
empty = component @Flat @Arrow @(->) @(Flat (->) Void) @f (U_I_II absurd)

rewrap :: forall into i ii .
	Precategory into =>
	Castable Dual into ii => 
	Castable Flat into i =>
	into (Supertype i) (Supertype ii) -> into i ii
rewrap f = wrap `compose` f `compose` unwrap

wrapped :: forall into i ii .
	Precategory into =>
	Castable Flat into ii =>
	Castable Dual into i =>
	into i ii -> into (Supertype i) (Supertype ii)
wrapped f = unwrap `compose` f `compose` wrap
