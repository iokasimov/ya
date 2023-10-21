{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE UndecidableSuperClasses #-}
module Ya.Algebra.Definition where

import Ya.Algebra.Abstract

infixr 8 /\, \/

class Dumb x
instance Dumb x

class Mapping v vv from into f g where
	mapping :: v from s t -> vv into (f s) (g t)

instance Mapping Flat Flat from into t tt => Mapping Dual Dual from into tt t
	where mapping (U_II_I from) = U_II_I (map @Flat @Flat @from @into @t @tt from)

instance Mapping Dual Flat from into t tt => Mapping Flat Dual from into tt t
	where mapping (U_I_II from) = U_II_I (map @Dual @Flat @from @into @t @tt from)

map :: forall v vv from into f g s t .
	Mapping v vv from into f g =>
	Castable Dual Arrow (v from s t) =>
	Castable Flat Arrow (vv into (f s) (g t)) =>
	Supertype (v from s t) -> Supertype (vv into (f s) (g t))
map from = unwrap @Arrow (mapping @v @vv @from @into @f @g @s @t (wrap @Arrow from))

type Component v = Transformation v Functor

component :: forall v from into f g t .
	Component v from into f g =>
	(Supertype (v from t t) ~ from t t) =>
	Castable Dual Arrow (v from t t) =>
	into (f t) (g t)
component = unwrap @Arrow (mapping @v @Flat @from @into @f @g @_ @t (wrap @Arrow identity))

{- [LAW] Associativity: compose f (compose g) ≡ compose (compose f g) -}
class
	( forall i . Mapping Flat Flat from Arrow (U_I_II from i) (U_I_II from i)
	, forall i . Mapping Dual Flat from Arrow (U_II_I from i) (U_II_I from i)
	) => Precategory from where
	compose :: from s t -> from i s -> from i t
	compose post pre = let U_I_II y = map @Flat @Flat post (U_I_II pre) in y

deriving instance
	( forall i . Mapping Flat Flat from Arrow (U_I_II from i) (U_I_II from i)
	, forall i . Mapping Dual Flat from Arrow (U_II_I from i) (U_II_I from i)
	) => Precategory from

{- [LAW] Left identity: identity . f ≡ f -}
{- [LAW] Right identity: f . identity ≡ f -}
class Precategory from => Category from
	where identity :: from s s

{- [LAW] Identity preserving: mapping identity ≡ identity -}
{- [LAW] Composition preserving: mapping (f . g) ≡ mapping f . mapping g -}
class (Category from, Category into, Mapping v Flat from into f f) => Functor v from into f
deriving instance (Category from, Category into, Mapping v Flat from into f f) => Functor v from into f

functor :: forall v from into f s t .
	Functor v from into f =>
	Castable Dual Arrow (v from s t) =>
	Supertype (v from s t) -> into (f s) (f t)
functor = map @v @Flat @from @into @f @f @s @t

{- [LAW] Composition preserving: mapping (f . g) ≡ mapping f . mapping g -}

class
	( Precategory from, Precategory into
	, Mapping v Flat from into f f
	, Dumb (x v from into f)
	) => Semi v x from into f

deriving instance
	( Precategory from, Precategory into
	, Mapping v Flat from into f f
	, Dumb (Functor v from into f)
	) => Semi v Functor from into f

semifunctor :: forall v from into f s t .
	Semi v Functor from into f =>
	Castable Dual Arrow (v from s t) =>
	Supertype (v from s t) -> into (f s) (f t)
semifunctor = map @v @Flat @from @into @f @f @s @t

type Endo v x c into = x v c into into

{- LAW: mapping @g @g morphism . component @f @g = component @f @g . mapping morphism @f @f -}
{- LAW: mapping @g @g morphism . component @f @g = component @f @g . mapping morphism @f @f -}
class
	( Mapping v Flat from into f g
	, x v from into f
	, x v from into g
	) => Transformation v x from into f g

deriving instance
	( Mapping v Flat from into f g
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
		(map @v @Flat @Arrow @Arrow @f @(UU_V_U_I_II_T_II v from into f t) identity x)
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

type family Co x where Co (x Flat) = x Dual

type family Object diagram = r | r -> diagram where
	Object (U_I_I (Flat Arrow)) = (/\)
	Object (U_I_I (Dual Arrow)) = (\/)

type family Neutral p where
	Neutral (/\) = Unit
	Neutral (\/) = Void

class
	( forall e . Mapping v v from into (Flat u e) I
	, forall e . Mapping v v from into (Dual u e) I
	) => Cone v from into u

deriving instance
	( forall e . Mapping v v from into (Flat u e) I
	, forall e . Mapping v v from into (Dual u e) I
	) => Cone v from into u

this :: forall v from into s t e .
	Cone v from into (Object (U_I_I (v into))) =>
	Castable Dual Arrow (v from s t) =>
	Castable Flat Arrow (v into (This (Object (U_I_I (v into))) e s) (I t)) =>
	Supertype (v from s t) -> Supertype (v into (This (Object (U_I_I (v into))) e s) (I t))
this from = map @v @v @from @into @(This (Object (U_I_I (v into))) e) @I @s @t from

that :: forall v from into s t e .
	Cone v from into (Object (U_I_I (v into))) =>
	Castable Dual Arrow (v from s t) =>
	Castable Flat Arrow (v into (That (Object (U_I_I (v into))) e s) (I t)) =>
	Supertype (v from s t) -> Supertype (v into (That (Object (U_I_I (v into))) e s) (I t))
that from = map @v @v @from @into @(That (Object (U_I_I (v into))) e) @I @s @t from

project :: forall p from into e s t .
	Precategory into =>
	Limit from into U_I_I =>
	Mapping Flat Flat from into (p (Object (U_I_I (Flat into))) e) I =>
	Castable Dual into (p (Object (U_I_I (Flat into))) e s) =>
	Castable Flat into (I t) =>
	from s t -> into (Supertype (p (Object (U_I_I (Flat into))) e s)) t
project from = wrapped @into / map @Flat @Flat @from @into @(p (Object (U_I_I (Flat into))) e) @I from

class Mapping v v from into I (diagram (Object (diagram (v into)))) =>
	Factor v from into diagram where
	factor ::
		Supertype (v from any i) ->
		Supertype (v from any ii) ->
		Supertype (v into any (Object (diagram (v into)) i ii))

type Limit = Factor Flat

type Product o = o Flat U_I_I

inject :: forall p from into e s t .
	Precategory into =>
	Co Limit into into U_I_I =>
	Mapping Flat Flat from into I (p (Object (U_I_I (Dual into))) e) =>
	Castable Flat into (p (Object (U_I_I (Dual into))) e t) =>
	Castable Dual into (I s) =>
	from s t -> into s (Supertype (p (Object (U_I_I (Dual into))) e t))
inject from = wrapped @into / map @Flat @Flat @from @into @I @(p (Object (U_I_I (Dual into))) e) from

(/\) :: forall from into any i ii .
	Limit from into U_I_I =>
	Supertype (Flat from any i) ->
	Supertype (Flat from any ii) ->
	Supertype (Flat into any (Object (U_I_I (Flat into)) i ii))
(/\) = factor @Flat @from @into @U_I_I

(\/) :: forall from into any i ii .
	Co Limit from into U_I_I =>
	Supertype (Dual from any i) ->
	Supertype (Dual from any ii) ->
	Supertype (Dual into any (Object (U_I_I (Dual into)) i ii))
(\/) = factor @Dual @from @into @U_I_I @any @i @ii

type Sum o into = o Dual U_I_I into

type Terminal o into i = o Flat into U_ i i

type Initial o into i = o Dual into U_ i i

instance Mapping Flat Flat Arrow Arrow I (U_I_I (/\))
	where mapping (U_I_II from) = U_I_II / \(I x) -> U_I_I (These (from x) (from x))

instance Mapping Flat Flat Arrow Arrow (U_I_II (/\) e) I
	where mapping (U_I_II from) = U_I_II / \(U_I_II (These _ x)) -> I (from x)

instance Mapping Flat Flat Arrow Arrow (U_II_I (/\) e) I
	where mapping (U_I_II from) = U_I_II / \(U_II_I (These x _)) -> I (from x)

instance Factor Flat Arrow Arrow U_I_I where
	factor this that x = These (this x) (that x)

instance Mapping Flat Flat Arrow Arrow (U_I_I (\/)) I
	where mapping (U_I_II from) = U_I_II / \case
		U_I_I (This x) -> I (from x)
		U_I_I (That x) -> I (from x)

instance Mapping Flat Flat Arrow Arrow I (U_I_II (\/) e)
	where mapping (U_I_II from) = U_I_II / \(I x) -> U_I_II (That (from x))

instance Mapping Flat Flat Arrow Arrow I (U_II_I (\/) e)
	where mapping (U_I_II from) = U_I_II / \(I x) -> U_II_I (This (from x))

instance Factor Dual Arrow Arrow U_I_I where
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
	( forall i ii . Mapping v Flat from Arrow (Day v from u uu f f i ii) f
	, Mapping v Flat from Arrow (v Arrow (Neutral uu)) f
	, x v from Arrow f
	) => Monoidal v x from u uu f where

deriving instance
	( forall i ii . Mapping v Flat from Arrow (Day v from u uu f f i ii) f
	, Mapping v Flat from Arrow (v Arrow (Neutral uu)) f
	, x v from Arrow f
	) => Monoidal v x from u uu f

monoidal :: forall v from f u uu s t i ii .
	Monoidal v Functor from u uu f =>
	Castable Dual Arrow (v from s t) =>
	Castable Dual Arrow (v from (uu i ii) s) =>
	Supertype (v from s t)
		-> Supertype (v from (uu i ii) s)
		-> u (f i) (f ii) -> f t
monoidal from f x = map @v @Flat @from @(->)
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

i_ :: forall into u s t e .
	Precategory into =>
	Castable Dual into (U_II_I u e s) =>
	Castable Flat into (U_II_I u e t) =>
	into (U_II_I u e s) (U_II_I u e t) -> into (u s e) (u t e)
i_ f = unwrap @into @(U_II_I _ _ _) `compose` f `compose` wrap @into @(U_II_I _ _ _)

_i :: forall into u s t e .
	Precategory into =>
	Castable Dual into (U_I_II u e s) =>
	Castable Flat into (U_I_II u e t) =>
	into (U_I_II u e s) (U_I_II u e t) -> into (u e s) (u e t)
_i f = unwrap @into @(U_I_II _ _ _) `compose` f `compose` wrap @into @(U_I_II _ _ _)
