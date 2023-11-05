{-# LANGUAGE AllowAmbiguousTypes #-}
module Ya.Algebra.Operators where

import Ya.Algebra.Abstract
import Ya.Algebra.Definition
import Ya.Algebra.Instances ()

infixl 9 `i`, `u`, `o`, `a`
infixl 8 `ii`, `fo`, `fa`, `yi`, `yo`, `ya`, `yu`, `a'a`, `lj`, `rj`, `ro`, `ra`, `pp`, `lm`, `ml`, `w'u`, `u'w`, `u'u`
infixl 7 `iii`, `yi_`, `ya_`, `_fo`, `fo_`, `fa_`
infixl 6 `yi'yi`, `fo'fi`, `fa'fi`, `fokl`, `fo'fo`, `yokl`, `yukl`, `pp'fo`, `yo'o`
infixl 5 `fi_'fi`, `_fo'fi`, `_fo'fo`, `_yokl`
infixl 4 `yi'yi'yi`, `fo'fo'fo`, `yoklKL`
infixl 3 `fi_'fi'fi`, `_fo'fi'fi`
infixl 2 `yi'yi'yi'yi`
infixl 0 `yi'yi'yi'yi'yi`

i, ii, iii :: Category into => into t t
iii = identity
ii = identity
i = identity

yi'yi'yi'yi'yi, yi'yi'yi'yi, yi'yi'yi, yi'yi, yi_, yi
	:: Category into => into t t
yi'yi'yi'yi'yi = identity
yi'yi'yi'yi = identity
yi'yi'yi = identity
yi'yi = identity
yi_ = identity
yi = identity

fi_, fi_'fi, fi_'fi'fi
	:: Category into => into (into s t) (into s t)
fi_ = identity
fi_'fi = identity
fi_'fi'fi = identity

fo, fo'fi :: forall from into f s t .
	Covariant Semi Functor from into f =>
	from s t -> into (f s) (f t)
fo'fi = semifunctor @Straight
fo = semifunctor @Straight

fa, fa'fi :: forall from into f s t .
	Contravariant Semi Functor from into f =>
	from s t -> into (f t) (f s)
fa'fi = semifunctor @Opposite
fa = semifunctor @Opposite

fu, fu'fi :: forall from into f s t .
	Covariant Semi Functor from into f =>
	Mapping U_1_I Straight from into f f =>
	Castable Opposite Arrow (from Unit t) =>
	Supertype (from Unit t) -> into (f s) (f t)
fu'fi = semifunctor @U_1_I @from @into `compose` wrap @Arrow @(from Unit t)
fu = semifunctor @U_1_I @from @into `compose` wrap @Arrow @(from Unit t)

yo :: forall from into f s t .
	Precategory into =>
	Covariant Yoneda Functor from into f =>
	Castable Opposite into (U_I_II from s t) =>
	f s -> into (from s t) (f t)
yo x = yoneda @Straight @Functor x

-- TODO: it's not finished, generalize!
yu :: forall f s t .
	Covariant Yoneda Functor Arrow Arrow f =>
	f s -> t -> f t
yu x r = yoneda @U_I_II @Functor x (\_ -> r)

yo'o :: forall from into f g s t .
	Precategory into =>
	Covariant Functor from from g =>
	Covariant Yoneda Functor from into f =>
	Contravariant Endo Semi Functor Arrow (U_II_I into (f (g t))) =>
	Castable Opposite into (U_I_II from (g s) (g t)) =>
	f (g s) -> into (from s t) (f (g t))
yo'o x = fa_ fo (yo @from @into x)

-- TODO: yo'yo : f (g s) -> into (from s b) (g s -> into (from b t) (f (g t)))

ya :: forall from into f s t .
	Precategory into =>
	Contravariant Yoneda Functor from into f =>
	Castable Opposite into (Opposite from s t) =>
	f s -> into (from t s) (f t)
ya = yoneda @Opposite @Functor

ya_ :: forall from into f e a o .
	Precategory into =>
	Contravariant Yoneda Functor from into (This f e) =>
	Castable Opposite into (Opposite from a o) =>
	Castable Straight into (This f e o) =>
	f a e -> into (from o a) (f o e)
ya_ x = compose unwrap (yoneda @Opposite @Functor @from @into @(This f e) (wrap x))

fokl :: forall from into f g s t .
	Component Natural from into (T_TT_I f g) f =>
	Castable Opposite into (T_TT_I f g t) =>
	from s (g t) -> into (f s) (f t)
fokl from = component @Straight @from @into @(f `T_TT_I` g) @f
	`compose` wrap `compose` fo from

yokl :: forall from into g f s t .
	Component Natural Arrow into (T_TT_I f g) f =>
	Covariant Yoneda Functor from into f =>
	Castable Opposite into (Straight from s (g t)) =>
	Castable Opposite into (T_TT_I f g t) =>
	f s -> into (from s (g t)) (f t)
yokl x = component @Straight @Arrow @into @(T_TT_I f g)
	`compose` wrap @into @(T_TT_I f g _)
	`compose` yoneda @Straight @Functor @from x

yukl :: forall into g f s t .
	Component Natural Arrow into (T_TT_I f g) f =>
	Covariant Yoneda Functor Constant into f =>
	Castable Opposite into (Straight Constant s (g t)) =>
	Castable Opposite into (Constant s (g t)) =>
	Castable Opposite into (T_TT_I f g t) =>
	f s -> into (g t) (f t)
yukl x = component @Straight @Arrow @into @(T_TT_I f g)
	`compose` wrap @into @(T_TT_I f g _)
	`compose` yoneda @Straight @Functor @Constant x
	`compose` wrap

yoklKL :: forall from into g f s t .
	Component Natural from into (T_TT_I f g) (TT_T_I f g) =>
	Covariant Yoneda Functor from into f =>
	Castable Opposite into (Straight from s (g t)) =>
	Castable Straight into (TT_T_I f g t) =>
	Castable Opposite into (T_TT_I f g t) =>
	f s -> into (from s (g t)) (g (f t))
yoklKL x = unwrap @into @(TT_T_I f g _)
	`compose` component @Straight @from @into @(T_TT_I f g) @(TT_T_I f g)
	`compose` wrap @into @(T_TT_I f g _)
	`compose` yoneda @Straight @Functor @from x

_yokl :: forall from into g f i s t .
	Component Natural from into (T_TT_I (U_I_II f i) g) (U_I_II f i) =>
	Covariant Yoneda Functor from into (U_I_II f i) =>
	Castable Opposite into (U_I_II from s (g t)) =>
	Castable Straight into (U_I_II f i t) =>
	Castable Opposite into (T_TT_I (U_I_II f i) g t) =>
	f i s -> into (from s (g t)) (f i t)
_yokl x = unwrap @into @(U_I_II f i t)
	`compose` component @Straight @from @into @(T_TT_I (U_I_II f i) g)
	`compose` wrap @into @(T_TT_I (U_I_II f i) g _)
	`compose` yoneda @Straight @Functor @from (U_I_II x)

fo'fo :: forall from into f g s t .
	Covariant Semi Functor from into g =>
	Covariant Endo Semi Functor into f =>
	from s t -> into (f (g s)) (f (g t))
fo'fo from = fo @into @into (fo @from @into from)

fo'fo'fo :: forall from into f g h s t .
	Covariant Semi Functor from into h =>
	Covariant Endo Semi Functor into g =>
	Covariant Endo Semi Functor into f =>
	from s t -> into (f (g (h s))) (f (g (h t)))
fo'fo'fo from = fo @into @into (fo @into @into (fo @from @into from))

_fo, _fo'fi, _fo'fi'fi :: forall from into f s t i .
	Covariant Semi Functor from into (U_I_II f i) =>
	Wrapper into (U_I_II f i s) =>
	Wrapper into (U_I_II f i t) =>
	from s t -> into (f i s) (f i t)
_fo from = unwrap `compose` fo @_ @_ @(U_I_II _ _) from `compose` wrap
_fo'fi from = unwrap `compose` fo @_ @_ @(U_I_II _ _) from `compose` wrap
_fo'fi'fi from = unwrap `compose` fo @_ @_ @(U_I_II _ _) from `compose` wrap

fo_ :: forall from into f s t i .
	Covariant Semi Functor from into (U_II_I f i) =>
	Wrapper into (U_II_I f i s) =>
	Wrapper into (U_II_I f i t) =>
	from s t -> into (f s i) (f t i)
fo_ from = unwrap `compose` fo @_ @_ @(U_II_I _ _) from `compose` wrap

fa_ :: forall from into f s t i .
	Contravariant Semi Functor from into (U_II_I f i) =>
	Wrapper into (U_II_I f i s) =>
	Wrapper into (U_II_I f i t) =>
	from s t -> into (f t i) (f s i)
fa_ from = unwrap `compose` fa @_ @_ @(U_II_I _ _) from `compose` wrap

_fo'fo :: forall from into f g o s t .
	Covariant Semi Functor into into (U_I_II f o) =>
	Covariant Semi Functor from into g =>
	(forall i . Wrapper into (U_I_II f o i)) =>
	from s t -> into (f o (g s)) (f o (g t))
_fo'fo from = _fo @into @into (fo @from @into from)

o :: forall from into i s t .
	Precategory into =>
	Covariant Yoneda Functor from into (U_I_II from i) =>
	Castable Opposite into (U_I_II from s t) =>
	Castable Straight into (U_I_II from i t) =>
	from i s -> into (from s t) (from i t)
o x = unwrap `compose` yo @from @into @(U_I_II from _) (U_I_II x)

a :: forall into from i s t .
	Precategory into =>
	Contravariant Yoneda Functor from into (U_II_I from i) =>
	Castable Opposite into (Opposite from s t) =>
	Castable Straight into (Opposite from i t) =>
	from s i -> into (from t s) (from t i)
a x = unwrap `compose` ya @from @into @(U_II_I from _) (U_II_I x)

u :: forall from into i s t .
	Precategory into =>
	Covariant Yoneda Functor from into (U_1_I from i) =>
	Castable Opposite into (U_I_II from s t) =>
	Castable Straight into (U_I_II from i t) =>
	Castable Opposite (->) (from Unit s) =>
	Castable Straight into (from Unit t) =>
	Castable Straight into (U_1_I from i t) =>
	Supertype (from Unit s) -> into (from s t) (Supertype (from Unit t))
u x = unwrap `compose` unwrap `compose` yo @from @into @(U_1_I from _)
	(U_1_I @from @i / wrap @(->) @(from _ _) x)

a'a :: forall from into i o e b .
	Precategory from =>
	Precategory into =>
	Contravariant Yoneda Functor from from (U_II_I from e) =>
	Contravariant Yoneda Functor from into (U_II_I from (from b e)) =>
	Castable Opposite from (Opposite from o b) =>
	Castable Straight from (Opposite from e b) =>
	Castable Opposite into (Opposite from (from b o) i) =>
	Castable Straight into (Opposite from (from b e) i) =>
	from o e -> into (from i (from b o)) (from i (from b e))
a'a = a @into @from `compose` a @from @from

ro :: forall from into hom f i .
	Covariant (Representable hom) Functor from into f =>
	Castable Straight into (Straight hom (Representation f) i) =>
	into (f i) (hom (Representation f) i)
ro = unwrap `compose` component @Straight @from @into @f @(Straight hom (Representation f))

ra :: forall from into hom f i .
	Contravariant (Representable hom) Functor from into f =>
	Castable Straight into (Opposite hom (Representation f) i) =>
	into (f i) (hom i (Representation f))
ra = unwrap `compose` component @Opposite @from @into @f @(Opposite hom (Representation f))

lj :: forall from into f g s t .
	Adjoint Functor from into f g =>
	Castable Straight into ((T_TT_I g f) s) =>
	Castable Opposite into (I s) =>
	from (f s) t -> into s (g t)
lj from = fo from
	`compose` unwrap @into
	`compose` component @Straight @from @into @I @(g `T_TT_I` f)
	`compose` wrap @into

_lj :: forall from into f g e ee s t .
	Adjoint Functor from into (U_I_II f e) (U_I_II g ee) =>
	Castable Straight into ((T_TT_I (U_I_II g ee) (U_I_II f e)) s) =>
	Castable Straight into (U_I_II g ee t) =>
	Castable Opposite into (I s) =>
	Castable Straight from (U_I_II f e s) =>
	from (f e s) t -> into s (g ee t)
_lj from = unwrap @into @(U_I_II g _ _)
	`compose` fo (from `compose` unwrap @from @(U_I_II f _ _))
	`compose` unwrap @into @(T_TT_I _ _ _)
	`compose` component @Straight @from @into @I @(U_I_II g ee `T_TT_I` U_I_II f e)
	`compose` wrap @into

rj :: forall from into f g s t .
	Adjoint Functor from into f g =>
	Castable Opposite from ((T_TT_I f g) t) =>
	Castable Straight from (I t) =>
	into s (g t) -> from (f s) t
rj from = unwrap @from
	`compose` component @Straight @into @from @(f `T_TT_I` g) @I
	`compose` wrap @from
	`compose` fo from

lm :: forall from into i o oo .
	Category from =>
	Limit Straight from into =>
	Covariant Functor into into (That (Product into) o) =>
	Covariant Functor into into (This (Product into) (Product into i i)) =>
	Castable Straight into (Both (Product into) (Product into i i)) =>
	Castable Straight into (That (Product into) o oo) =>
	Castable Opposite into (This (Product into) i i) =>
	Castable Opposite into (That (Product into) i i) =>
	Castable Straight into (Both (Product into) i) =>
	Castable Straight into (This (Product into) (Product into i i) o) =>
	Castable Opposite into (This (Product into) (Product into i i) (Product into i i)) =>
	Wrapper into (That (Product into) o (Product into i i)) =>
	(forall e . Wrapper into (I e)) =>
	from i o -> from i oo -> into i (Product into o oo)
lm from_this from_that = 
	_i (semifunctor @Straight (wrapped (that @Straight from_that))) `compose`
	i_ (semifunctor @Straight (wrapped (this @Straight from_this))) `compose`
	wrapped (map @Straight @Straight @from @into @I @(Both (Product into)) identity) `compose`
	wrapped (map @Straight @Straight @from @into @I @(Both (Product into)) identity)

ml :: forall from into i o oo .
	Category from =>
	Limit Opposite from into =>
	Covariant Functor into into (That (Sum into) o) =>
	Covariant Functor into into (This (Sum into) (Sum into i i)) =>
	Castable Opposite into (Both (Sum into) (Sum into i i)) =>
	Castable Opposite into (That (Sum into) o oo) =>
	Castable Straight into (That (Sum into) i i) =>
	Castable Straight into (This (Sum into) i i) =>
	Castable Opposite into (Both (Sum into) i) =>
	Castable Opposite into (This (Sum into) (Sum into i i) o) =>
	Castable Straight into (This (Sum into) (Sum into i i) (Sum into i i)) =>
	Wrapper into (That (Sum into) o (Sum into i i)) =>
	(forall e . Wrapper into (I e)) =>
	from o i -> from oo i -> into (Sum into o oo) i
ml from_this from_that = 
	wrapped (map @Opposite @Opposite @from @into @I @(Both (Sum into)) identity) `compose`
	wrapped (map @Opposite @Opposite @from @into @I @(Both (Sum into)) identity) `compose`
	i_ (semifunctor @Straight (wrapped (this @Opposite from_this))) `compose`
	_i (semifunctor @Straight (wrapped (that @Opposite from_that)))

pp'fo :: forall from i ii r f .
	Covariant Monoidal Functor from (/\) (/\) f =>
	from (i /\ ii) r -> f i /\ f ii -> f r
pp'fo = monoidal @Straight @from @f @(/\) @(/\) identity

pp :: forall i ii f .
	Covariant Monoidal Functor Arrow (/\) (/\) f =>
	f i -> f ii -> f (i /\ ii)
pp x y = monoidal @Straight @Arrow @f @(/\) @(/\) identity identity (These x y)

-- TODO: define pp'yo instead of pp'fo

w'u :: forall into s t .
	Precategory into =>
	Castable Opposite into t =>
	Castable Straight into s =>
	into (Supertype s) (Supertype t) -> into s t
w'u into = wrap @into `compose` into `compose` unwrap @into

u'w :: forall into s t .
	Precategory into =>
	Castable Opposite into s =>
	Castable Straight into t =>
	into s t -> into (Supertype s) (Supertype t)
u'w into = unwrap @into `compose` into `compose` wrap @into

u'u :: forall into s .
	Precategory into =>
	Castable Straight into s =>
	Castable Straight into (Supertype s) =>
	into s (Supertype (Supertype s))
u'u = unwrap @into `compose` unwrap @into

o'yokl :: forall from into t tt a o e .
	Covariant Functor (->) into tt =>
	Covariant Functor (->) into t =>
	Covariant Functor into into t =>
	Covariant Yoneda Functor from into t =>
	Covariant Yoneda Functor into into (U_I_II into (from a (tt o))) =>
	Mapping Straight Straight (->) into (T_TT_I t tt) t =>
	Castable Opposite into (U_I_II from a (tt o)) =>
	(forall ee . Wrapper into (U_I_II into ee e)) =>
	(forall ee . Wrapper into (T_TT_I t tt ee)) =>
	t a -> into (into (t o) e) (into (from a (tt o)) e)
o'yokl = o `compose` yokl @from @into @tt @t