{-# LANGUAGE AllowAmbiguousTypes #-}
module Ya.Algebra.Operators where

import Ya.Algebra.Abstract
import Ya.Algebra.Definition
import Ya.Algebra.Instances ()

infixl 9 `i`, `u`, `o`, `a`
infixl 8 `ii`, `fo`, `fa`, `yi`, `yo`, `ya`, `yu`, `a'a`, `lj`, `rj`, `ro`, `ra`, `pp`, `lm`, `w'u`, `u'w`, `u'u`
infixl 7 `iii`, `yi_`, `_fo`, `fo_`, `fa_`
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
fo'fi = semifunctor @Flat
fo = semifunctor @Flat

yo :: forall from into f s t .
	Precategory into =>
	Covariant Yoneda Functor from into f =>
	Castable Dual into (U_I_II from s t) =>
	f s -> into (from s t) (f t)
yo x = yoneda @Flat @Functor x

yu :: forall into f s t .
	Precategory into =>
	Covariant Yoneda Functor Constant into f =>
	Castable Dual into (U_I_II Constant s t) =>
	Castable Dual into (Constant s t) =>
	f s -> into t (f t)
yu x = yoneda @Flat @Functor x `compose` wrap @into @(Constant _ _)

yo'o :: forall from into f g s t .
	Precategory into =>
	Covariant Functor from from g =>
	Covariant Yoneda Functor from into f =>
	Contravariant Endo Semi Functor Arrow (U_II_I into (f (g t))) =>
	Castable Dual into (U_I_II from (g s) (g t)) =>
	f (g s) -> into (from s t) (f (g t))
yo'o x = fa_ fo (yo @from @into x)

-- TODO: yo'yo : f (g s) -> into (from s b) (g s -> into (from b t) (f (g t)))

fa, fa'fi :: forall from into f s t .
	Contravariant Semi Functor from into f =>
	from s t -> into (f t) (f s)
fa'fi = semifunctor @Dual
fa = semifunctor @Dual

ya :: forall from into f s t .
	Precategory into =>
	Contravariant Yoneda Functor from into f =>
	Castable Dual into (Dual from s t) =>
	f s -> into (from t s) (f t)
ya x = yoneda @Dual @Functor x

fokl :: forall from into f g s t .
	Component Natural from into (T_TT_I f g) f =>
	Castable Dual into (T_TT_I f g t) =>
	from s (g t) -> into (f s) (f t)
fokl from = component @Flat @from @into @(f `T_TT_I` g) @f
	`compose` wrap `compose` fo from

yokl :: forall from into g f s t .
	Component Natural Arrow into (T_TT_I f g) f =>
	Covariant Yoneda Functor from into f =>
	Castable Dual into (Flat from s (g t)) =>
	Castable Dual into (T_TT_I f g t) =>
	f s -> into (from s (g t)) (f t)
yokl x = component @Flat @Arrow @into @(T_TT_I f g)
	`compose` wrap @into @(T_TT_I f g _)
	`compose` yoneda @Flat @Functor @from x

yukl :: forall into g f s t .
	Component Natural Arrow into (T_TT_I f g) f =>
	Covariant Yoneda Functor Constant into f =>
	Castable Dual into (Flat Constant s (g t)) =>
	Castable Dual into (Constant s (g t)) =>
	Castable Dual into (T_TT_I f g t) =>
	f s -> into (g t) (f t)
yukl x = component @Flat @Arrow @into @(T_TT_I f g)
	`compose` wrap @into @(T_TT_I f g _)
	`compose` yoneda @Flat @Functor @Constant x
	`compose` wrap

yoklKL :: forall from into g f s t .
	Component Natural from into (T_TT_I f g) (TT_T_I f g) =>
	Covariant Yoneda Functor from into f =>
	Castable Dual into (Flat from s (g t)) =>
	Castable Flat into (TT_T_I f g t) =>
	Castable Dual into (T_TT_I f g t) =>
	f s -> into (from s (g t)) (g (f t))
yoklKL x = unwrap @into @(TT_T_I f g _)
	`compose` component @Flat @from @into @(T_TT_I f g) @(TT_T_I f g)
	`compose` wrap @into @(T_TT_I f g _)
	`compose` yoneda @Flat @Functor @from x

_yokl :: forall from into g f i s t .
	Component Natural from into (T_TT_I (U_I_II f i) g) (U_I_II f i) =>
	Covariant Yoneda Functor from into (U_I_II f i) =>
	Castable Dual into (U_I_II from s (g t)) =>
	Castable Flat into (U_I_II f i t) =>
	Castable Dual into (T_TT_I (U_I_II f i) g t) =>
	f i s -> into (from s (g t)) (f i t)
_yokl x = unwrap @into @(U_I_II f i t)
	`compose` component @Flat @from @into @(T_TT_I (U_I_II f i) g)
	`compose` wrap @into @(T_TT_I (U_I_II f i) g _)
	`compose` yoneda @Flat @Functor @from (U_I_II x)

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
	Castable Dual into (U_I_II from s t) =>
	Castable Flat into (U_I_II from i t) =>
	from i s -> into (from s t) (from i t)
o x = unwrap `compose` yo @from @into @(U_I_II from _) (U_I_II x)

a :: forall into from i s t .
	Precategory into =>
	Contravariant Yoneda Functor from into (U_II_I from i) =>
	Castable Dual into (Dual from s t) =>
	Castable Flat into (Dual from i t) =>
	from s i -> into (from t s) (from t i)
a x = unwrap `compose` ya @from @into @(U_II_I from _) (U_II_I x)

u :: forall from into i s t .
	Precategory into =>
	Covariant Yoneda Functor from into (U_I_II Constant i) =>
	Castable Dual into (U_I_II from s t) =>
	Castable Flat into (U_I_II Constant i t) =>
	Castable Flat into (Constant i t) =>
	s -> into (from s t) t
u x = unwrap @into @(Constant i t) `compose` unwrap `compose`
	yo @from @into @(U_I_II Constant _) (U_I_II / wrap x)

a'a :: forall from into i o e b .
	Precategory from =>
	Precategory into =>
	Contravariant Yoneda Functor from from (U_II_I from e) =>
	Contravariant Yoneda Functor from into (U_II_I from (from b e)) =>
	Castable Dual from (Dual from o b) =>
	Castable Flat from (Dual from e b) =>
	Castable Dual into (Dual from (from b o) i) =>
	Castable Flat into (Dual from (from b e) i) =>
	from o e -> into (from i (from b o)) (from i (from b e))
a'a = a @into @from `compose` a @from @from

ro :: forall from into hom f i .
	Covariant (Representable hom) Functor from into f =>
	Castable Flat into (Flat hom (Representation f) i) =>
	into (f i) (hom (Representation f) i)
ro = unwrap `compose` component @Flat @from @into @f @(Flat hom (Representation f))

ra :: forall from into hom f i .
	Contravariant (Representable hom) Functor from into f =>
	Castable Flat into (Dual hom (Representation f) i) =>
	into (f i) (hom i (Representation f))
ra = unwrap `compose` component @Dual @from @into @f @(Dual hom (Representation f))

lj :: forall from into f g s t .
	Adjoint Functor from into f g =>
	Castable Flat into ((T_TT_I g f) s) =>
	Castable Dual into (I s) =>
	from (f s) t -> into s (g t)
lj from = fo from
	`compose` unwrap @into
	`compose` component @Flat @from @into @I @(g `T_TT_I` f)
	`compose` wrap @into

_lj :: forall from into f g e ee s t .
	Adjoint Functor from into (U_I_II f e) (U_I_II g ee) =>
	Castable Flat into ((T_TT_I (U_I_II g ee) (U_I_II f e)) s) =>
	Castable Flat into (U_I_II g ee t) =>
	Castable Dual into (I s) =>
	Castable Flat from (U_I_II f e s) =>
	from (f e s) t -> into s (g ee t)
_lj from = unwrap @into @(U_I_II g _ _)
	`compose` fo (from `compose` unwrap @from @(U_I_II f _ _))
	`compose` unwrap @into @(T_TT_I _ _ _)
	`compose` component @Flat @from @into @I @(U_I_II g ee `T_TT_I` U_I_II f e)
	`compose` wrap @into

rj :: forall from into f g s t .
	Adjoint Functor from into f g =>
	Castable Dual from ((T_TT_I f g) t) =>
	Castable Flat from (I t) =>
	into s (g t) -> from (f s) t
rj from = unwrap @from
	`compose` component @Flat @into @from @(f `T_TT_I` g) @I
	`compose` wrap @from
	`compose` fo from

lm :: forall from into i o oo .
	Category from =>
	Limit' Flat from into =>
	Covariant Functor into into (That (Product into) o) =>
	Covariant Functor into into (This (Product into) (Product into i i)) =>
	Castable Flat into (Both (Product into) (Product into i i)) =>
	Castable Flat into (That (Product into) o oo) =>
	Castable Dual into (This (Product into) i i) =>
	Castable Dual into (That (Product into) i i) =>
	Castable Flat into (Both (Product into) i) =>
	Castable Flat into (This (Product into) (Product into i i) o) =>
	Castable Dual into (This (Product into) (Product into i i) (Product into i i)) =>
	Wrapper into (That (Product into) o (Product into i i)) =>
	(forall e . Wrapper into (I e)) =>
	from i o -> from i oo -> into i (Product into o oo)
lm from_this from_that = 
	_i (semifunctor @Flat (wrapped (that @Flat from_that))) `compose`
	i_ (semifunctor @Flat (wrapped (this @Flat from_this))) `compose`
	wrapped (map @Flat @Flat @from @into @I @(Both (Product into)) identity) `compose`
	wrapped (map @Flat @Flat @from @into @I @(Both (Product into)) identity)

pp'fo :: forall from i ii r f .
	Covariant Monoidal Functor from (/\) (/\) f =>
	from (i /\ ii) r -> f i /\ f ii -> f r
pp'fo = monoidal @Flat @from @f @(/\) @(/\) identity

pp :: forall i ii f .
	Covariant Monoidal Functor Arrow (/\) (/\) f =>
	f i -> f ii -> f (i /\ ii)
pp x y = monoidal @Flat @Arrow @f @(/\) @(/\) identity identity (These x y)

-- TODO: define pp'yo instead of pp'fo

w'u :: forall into s t .
	Precategory into =>
	Castable Dual into t =>
	Castable Flat into s =>
	into (Supertype s) (Supertype t) -> into s t
w'u into = wrap @into `compose` into `compose` unwrap @into

u'w :: forall into s t .
	Precategory into =>
	Castable Dual into s =>
	Castable Flat into t =>
	into s t -> into (Supertype s) (Supertype t)
u'w into = unwrap @into `compose` into `compose` wrap @into

u'u :: forall into s .
	Precategory into =>
	Castable Flat into s =>
	Castable Flat into (Supertype s) =>
	into s (Supertype (Supertype s))
u'u = unwrap @into `compose` unwrap @into
