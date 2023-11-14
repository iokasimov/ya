{-# LANGUAGE AllowAmbiguousTypes #-}
module Ya.Algebra.Operators where

import Ya.Algebra.Abstract
import Ya.Algebra.Definition
import Ya.Algebra.Instances ()

infixl 9 `i`, `u`, `o`, `a`
infixl 8 `i'i`, `u'u`, `fo`, `fa`, `yi`, `yo`, `ya`, `yu`, `a'a`, `o'a`, `a'o`, `lj`, `rj`, `ro`, `ra`, `pp`, `lm`, `ml`, `cc`
infixl 7 `i'i'i`, `u'u'u`, `yi_`, `ya_`, `_fo`, `fo_`, `yo_`, `fa_`, `w'uw`, `uw'w`
infixl 6 `i'i'i'i`, `u'u'u'u`, `yi'yi`, `fo'fi`, `fa'fi`, `fokl`, `fo'fo`, `yokl`, `pp'fo`, `yo'o`, `uw'uw` -- , `yukl`
infixl 5 `i'i'i'i'i`, `u'u'u'u'u`, `fi_'fi`, `_fo'fi`, `_fo'fo`, `_yokl`, `a'yokl`
infixl 4 `i'i'i'i'i'i`, `u'u'u'u'u'u`, `yi'yi'yi`, `fo'fo'fo`, `yoklKL`
infixl 3 `i'i'i'i'i'i'i`, `u'u'u'u'u'u'u`, `fi_'fi'fi`, `_fo'fi'fi`
infixl 2 `i'i'i'i'i'i'i'i`, `u'u'u'u'u'u'u'u`, `yi'yi'yi'yi`
infixl 1 `i'i'i'i'i'i'i'i'i`, `u'u'u'u'u'u'u'u'u`
infixl 0 `i'i'i'i'i'i'i'i'i'i`, `u'u'u'u'u'u'u'u'u'u`, `yi'yi'yi'yi'yi`

i, i'i, i'i'i, i'i'i'i, i'i'i'i'i, i'i'i'i'i'i, i'i'i'i'i'i'i,
	i'i'i'i'i'i'i'i, i'i'i'i'i'i'i'i'i, i'i'i'i'i'i'i'i'i'i :: Category into => into e e
i'i'i'i'i'i'i'i'i'i = identity
i'i'i'i'i'i'i'i'i = identity
i'i'i'i'i'i'i'i = identity
i'i'i'i'i'i'i = identity
i'i'i'i'i'i = identity
i'i'i'i'i = identity
i'i'i'i = identity
i'i'i = identity
i'i = identity
i = identity

yi'yi'yi'yi'yi, yi'yi'yi'yi, yi'yi'yi, yi'yi, yi_, yi
	:: Category into => into e e
yi'yi'yi'yi'yi = identity
yi'yi'yi'yi = identity
yi'yi'yi = identity
yi'yi = identity
yi_ = identity
yi = identity

fi_, fi_'fi, fi_'fi'fi
	:: Category into => into (into a o) (into a o)
fi_ = identity
fi_'fi = identity
fi_'fi'fi = identity

fo, fo'fi :: forall from into t a o .
	Covariant Semi Functor from into t =>
	from a o -> into (t a) (t o)
fo'fi = semifunctor @Straight
fo = semifunctor @Straight

fa, fa'fi :: forall from into t a o .
	Contravariant Semi Functor from into t =>
	from a o -> into (t o) (t a)
fa'fi = semifunctor @Opposite
fa = semifunctor @Opposite

fu, fu'fi :: forall from into t a o .
	Covariant Semi Functor from into t =>
	Mapping Constant Straight from into t t =>
	Castable Opposite Arrow (from Unit o) =>
	Supertype (from Unit o) -> into (t a) (t o)
fu'fi = semifunctor @Constant @from @into `compose` wrap @Arrow @(from Unit o)
fu = semifunctor @Constant @from @into `compose` wrap @Arrow @(from Unit o)

yo :: forall from into t a o .
	Precategory into =>
	Covariant Yoneda Functor from into t =>
	Castable Opposite into (U_I_II from a o) =>
	t a -> into (from a o) (t o)
yo x = yoneda @Straight @Functor x

yo_ :: forall from into t e a o .
	Precategory into =>
	Covariant Yoneda Functor from into (This t e) =>
	Castable Opposite into (Straight from a o) =>
	Castable Straight into (This t e o) =>
	t a e -> into (from a o) (t o e)
yo_ x = compose uw (yoneda @Straight @Functor @from @into @(This t e) (wrap x))

yu :: forall into t a o .
	Covariant Yoneda Functor into into t =>
	Covariant Endo Semi Functor (->) t =>
	Castable Opposite into (into Unit o) =>
	Castable Opposite into (U_I_II into Unit o) =>
	t a -> into (Supertype (into Unit o)) (t o)
yu x = yoneda @U_I_II @Functor (fu @Arrow Unit x)
	`compose` wrap @into @(into Unit o)

yo'o :: forall from into t tt a o .
	Precategory into =>
	Covariant Functor from from tt =>
	Covariant Yoneda Functor from into t =>
	Contravariant Endo Semi Functor Arrow (U_II_I into (t (tt o))) =>
	Castable Opposite into (U_I_II from (tt a) (tt o)) =>
	t (tt a) -> into (from a o) (t (tt o))
yo'o x = fa_ fo (yo @from @into x)

-- TODO: yo'yo : t (tt a) -> into (from a b) (tt a -> into (from b o) (t (tt o)))

ya :: forall from into t a o .
	Precategory into =>
	Contravariant Yoneda Functor from into t =>
	Castable Opposite into (Opposite from a o) =>
	t a -> into (from o a) (t o)
ya = yoneda @Opposite @Functor

ya_ :: forall from into t e a o .
	Precategory into =>
	Contravariant Yoneda Functor from into (This t e) =>
	Castable Opposite into (Opposite from a o) =>
	Castable Straight into (This t e o) =>
	t a e -> into (from o a) (t o e)
ya_ x = compose uw (yoneda @Opposite @Functor @from @into @(This t e) (wrap x))

fokl :: forall from into t tt a o .
	Component Natural from into (T_TT_I t tt) t =>
	Castable Opposite into (T_TT_I t tt o) =>
	from a (tt o) -> into (t a) (t o)
fokl from = component @Straight @from @into @(t `T_TT_I` tt) @t
	`compose` wrap `compose` fo from

yokl :: forall from into tt t a o .
	Component Natural Arrow into (T_TT_I t tt) t =>
	Covariant Yoneda Functor from into t =>
	Castable Opposite into (Straight from a (tt o)) =>
	Castable Opposite into (T_TT_I t tt o) =>
	t a -> into (from a (tt o)) (t o)
yokl x = component @Straight @Arrow @into @(T_TT_I t tt)
	`compose` wrap @into @(T_TT_I t tt _)
	`compose` yoneda @Straight @Functor @from x

-- yukl :: forall into tt t a o .
-- 	Component Natural Arrow into (T_TT_I t tt) t =>
-- 	Covariant Yoneda Functor Constant into t =>
-- 	Castable Opposite into (Straight Constant a (tt o)) =>
-- 	Castable Opposite into (Constant a (tt o)) =>
-- 	Castable Opposite into (T_TT_I t tt o) =>
-- 	t a -> into (tt o) (t o)
-- yukl x = component @Straight @Arrow @into @(T_TT_I t tt)
-- 	`compose` wrap @into @(T_TT_I t tt _)
-- 	`compose` yoneda @Straight @Functor @Constant x
-- 	`compose` wrap

yoklKL :: forall from into tt t a o .
	Component Natural from into (T_TT_I t tt) (TT_T_I t tt) =>
	Covariant Yoneda Functor from into t =>
	Castable Opposite into (Straight from a (tt o)) =>
	Castable Straight into (TT_T_I t tt o) =>
	Castable Opposite into (T_TT_I t tt o) =>
	t a -> into (from a (tt o)) (tt (t o))
yoklKL x = uw @into @(TT_T_I t tt _)
	`compose` component @Straight @from @into @(T_TT_I t tt) @(TT_T_I t tt)
	`compose` wrap @into @(T_TT_I t tt _)
	`compose` yoneda @Straight @Functor @from x

_yokl :: forall from into tt t i a o .
	Component Natural from into (T_TT_I (U_I_II t i) tt) (U_I_II t i) =>
	Covariant Yoneda Functor from into (U_I_II t i) =>
	Castable Opposite into (U_I_II from a (tt o)) =>
	Castable Straight into (U_I_II t i o) =>
	Castable Opposite into (T_TT_I (U_I_II t i) tt o) =>
	t i a -> into (from a (tt o)) (t i o)
_yokl x = uw @into @(U_I_II t i o)
	`compose` component @Straight @from @into @(T_TT_I (U_I_II t i) tt)
	`compose` wrap @into @(T_TT_I (U_I_II t i) tt _)
	`compose` yoneda @Straight @Functor @from (U_I_II x)

fo'fo :: forall from into t tt a o .
	Covariant Semi Functor from into tt =>
	Covariant Endo Semi Functor into t =>
	from a o -> into (t (tt a)) (t (tt o))
fo'fo from = fo @into @into (fo @from @into from)

fo'fo'fo :: forall from into t tt h a o .
	Covariant Semi Functor from into h =>
	Covariant Endo Semi Functor into tt =>
	Covariant Endo Semi Functor into t =>
	from a o -> into (t (tt (h a))) (t (tt (h o)))
fo'fo'fo from = fo @into @into (fo @into @into (fo @from @into from))

_fo, _fo'fi, _fo'fi'fi :: forall from into t a o i .
	Covariant Semi Functor from into (U_I_II t i) =>
	Wrapper into (U_I_II t i a) =>
	Wrapper into (U_I_II t i o) =>
	from a o -> into (t i a) (t i o)
_fo from = uw `compose` fo @_ @_ @(U_I_II _ _) from `compose` wrap
_fo'fi from = uw `compose` fo @_ @_ @(U_I_II _ _) from `compose` wrap
_fo'fi'fi from = uw `compose` fo @_ @_ @(U_I_II _ _) from `compose` wrap

fo_ :: forall from into t a o i .
	Covariant Semi Functor from into (U_II_I t i) =>
	Wrapper into (U_II_I t i a) =>
	Wrapper into (U_II_I t i o) =>
	from a o -> into (t a i) (t o i)
fo_ from = uw `compose` fo @_ @_ @(U_II_I _ _) from `compose` wrap

fa_ :: forall from into t a o i .
	Contravariant Semi Functor from into (U_II_I t i) =>
	Wrapper into (U_II_I t i a) =>
	Wrapper into (U_II_I t i o) =>
	from a o -> into (t o i) (t a i)
fa_ from = uw `compose` fa @_ @_ @(U_II_I _ _) from `compose` wrap

_fo'fo :: forall from into t tt e a o .
	Covariant Semi Functor into into (U_I_II t e) =>
	Covariant Semi Functor from into tt =>
	(forall i . Wrapper into (U_I_II t e i)) =>
	from a o -> into (t e (tt a)) (t e (tt o))
_fo'fo from = _fo @into @into (fo @from @into from)

o :: forall from into u i a o .
	Precategory into =>
	Covariant Yoneda Functor from into (U_I_II u i) =>
	Castable Opposite into (U_I_II from a o) =>
	Castable Straight into (U_I_II u i o) =>
	u i a -> into (from a o) (u i o)
o x = uw `compose` yo @from @into @(U_I_II u _) (U_I_II x)

a :: forall into from u e a o .
	Precategory into =>
	Contravariant Yoneda Functor from into (U_II_I u e) =>
	Castable Opposite into (Opposite from a o) =>
	Castable Straight into (Opposite u e o) =>
	u a e -> into (from o a) (u o e)
a x = uw `compose` ya @from @into @(U_II_I u _) (U_II_I x)

a'a :: forall from into u i o e b .
	Precategory from =>
	Precategory into =>
	Contravariant Yoneda Functor from from (U_II_I u e) =>
	Contravariant Yoneda Functor from into (U_II_I from (u b e)) =>
	Castable Opposite from (Opposite from o b) =>
	Castable Straight from (Opposite u e b) =>
	Castable Opposite into (Opposite from (from b o) i) =>
	Castable Straight into (Opposite from (u b e) i) =>
	u o e -> into (from i (from b o)) (from i (u b e))
a'a = a @into @from `compose` a @from @from

o'a :: forall from into u i o e b .
	Precategory from =>
	Precategory into =>
	Category from =>
	Category into =>
	Contravariant Yoneda Functor from from (U_II_I u e) =>
	Covariant Yoneda Functor into from (U_I_II from (from i o)) =>
	Castable Opposite from (U_I_II into (u i e) b) =>
	Castable Straight from (U_I_II from (from i o) b) =>
	Castable Straight from (Opposite u e i) =>
	Castable Opposite from (Opposite from o i) =>
	u o e -> from (into (u i e) b) (from (from i o) b)
o'a = o @into @from `compose` a @from @from

a'o :: forall from into u uu o e i a .
	Category from =>
	Category into =>
	Contravariant Yoneda Functor from into (U_II_I from (u i e)) =>
	Covariant Yoneda Functor from from (U_I_II u i) =>
	Castable Opposite from (U_I_II from a e) =>
	Castable Straight from (U_I_II u i e) =>
	Castable Straight into (Opposite from (u i e) o) =>
	Castable Opposite into (Opposite from (from a e) o) =>
	u i a -> into (from o (from a e)) (from o (u i e))
a'o = a @into @from `compose` o @from @from

u, u'u, u'u'u, u'u'u'u, u'u'u'u'u, u'u'u'u'u'u, u'u'u'u'u'u'u,
	u'u'u'u'u'u'u'u, u'u'u'u'u'u'u'u'u, u'u'u'u'u'u'u'u'u'u :: forall from into i a o .
	Precategory into =>
	Covariant Yoneda Functor from into (U_1_I from i) =>
	Castable Opposite into (U_I_II from a o) =>
	Castable Straight into (U_I_II from i o) =>
	Castable Opposite (->) (from Unit a) =>
	Castable Straight into (from Unit o) =>
	Castable Straight into (U_1_I from i o) =>
	Supertype (from Unit a) -> into (from a o) (Supertype (from Unit o))
u x = uw `compose` uw `compose` yo @from @into @(U_1_I from _)
	(U_1_I @from @i / wrap @(->) @(from _ _) x)
u'u x = uw `compose` uw `compose` yo @from @into @(U_1_I from _)
	(U_1_I @from @i / wrap @(->) @(from _ _) x)
u'u'u x = uw `compose` uw `compose` yo @from @into @(U_1_I from _)
	(U_1_I @from @i / wrap @(->) @(from _ _) x)
u'u'u'u x = uw `compose` uw `compose` yo @from @into @(U_1_I from _)
	(U_1_I @from @i / wrap @(->) @(from _ _) x)
u'u'u'u'u x = uw `compose` uw `compose` yo @from @into @(U_1_I from _)
	(U_1_I @from @i / wrap @(->) @(from _ _) x)
u'u'u'u'u'u x = uw `compose` uw `compose` yo @from @into @(U_1_I from _)
	(U_1_I @from @i / wrap @(->) @(from _ _) x)
u'u'u'u'u'u'u x = uw `compose` uw `compose` yo @from @into @(U_1_I from _)
	(U_1_I @from @i / wrap @(->) @(from _ _) x)
u'u'u'u'u'u'u'u x = uw `compose` uw `compose` yo @from @into @(U_1_I from _)
	(U_1_I @from @i / wrap @(->) @(from _ _) x)
u'u'u'u'u'u'u'u'u x = uw `compose` uw `compose` yo @from @into @(U_1_I from _)
	(U_1_I @from @i / wrap @(->) @(from _ _) x)
u'u'u'u'u'u'u'u'u'u x = uw `compose` uw `compose` yo @from @into @(U_1_I from _)
	(U_1_I @from @i / wrap @(->) @(from _ _) x)

ro :: forall from into hom t i .
	Covariant (Representable hom) Functor from into t =>
	Castable Straight into (Straight hom (Representation t) i) =>
	into (t i) (hom (Representation t) i)
ro = uw `compose` component @Straight @from @into @t @(Straight hom (Representation t))

ra :: forall from into hom t i .
	Contravariant (Representable hom) Functor from into t =>
	Castable Straight into (Opposite hom (Representation t) i) =>
	into (t i) (hom i (Representation t))
ra = uw `compose` component @Opposite @from @into @t @(Opposite hom (Representation t))

lj :: forall from into t tt a o .
	Adjoint Functor from into t tt =>
	Castable Straight into ((T_TT_I tt t) a) =>
	Castable Opposite into (I a) =>
	from (t a) o -> into a (tt o)
lj from = fo from
	`compose` uw @into
	`compose` component @Straight @from @into @I @(tt `T_TT_I` t)
	`compose` wrap @into

_lj :: forall from into t tt e ee a o .
	Adjoint Functor from into (U_I_II t e) (U_I_II tt ee) =>
	Castable Straight into ((T_TT_I (U_I_II tt ee) (U_I_II t e)) a) =>
	Castable Straight into (U_I_II tt ee o) =>
	Castable Opposite into (I a) =>
	Castable Straight from (U_I_II t e a) =>
	from (t e a) o -> into a (tt ee o)
_lj from = uw @into @(U_I_II tt _ _)
	`compose` fo (from `compose` uw @from @(U_I_II t _ _))
	`compose` uw @into @(T_TT_I _ _ _)
	`compose` component @Straight @from @into @I @(U_I_II tt ee `T_TT_I` U_I_II t e)
	`compose` wrap @into

rj :: forall from into t tt a o .
	Adjoint Functor from into t tt =>
	Castable Opposite from ((T_TT_I t tt) o) =>
	Castable Straight from (I o) =>
	into a (tt o) -> from (t a) o
rj from = uw @from
	`compose` component @Straight @into @from @(t `T_TT_I` tt) @I
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

pp'fo :: forall from e ee r t .
	Covariant Monoidal Functor from (/\) (/\) t =>
	from (e /\ ee) r -> t e /\ t ee -> t r
pp'fo = monoidal @Straight @from @t @(/\) @(/\) identity

pp :: forall e ee t .
	Covariant Monoidal Functor Arrow (/\) (/\) t =>
	t e -> t ee -> t (e /\ ee)
pp x y = monoidal @Straight @Arrow @t @(/\) @(/\) identity identity (These x y)

-- TODO: define pp'yo instead of pp'fo

w'uw :: forall into a o .
	Precategory into =>
	Castable Opposite into o =>
	Castable Straight into a =>
	into (Supertype a) (Supertype o) -> into a o
w'uw into = wrap @into `compose` into `compose` uw @into

uw'w :: forall into a o .
	Precategory into =>
	Castable Opposite into a =>
	Castable Straight into o =>
	into a o -> into (Supertype a) (Supertype o)
uw'w into = uw @into `compose` into `compose` wrap @into

uw'uw :: forall into a .
	Precategory into =>
	Castable Straight into a =>
	Castable Straight into (Supertype a) =>
	into a (Supertype (Supertype a))
uw'uw = uw @into `compose` uw @into

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

a'yokl :: forall from into u t tt a o e .
	Covariant Functor (->) into tt =>
	Covariant Functor (->) into t =>
	Covariant Functor into into tt =>
	Covariant Functor from into t =>
	Covariant Functor from into tt =>
	Covariant Yoneda Functor into into (U_I_II into (from a (tt o))) =>
	Contravariant Yoneda Functor from into (U_II_I into (tt o)) =>
	Mapping Straight Straight from into (T_TT_I tt t) tt =>
	Castable Opposite into (Straight from a (tt o)) =>
	Castable Straight into (Opposite into (tt o) e) =>
	Castable Opposite into (Opposite from (tt a) e) =>
	(forall ee . Wrapper into (T_TT_I tt t ee)) =>
	from a (t o) -> into (from e (tt a)) (into e (tt o))
a'yokl = a `compose` fokl @from @into @tt @t

-- TODO: to generalize, I need to generalize `monoidal` first
-- TODO: effects are executed in reverse order, we can use it
-- to alter execution order, in Scrolling List for example
cc :: forall into t a o .
	Adjoint Functor (->) (->) (That (/\) (t a)) (That into (t a)) =>
	Adjoint Functor (->) (->) (That (/\) a) (That (->) a) =>
	Monoidal Straight Functor (->) (/\) (/\) t =>
	t (a -> o) -> into (t a) (t o)
cc = uw @(->) @(That into (t a) _)
	`compose` (fo @(->) @(->) `compose` fo @(->) @(->))
		(rj @(->) @(->) (wrap @_ @(That _ _ _)) `compose` wrap @_ @(That _ _ _))
	`compose` lj @(->) @(->) @(That (/\) (t a)) @(That into _)
		(monoidal @Straight @(->) @t @(/\) @(/\) identity identity `compose` uw @(->) @(That (/\) (t a) (t (a -> o))))