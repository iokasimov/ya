{-# LANGUAGE AllowAmbiguousTypes #-}
module Ya.Algebra.Operators where

import Ya.Algebra.Abstract
import Ya.Algebra.Definition
import Ya.Algebra.Instances ()

infixl 9 `i`, `u`, `o`, `a`, `a'a`, `o'a`, `a'o`, `a'yokl`
infixl 8 `i'i`, `u'u`, `yi`, `yo`, `ya`, `yu`, `fo`, `fa`, `fu`, `lj`, `rj`, `ro`, `ra`, `pp`, `lm'`, `lm`, `ml'`, `cc`, `fc`, `jt`, `fo'fi`, `fa'fi`, `pp'yo`, `pp'pp`, `yo'yo`, `fo'fo`, `uw'uw`, `lm''pp`, `lm'pp`, `fo'fo'fo`, `pp'pp'yo`, `pp'yokl`, `pp'pp'jt`, `pp'pp'jt'yokl`, `uw'uw'uw`, `lm'pp'pp`
infixl 7 `i'i'i`, `u'u'u`, `yi_`, `ya_`, `_fo`, `fo_`, `yo_`, `fa_`, `yu_`, `_lj`, `_rj`, `fi_'fi`, `_fo'fi`, `_fo'fo`, `fi_'fi'fi`, `_fo'fi'fi`, `w'uw`, `uw'w`, `rwr'yo_`, `rwr'yu_`
infixl 6 `i'i'i'i`, `u'u'u'u`, `yi'yi`, `fokl`, `yokl`, `yukl`, `yokl'u`, `yukl'u`, `yokl'u'u`, `yukl'u'u`, `yokl'u'u'u`, `yukl'u'u'u`, `yukl'u'u'u'u`, `yokl'u'u'u'u`, `yukl'u'u'u'u'u'u`, `yokl'u'u'u'u'u'u`, `yukl'u'u'u'u'u`, `yokl'rwr'yo_`, `yokl'rwr'yu_`, `yokl'u'u'u'u'u`, `yokl'uw'yokl`
infixl 5 `i'i'i'i'i`, `u'u'u'u'u`, `_yokl`
infixl 4 `i'i'i'i'i'i`, `u'u'u'u'u'u`, `yi'yi'yi`, `yoklKL`, `yukl'yi`
infixl 3 `i'i'i'i'i'i'i`, `u'u'u'u'u'u'u`
infixl 2 `i'i'i'i'i'i'i'i`, `u'u'u'u'u'u'u'u`, `yi'yi'yi'yi`, `yukl'yi'yi`
infixl 1 `i'i'i'i'i'i'i'i'i`, `u'u'u'u'u'u'u'u'u`
infixl 0 `i'i'i'i'i'i'i'i'i'i`, `u'u'u'u'u'u'u'u'u'u`, `yi'yi'yi'yi'yi`, `yukl'yi'yi'yi`

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

fu, fu'fi :: forall into t a o .
	Covariant Semi Functor into into t =>
	Mapping Constant Straight into into t t =>
	Castable Opposite Arrow (into Unit o) =>
	Supertype (into Unit o) -> into (t a) (t o)
fu'fi = semifunctor @Constant @into @into `compose` wrap @Arrow @(into Unit o)
fu = semifunctor @Constant @into @into `compose` wrap @Arrow @(into Unit o)

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

yu_ :: forall into t e a o .
	Covariant Yoneda Functor into into (U_II_I t e) =>
	Covariant Endo Semi Functor (->) (U_II_I t e) =>
	Castable Opposite into (into Unit o) =>
	Castable Opposite into (U_I_II into Unit o) =>
	Castable Straight into (U_II_I t e o) =>
	t a e -> into (Supertype (into Unit o)) (t o e)
yu_ x = uw @into @(U_II_I t e _) `compose` yu @into (wrap @(->) @(U_II_I t e _) x)

yo'yo :: forall from into t tt a o .
	Precategory into =>
	Covariant Functor from from tt =>
	Covariant Yoneda Functor from into t =>
	Contravariant Endo Semi Functor Arrow (U_II_I into (t (tt o))) =>
	Castable Opposite into (U_I_II from (tt a) (tt o)) =>
	t (tt a) -> into (from a o) (t (tt o))
yo'yo x = fa_ fo (yo @from @into x)

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
	Component Natural from into (T'TT'I t tt) t =>
	Castable Opposite into (T'TT'I t tt o) =>
	from a (tt o) -> into (t a) (t o)
fokl from = component @Straight @from @into @(t `T'TT'I` tt) @t
	`compose` wrap `compose` fo from

yokl, yokl'u, yokl'u'u, yokl'u'u'u, yokl'u'u'u'u, yokl'u'u'u'u'u, yokl'u'u'u'u'u'u :: forall from into tt t a o .
	Component Natural Arrow into (T'TT'I t tt) t =>
	Covariant Yoneda Functor from into t =>
	Castable Opposite into (Straight from a (tt o)) =>
	Castable Opposite into (T'TT'I t tt o) =>
	t a -> into (from a (tt o)) (t o)
yokl x = component @Straight @Arrow @into @(T'TT'I t tt)
	`compose` wrap @into @(T'TT'I t tt _)
	`compose` yoneda @Straight @Functor @from x
yokl'u x = component @Straight @Arrow @into @(T'TT'I t tt)
	`compose` wrap @into @(T'TT'I t tt _)
	`compose` yoneda @Straight @Functor @from x
yokl'u'u x = component @Straight @Arrow @into @(T'TT'I t tt)
	`compose` wrap @into @(T'TT'I t tt _)
	`compose` yoneda @Straight @Functor @from x
yokl'u'u'u x = component @Straight @Arrow @into @(T'TT'I t tt)
	`compose` wrap @into @(T'TT'I t tt _)
	`compose` yoneda @Straight @Functor @from x
yokl'u'u'u'u x = component @Straight @Arrow @into @(T'TT'I t tt)
	`compose` wrap @into @(T'TT'I t tt _)
	`compose` yoneda @Straight @Functor @from x
yokl'u'u'u'u'u x = component @Straight @Arrow @into @(T'TT'I t tt)
	`compose` wrap @into @(T'TT'I t tt _)
	`compose` yoneda @Straight @Functor @from x
yokl'u'u'u'u'u'u x = component @Straight @Arrow @into @(T'TT'I t tt)
	`compose` wrap @into @(T'TT'I t tt _)
	`compose` yoneda @Straight @Functor @from x

yukl, yukl'u, yukl'u'u, yukl'u'u'u, yukl'u'u'u'u, yukl'u'u'u'u'u, yukl'u'u'u'u'u'u, yukl'yi, yukl'yi'yi, yukl'yi'yi'yi
	:: forall into tt t a o .
	Covariant Endo Semi Functor (->) t =>
	Component Natural Arrow into (T'TT'I t tt) t =>
	Covariant Yoneda Functor into into t =>
	Castable Opposite into (into Unit (tt o)) =>
	Castable Opposite into (Straight into Unit (tt o)) =>
	Castable Opposite into (T'TT'I t tt o) =>
	t a -> into (Supertype (into Unit (tt o))) (t o)
yukl x = component @Straight @Arrow @into @(T'TT'I t tt)
	`compose` wrap @into @(T'TT'I t tt _)
	`compose` yoneda @Straight @Functor (fu @Arrow Unit x)
	`compose` wrap @into @(into Unit (tt o))
yukl'u x = component @Straight @Arrow @into @(T'TT'I t tt)
	`compose` wrap @into @(T'TT'I t tt _)
	`compose` yoneda @Straight @Functor (fu @Arrow Unit x)
	`compose` wrap @into @(into Unit (tt o))
yukl'u'u x = component @Straight @Arrow @into @(T'TT'I t tt)
	`compose` wrap @into @(T'TT'I t tt _)
	`compose` yoneda @Straight @Functor (fu @Arrow Unit x)
	`compose` wrap @into @(into Unit (tt o))
yukl'u'u'u x = component @Straight @Arrow @into @(T'TT'I t tt)
	`compose` wrap @into @(T'TT'I t tt _)
	`compose` yoneda @Straight @Functor (fu @Arrow Unit x)
	`compose` wrap @into @(into Unit (tt o))
yukl'u'u'u'u x = component @Straight @Arrow @into @(T'TT'I t tt)
	`compose` wrap @into @(T'TT'I t tt _)
	`compose` yoneda @Straight @Functor (fu @Arrow Unit x)
	`compose` wrap @into @(into Unit (tt o))
yukl'u'u'u'u'u x = component @Straight @Arrow @into @(T'TT'I t tt)
	`compose` wrap @into @(T'TT'I t tt _)
	`compose` yoneda @Straight @Functor (fu @Arrow Unit x)
	`compose` wrap @into @(into Unit (tt o))
yukl'u'u'u'u'u'u x = component @Straight @Arrow @into @(T'TT'I t tt)
	`compose` wrap @into @(T'TT'I t tt _)
	`compose` yoneda @Straight @Functor (fu @Arrow Unit x)
	`compose` wrap @into @(into Unit (tt o))
yukl'yi x = component @Straight @Arrow @into @(T'TT'I t tt)
	`compose` wrap @into @(T'TT'I t tt _)
	`compose` yoneda @Straight @Functor (fu @Arrow Unit x)
	`compose` wrap @into @(into Unit (tt o))
yukl'yi'yi x = component @Straight @Arrow @into @(T'TT'I t tt)
	`compose` wrap @into @(T'TT'I t tt _)
	`compose` yoneda @Straight @Functor (fu @Arrow Unit x)
	`compose` wrap @into @(into Unit (tt o))
yukl'yi'yi'yi x = component @Straight @Arrow @into @(T'TT'I t tt)
	`compose` wrap @into @(T'TT'I t tt _)
	`compose` yoneda @Straight @Functor (fu @Arrow Unit x)
	`compose` wrap @into @(into Unit (tt o))

yoklKL :: forall from into tt t a o .
	Component Natural from into (T'TT'I t tt) (TT'T'I t tt) =>
	Covariant Yoneda Functor from into t =>
	Castable Opposite into (Straight from a (tt o)) =>
	Castable Straight into (TT'T'I t tt o) =>
	Castable Opposite into (T'TT'I t tt o) =>
	t a -> into (from a (tt o)) (tt (t o))
yoklKL x = uw @into @(TT'T'I t tt _)
	`compose` component @Straight @from @into @(T'TT'I t tt) @(TT'T'I t tt)
	`compose` wrap @into @(T'TT'I t tt _)
	`compose` yoneda @Straight @Functor @from x

_yokl :: forall from into tt t i a o .
	Component Natural from into (T'TT'I (U_I_II t i) tt) (U_I_II t i) =>
	Covariant Yoneda Functor from into (U_I_II t i) =>
	Castable Opposite into (U_I_II from a (tt o)) =>
	Castable Straight into (U_I_II t i o) =>
	Castable Opposite into (T'TT'I (U_I_II t i) tt o) =>
	t i a -> into (from a (tt o)) (t i o)
_yokl x = uw @into @(U_I_II t i o)
	`compose` component @Straight @from @into @(T'TT'I (U_I_II t i) tt)
	`compose` wrap @into @(T'TT'I (U_I_II t i) tt _)
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
	Wrapper into (U_I_II t e (tt a)) =>
	Wrapper into (U_I_II t e (tt o)) =>
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
	Contravariant Yoneda Functor from from (U_II_I u e) =>
	Covariant Yoneda Functor into from (U_I_II from (from i o)) =>
	Castable Opposite from (U_I_II into (u i e) b) =>
	Castable Straight from (U_I_II from (from i o) b) =>
	Castable Straight from (Opposite u e i) =>
	Castable Opposite from (Opposite from o i) =>
	u o e -> from (into (u i e) b) (from (from i o) b)
o'a = o @into @from `compose` a @from @from

a'o :: forall from into u o e i a .
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
	Castable Straight into ((T'TT'I tt t) a) =>
	Castable Opposite into (I a) =>
	from (t a) o -> into a (tt o)
lj from = fo from
	`compose` uw @into
	`compose` component @Straight @from @into @I @(tt `T'TT'I` t)
	`compose` wrap @into

_lj :: forall from into t tt e ee a o .
	Adjoint Functor from into (U_I_II t e) (U_I_II tt ee) =>
	Castable Straight into ((T'TT'I (U_I_II tt ee) (U_I_II t e)) a) =>
	Castable Straight into (U_I_II tt ee o) =>
	Castable Opposite into (I a) =>
	Castable Straight from (U_I_II t e a) =>
	from (t e a) o -> into a (tt ee o)
_lj from = uw @into @(U_I_II tt _ _)
	`compose` fo (from `compose` uw @from @(U_I_II t _ _))
	`compose` uw @into @(T'TT'I _ _ _)
	`compose` component @Straight @from @into @I @(U_I_II tt ee `T'TT'I` U_I_II t e)
	`compose` wrap @into

rj :: forall from into t tt a o .
	Adjoint Functor from into t tt =>
	Castable Opposite from ((T'TT'I t tt) o) =>
	Castable Straight from (I o) =>
	into a (tt o) -> from (t a) o
rj from = uw @from @(I _)
	`compose` component @Straight @into @from @(t `T'TT'I` tt) @I
	`compose` wrap @from @((t `T'TT'I` tt) _)
	`compose` fo @into @from from

_rj :: forall from into t tt e ee a o .
	Adjoint Functor from into (U_I_II t ee) (U_I_II tt e) =>
	Castable Opposite from ((T'TT'I (U_I_II t ee) (U_I_II tt e)) o) =>
	Castable Straight from (I o) =>
	Castable Opposite from (U_I_II t ee a) =>
	Castable Opposite into (U_I_II tt e o) =>
	into a (tt e o) -> from (t ee a) o
_rj from = uw @from
	`compose` component @Straight @into @from @(U_I_II t ee `T'TT'I` U_I_II tt e) @I
	`compose` wrap @from @((U_I_II t ee `T'TT'I` U_I_II tt e) _)
	`compose` fo (wrap @into @(U_I_II tt e _) `compose` from)
	`compose` wrap @from @(U_I_II t ee _)

lm' :: forall from into i o oo .
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
lm' from_left from_that =
	_i (semifunctor @Straight (wrapped (that @Straight from_that))) `compose`
	i_ (semifunctor @Straight (wrapped (left @Straight from_left))) `compose`
	wrapped (map @Straight @Straight @from @into @I @(Both (Product into)) identity) `compose`
	wrapped (map @Straight @Straight @from @into @I @(Both (Product into)) identity)

lm :: forall o oo .
	Limit Straight (->) (->) =>
	Covariant Functor (->) (->) (That (Product (->)) o) =>
	Covariant Functor (->) (->) (This (Product (->)) (Product (->) Unit Unit)) =>
	Castable Straight (->) (Both (Product (->)) (Product (->) Unit Unit)) =>
	Castable Straight (->) (That (Product (->)) o oo) =>
	Castable Opposite (->) (This (Product (->)) Unit Unit) =>
	Castable Opposite (->) (That (Product (->)) Unit Unit) =>
	Castable Straight (->) (Both (Product (->)) Unit) =>
	Castable Straight (->) (This (Product (->)) (Product (->) Unit Unit) o) =>
	Castable Opposite (->) (This (Product (->)) (Product (->) Unit Unit) (Product (->) Unit Unit)) =>
	Wrapper (->) (That (Product (->)) o (Product (->) Unit Unit)) =>
	(forall e . Wrapper (->) (I e)) =>
	Castable Opposite (->) ((->) Unit o) =>
	Castable Opposite (->) ((->) Unit oo) =>
	Castable Straight (->) ((->) Unit (Product (->) o oo)) =>
	Supertype ((->) Unit o) -> Supertype ((->) Unit oo) -> Supertype ((->) Unit (Product (->) o oo))
lm from_left from_that = unwrap /
	_i (semifunctor @Straight (wrapped (that @Straight (wrap @_ @((->) Unit oo) from_that)))) `compose`
	i_ (semifunctor @Straight (wrapped (left @Straight (wrap @_ @((->) Unit o) from_left)))) `compose`
	wrapped (map @Straight @Straight @(->) @(->) @I @(Both (Product (->))) identity) `compose`
	wrapped (map @Straight @Straight @(->) @(->) @I @(Both (Product (->))) identity)

ml' :: forall from into i o oo .
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
ml' from_left from_that =
	wrapped (map @Opposite @Opposite @from @into @I @(Both (Sum into)) identity) `compose`
	wrapped (map @Opposite @Opposite @from @into @I @(Both (Sum into)) identity) `compose`
	i_ (semifunctor @Straight (wrapped (left @Opposite from_left))) `compose`
	_i (semifunctor @Straight (wrapped (that @Opposite from_that)))

pp :: forall e ee t .
	Covariant Monoidal Functor Arrow LM LM t =>
	t e `LM` t ee -> t (e `LM` ee)
pp = monoidal @Straight @Arrow @t @LM @LM identity identity

pp'pp :: forall e ee t tt .
	Covariant Monoidal Functor Arrow LM LM t =>
	Covariant Monoidal Functor Arrow LM LM tt =>
	t (tt e) `LM` t (tt ee) -> t (tt (e `LM` ee))
pp'pp = monoidal @Straight @Arrow @t @LM @LM identity
	(monoidal @Straight @Arrow @tt @LM @LM identity identity)

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

uw'uw'uw :: forall into a .
	Precategory into =>
	Castable Straight into a =>
	Castable Straight into (Supertype a) =>
	Castable Straight into (Supertype (Supertype a)) =>
	into a (Supertype (Supertype (Supertype a)))
uw'uw'uw = uw @into `compose` uw @into `compose` uw @into

o'yokl :: forall from into t tt a o e .
	Covariant Functor (->) into tt =>
	Covariant Functor (->) into t =>
	Covariant Functor into into t =>
	Covariant Yoneda Functor from into t =>
	Covariant Yoneda Functor into into (U_I_II into (from a (tt o))) =>
	Mapping Straight Straight (->) into (T'TT'I t tt) t =>
	Castable Opposite into (U_I_II from a (tt o)) =>
	(forall ee . Wrapper into (U_I_II into ee e)) =>
	(forall ee . Wrapper into (T'TT'I t tt ee)) =>
	t a -> into (into (t o) e) (into (from a (tt o)) e)
o'yokl = o `compose` yokl @from @into @tt @t

a'yokl :: forall from into t tt a o e .
	Covariant Functor (->) into tt =>
	Covariant Functor (->) into t =>
	Covariant Functor into into tt =>
	Covariant Functor from into t =>
	Covariant Functor from into tt =>
	Covariant Yoneda Functor into into (U_I_II into (from a (tt o))) =>
	Contravariant Yoneda Functor from into (U_II_I into (tt o)) =>
	Mapping Straight Straight from into (T'TT'I tt t) tt =>
	Castable Opposite into (Straight from a (tt o)) =>
	Castable Straight into (Opposite into (tt o) e) =>
	Castable Opposite into (Opposite from (tt a) e) =>
	(forall ee . Wrapper into (T'TT'I tt t ee)) =>
	from a (t o) -> into (from e (tt a)) (into e (tt o))
a'yokl = a `compose` fokl @from @into @tt @t

lm''pp :: forall from t i o oo .
	Category from =>
	Limit Straight from (->) =>
	Covariant Functor (->) (->) (That (LM) o) =>
	Covariant Functor (->) (->) (This (LM) (LM i i)) =>
	Covariant Monoidal Functor Arrow LM LM t =>
	Castable Straight (->) (Both (LM) (LM i i)) =>
	Castable Straight (->) (That (LM) o oo) =>
	Castable Opposite (->) (This (LM) i i) =>
	Castable Opposite (->) (That (LM) i i) =>
	Castable Straight (->) (Both (LM) i) =>
	Castable Straight (->) (This (LM) (LM i i) o) =>
	Castable Opposite (->) (This (LM) (LM i i) (LM i i)) =>
	Wrapper (->) (That (LM) o (LM i i)) =>
	(forall e . Wrapper (->) (I e)) =>
	from i (t o) -> from i (t oo) -> i -> t (LM o oo)
lm''pp from_left from_that = pp `compose`
	_i (semifunctor @Straight (wrapped (that @Straight from_that))) `compose`
	i_ (semifunctor @Straight (wrapped (left @Straight from_left))) `compose`
	wrapped (map @Straight @Straight @from @(->) @I @(Both (LM)) identity) `compose`
	wrapped (map @Straight @Straight @from @(->) @I @(Both (LM)) identity)

lm'pp :: forall o oo t .
	Covariant Monoidal Functor Arrow LM LM t =>
	t o -> t oo -> t (o `LM` oo)
lm'pp from_left from_that = pp (lm from_left from_that)

lm'pp'pp :: forall o oo t tt .
	Covariant Monoidal Functor Arrow LM LM t =>
	Covariant Monoidal Functor Arrow LM LM tt =>
	t (tt o) -> t (tt oo) -> t (tt (o `LM` oo))
lm'pp'pp from_left from_that = pp'pp (lm from_left from_that)

-- TODO: generalize
pp'yo :: forall from e ee r t .
	Covariant Monoidal Functor from LM LM t =>
	t e `LM` t ee -> from (e `LM` ee) r -> t r
pp'yo x f = monoidal @Straight @from @t @LM @LM identity f x

-- TODO: generalize
pp'yokl :: forall e ee from into t tt o .
	Covariant Monoidal Functor Arrow LM LM t =>
	Covariant Yoneda Functor from into t =>
	Component Natural Arrow into (T'TT'I t tt) t =>
	Castable Opposite into (Straight from (e `LM` ee) (tt o)) =>
	Castable Opposite into (T'TT'I t tt o) =>
	t e `LM` t ee -> into (from (e `LM` ee) (tt o)) (t o)
pp'yokl = yokl @from @into `compose` pp

-- TODO: generalize
pp'pp'yo :: forall from e ee r t tt .
	Covariant Monoidal Functor Arrow LM LM t =>
	Covariant Monoidal Functor from LM LM tt =>
	t (tt e) `LM` t (tt ee) -> from (e `LM` ee) r -> t (tt r)
pp'pp'yo x f = monoidal @Straight @Arrow @t @LM @LM identity
	(monoidal @Straight @from @tt @LM @LM identity f) x

jt :: forall into f g e .
	Component Natural (->) into (f `T'TT'I` g) (f `J` g) =>
	Castable Opposite into ((f `T'TT'I` g) e) =>
	into (f (g e)) ((f `J` g) e)
jt = component @Straight @(->) @into @(f `T'TT'I` g) @(f `J` g) @e
	`compose` wrap @into @((f `T'TT'I` g) e)

-- TODO: generalize
pp'pp'jt :: forall e ee t tt .
	Component Natural (->) (->) (t `T'TT'I` tt) (t `J` tt) =>
	Covariant Monoidal Functor (->) LM LM t =>
	Covariant Monoidal Functor (->) LM LM tt =>
	t (tt e) `LM` t (tt ee) -> (t `J` tt) (e `LM` ee)
pp'pp'jt = jt `compose` monoidal @Straight @Arrow @t @LM @LM identity
	(monoidal @Straight @(->) @tt @LM @LM identity identity)

-- TODO: generalize
pp'pp'jt'yokl :: forall from into e ee t tt ttt o .
	Covariant Yoneda Functor from into t =>
	Covariant Yoneda Functor from into (t `J` tt) =>
	Component Natural (->) (->) (t `T'TT'I` tt) (t `J` tt) =>
	Component Natural (->) into (T'TT'I (t `J` tt) ttt) (t `J` tt) =>
	Covariant Monoidal Functor (->) LM LM t =>
	Covariant Monoidal Functor (->) LM LM tt =>
	Castable Opposite into (Straight from (e `LM` ee) (ttt o)) =>
	Castable Opposite into (T'TT'I (J t tt) ttt o) =>
	t (tt e) `LM` t (tt ee) -> into (from (e `LM` ee) (ttt o)) ((t `J` tt) o)
pp'pp'jt'yokl = yokl @from @into `compose` pp'pp'jt

rwr'yo_ :: forall into w o u e ee .
	Covariant Endo Semi Functor into (U_II_I u o) =>
	Castable Straight into (U_II_I u o ee) =>
	Castable Opposite into (U_II_I u o e) =>
	Castable Opposite into (w u ee o) =>
	Castable Straight into (w u e o) =>
	Castable Opposite Arrow (into Unit ee) =>
	(Supertype (w u e o) ~ u e o) =>
	(Supertype (w u ee o) ~ u ee o) =>
	into e ee -> into (w u e o) (w u ee o)
rwr'yo_ = rwr `compose` i_ `compose` fo

yokl'rwr'yo_ :: forall into w t o u e ee .
	Covariant Yoneda Functor into (->) t =>
	Covariant Endo Semi Functor (->) t =>
	Covariant Endo Semi Functor (->) (w u ee) =>
	Covariant Endo Semi Functor into (U_II_I u o) =>
	Component Natural (->) (->) (T'TT'I t (w u ee)) t =>
	(Supertype (w u e o) ~ u e o) =>
	(Supertype (w u ee o) ~ u ee o) =>
	Castable Opposite Arrow (into Unit ee) =>
	Castable Opposite into (U_II_I u o e) =>
	Castable Opposite into (w u ee o) =>
	Castable Straight into (U_II_I u o ee) =>
	Castable Straight into (w u e o) =>
	t (w u e o) -> into e ee -> t o
yokl'rwr'yo_ x f = yokl @into @_ @(w u ee) @t x
	(rwr'yo_ @into @w @o @u @e @ee f)

rwr'yu_ :: forall into w o u e ee .
	Covariant Endo Semi Functor into (U_II_I u o) =>
	Mapping Constant Straight into into (U_II_I u o) (U_II_I u o) =>
	Castable Straight into (U_II_I u o ee) =>
	Castable Opposite into (U_II_I u o e) =>
	Castable Opposite into (w u ee o) =>
	Castable Straight into (w u e o) =>
	Castable Opposite Arrow (into Unit ee) =>
	(Supertype (w u e o) ~ u e o) =>
	(Supertype (w u ee o) ~ u ee o) =>
	Supertype (into Unit ee) -> into (w u e o) (w u ee o)
rwr'yu_ = rwr `compose` i_ `compose` fu

-- TODO: find a way to generalize
yokl'rwr'yu_ :: forall w t o u e ee .
	Covariant Yoneda Functor (->) (->) t =>
	Covariant Endo Semi Functor (->) t =>
	Covariant Endo Semi Functor (->) (w u ee) =>
	Covariant Endo Semi Functor (->) (U_II_I u o) =>
	Mapping Constant Straight (->) (->) (U_II_I u o) (U_II_I u o) =>
	Component Natural (->) (->) (T'TT'I t (w u ee)) t =>
	(Supertype (w u e o) ~ u e o) =>
	(Supertype (w u ee o) ~ u ee o) =>
	Castable Opposite Arrow ((->) Unit ee) =>
	Castable Opposite (->) (U_II_I u o e) =>
	Castable Opposite (->) (w u ee o) =>
	Castable Straight (->) (U_II_I u o ee) =>
	Castable Straight (->) (w u e o) =>
	t (w u e o) -> Supertype (Unit -> ee) -> t o
yokl'rwr'yu_ x f = yokl @(->) @_ @(w u ee) @t x
	(rwr'yu_ @(->) @w @o @u @e @ee f)

-- TODO: generalize
yokl'uw'yokl :: forall t tt ttt a aa o .
	Covariant Yoneda Functor (->) (->) t =>
	Covariant Endo Semi Functor (->) t =>
	Covariant Endo Semi Functor (->) tt =>
	Covariant Endo Semi Functor (->) ttt =>
	Component Natural (->) (->) (T'TT'I t tt) t =>
	Component Natural (->) (->) (T'TT'I t ttt) t =>
	Castable Straight (->) a =>
	(Supertype a ~ tt aa) =>
	t a -> (aa -> ttt o) -> t o
yokl'uw'yokl x = yokl @(->) @(->) @ttt @t
	(yokl @(->) @(->) @tt @t x unwrap)

-- TODO: effects are executed in reverse order, we can use it
-- to alter execution order, in Scrolling List for example
fc :: forall into t a o .
	Covariant Endo Semi Functor (->) t =>
	Covariant Endo Semi Functor (->) (U_I_II into a) =>
	Adjoint Functor (->) (->) (That LM (t a)) (That into (t a)) =>
	Adjoint Functor (->) (->) (That LM a) (That into a) =>
	Adjoint Functor (->) (->) (That LM (t a `LM` t (into a o))) (That (->) (t a `LM` t (into a o))) =>
	Monoidal Straight Functor into LM LM t =>
	t (into a o) -> into (t a) (t o)
fc = uw @(->) @(That into (t a) _)
	`compose` (fo @(->) @(->) `compose` fo @(->) @(->))
		(rj @(->) @(->) (wrap @_ @(That _ _ _)) `compose` wrap @_ @(That _ _ _))
	`compose` lj @(->) @(->) @(That LM (t a)) @(That into _)
		(monoidal' @Straight @into @(->) @t @LM @LM identity (wrap identity)
			`compose` uw @(->) @(That LM (t a) (t (into a o))))

cc :: forall t e ee .
	Adjoint Functor (->) (->) (That LM (t e `LM` t ee)) (That (->) (t e `LM` t ee)) =>
	Monoidal Straight Functor (->) LM LM t =>
	t e -> t ee -> t (e `LM` ee)
cc e ee = monoidal'
	@Straight @(->) @(->) @t @LM @LM identity
	(wrap @(->) identity)
	(e `lm` ee)
