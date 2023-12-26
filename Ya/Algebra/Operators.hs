{-# LANGUAGE AllowAmbiguousTypes #-}
module Ya.Algebra.Operators where

import Ya.Algebra.Abstract
import Ya.Algebra.Definition
import Ya.Algebra.Instances ()

infixl 9 `i`, `u`, `o`, `a`, `a_a`, `o_a`, `o_rw_o`, `a_o`, `a_yokl`
infixl 8 `i_i`, `u_u`, `yi`, `yo`, `ya`, `yu`, `fo`, `fa`, `fu`, `lj`, `rj`, `ro`, `ra`, `dp`, `ds`, `fr`, `lm`, `rf`, `cc`, `fc`, `jt`, `dp_yo`, `dp_dp`, `yo_yo`, `fo_fo`, `rw_rw`, `fr_dp`, `lm_dp`, `lm_ds`, `fo_fo_fo`, `dp_dp_yo`, `dp_yokl`, `dp_dp_jt`, `dp_dp_jt_yokl`, `rw_rw_rw`, `lm_dp_dp`
infixl 7 `i_i_i`, `u_u_u`, `yai`, `fio`, `foi`, `yoi`, `fai`, `yui`, `ilj`, `irj`, `fio_fo`, `w_rw`, `rw_w`, `rwr_yoi`, `rwr_yui`
infixl 6 `i_i_i_i`, `u_u_u_u`, `yi_yi`, `yi_yu`, `yi_rf`, `fokl`, `yokl`, `yukl`, `yokl_yoklKL`, `yokl_u`, `yukl_u`, `yokl_u_u`, `yukl_u_u`, `yokl_u_u_u`, `yukl_u_u_u`, `yukl_u_u_u_u`, `yokl_u_u_u_u`, `yukl_u_u_u_u_u_u`, `yokl_u_u_u_u_u_u`, `yukl_u_u_u_u_u`, `yokl_rwr_yoi`, `yokl_rwr_yui`, `yokl_u_u_u_u_u`, `yokl_rw_yokl`
infixl 5 `i_i_i_i_i`, `u_u_u_u_u`, `yiokl`
infixl 4 `i_i_i_i_i_i`, `u_u_u_u_u_u`, `yi_yi_yi`, `yi_yi_yu`, `yi_yi_rf`, `yoklKL`, `yoklKL_yokl`, `yoklKL_yoklKL`, `yi_yukl`
infixl 3 `i_i_i_i_i_i_i`, `u_u_u_u_u_u_u`
infixl 2 `i_i_i_i_i_i_i_i`, `u_u_u_u_u_u_u_u`, `yi_yi_yi_yi`, `yi_yi_yi_yu`, `yi_yi_yukl`
infixl 1 `i_i_i_i_i_i_i_i_i`, `u_u_u_u_u_u_u_u_u`
infixl 0 `i_i_i_i_i_i_i_i_i_i`, `u_u_u_u_u_u_u_u_u_u`, `yi_yi_yi_yi_yi`, `yi_yi_yi_yukl`

i, i_i, i_i_i, i_i_i_i, i_i_i_i_i, i_i_i_i_i_i, i_i_i_i_i_i_i,
	i_i_i_i_i_i_i_i, i_i_i_i_i_i_i_i_i, i_i_i_i_i_i_i_i_i_i :: Category into => into e e
i_i_i_i_i_i_i_i_i_i = identity
i_i_i_i_i_i_i_i_i = identity
i_i_i_i_i_i_i_i = identity
i_i_i_i_i_i_i = identity
i_i_i_i_i_i = identity
i_i_i_i_i = identity
i_i_i_i = identity
i_i_i = identity
i_i = identity
i = identity

yi_yi_yi_yi_yi, yi_yi_yi_yi, yi_yi_yi, yi_yi, yi
	:: Category into => into e e
yi_yi_yi_yi_yi = identity
yi_yi_yi_yi = identity
yi_yi_yi = identity
yi_yi = identity
yi = identity

fo :: forall from into t a o .
	Covariant Semi Functor from into t =>
	from a o -> into (t a) (t o)
fo = map @Straight @Straight

fa :: forall from into t a o .
	Contravariant Semi Functor from into t =>
	from a o -> into (t o) (t a)
fa = map @Opposite @Straight

fu :: forall into t a o .
	Covariant Semi Functor into into t =>
	Mapping Constant Straight into into t t =>
	Castable Opposite Arrow (into Unit o) =>
	Supertype (into Unit o) -> into (t a) (t o)
fu = map @Constant @Straight @into @into `compose` wrap @Arrow @(into Unit o)

fokl :: forall from into t tt a o .
	Component Natural from into (T_TT_I t tt) t =>
	Castable Opposite into (T_TT_I t tt o) =>
	from a (tt o) -> into (t a) (t o)
fokl from = component @Straight @from @into @(t `T_TT_I` tt) @t
	`compose` wrap `compose` fo from

foklKL :: forall from into t tt a o .
	Covariant Semi Functor from into t =>
	Component Natural from into (T_TT_I t tt) (TT_T_I t tt) =>
	Castable Opposite into (T_TT_I t tt o) =>
	Castable Straight into (TT_T_I t tt o) =>
	from a (tt o) -> into (t a) (tt (t o))
foklKL from = wrapped
	(component @Straight @from @into @(t `T_TT_I` tt) @(t `TT_T_I` tt))
	`compose` fo from

yo :: forall from into t a o .
	Precategory into =>
	Covariant Yoneda Functor from into t =>
	Castable Opposite into (U_I_II from a o) =>
	t a -> into (from a o) (t o)
yo x = yoneda @Straight @Functor x

yoi :: forall from into t e a o .
	Precategory into =>
	Covariant Yoneda Functor from into (This t e) =>
	Castable Opposite into (Straight from a o) =>
	Castable Straight into (This t e o) =>
	t a e -> into (from a o) (t o e)
yoi x = compose rw (yoneda @Straight @Functor @from @into @(This t e) (wrap x))

yu, yi_yu, yi_yi_yu, yi_yi_yi_yu  :: forall into t a o .
	Covariant Yoneda Functor into into t =>
	Covariant Endo Semi Functor (->) t =>
	Castable Opposite into (into Unit o) =>
	Castable Opposite into (U_I_II into Unit o) =>
	t a -> into (Supertype (into Unit o)) (t o)
yu x = yoneda @U_I_II @Functor (fu @Arrow Unit x)
	`compose` wrap @into @(into Unit o)
yi_yu x = yoneda @U_I_II @Functor (fu @Arrow Unit x)
	`compose` wrap @into @(into Unit o)
yi_yi_yu x = yoneda @U_I_II @Functor (fu @Arrow Unit x)
	`compose` wrap @into @(into Unit o)
yi_yi_yi_yu x = yoneda @U_I_II @Functor (fu @Arrow Unit x)
	`compose` wrap @into @(into Unit o)

yui :: forall into t e a o .
	Covariant Yoneda Functor into into (U_II_I t e) =>
	Covariant Endo Semi Functor (->) (U_II_I t e) =>
	Castable Opposite into (into Unit o) =>
	Castable Opposite into (U_I_II into Unit o) =>
	Castable Straight into (U_II_I t e o) =>
	t a e -> into (Supertype (into Unit o)) (t o e)
yui x = rw @into @(U_II_I t e _) `compose` yu @into (wrap @(->) @(U_II_I t e _) x)

yo_yo :: forall from into t tt a o .
	Precategory into =>
	Covariant Functor from from tt =>
	Covariant Yoneda Functor from into t =>
	Contravariant Endo Semi Functor Arrow (U_II_I into (t (tt o))) =>
	Castable Opposite into (U_I_II from (tt a) (tt o)) =>
	t (tt a) -> into (from a o) (t (tt o))
yo_yo x = fai fo (yo @from @into x)

-- TODO: yo_yo : t (tt a) -> into (from a b) (tt a -> into (from b o) (t (tt o)))

ya :: forall from into t a o .
	Precategory into =>
	Contravariant Yoneda Functor from into t =>
	Castable Opposite into (Opposite from a o) =>
	t a -> into (from o a) (t o)
ya = yoneda @Opposite @Functor

yai :: forall from into t e a o .
	Precategory into =>
	Contravariant Yoneda Functor from into (This t e) =>
	Castable Opposite into (Opposite from a o) =>
	Castable Straight into (This t e o) =>
	t a e -> into (from o a) (t o e)
yai x = compose rw (yoneda @Opposite @Functor @from @into @(This t e) (wrap x))

yokl, yokl_u, yokl_u_u, yokl_u_u_u, yokl_u_u_u_u, yokl_u_u_u_u_u, yokl_u_u_u_u_u_u :: forall from into tt t a o .
	Component Natural Arrow into (T_TT_I t tt) t =>
	Covariant Yoneda Functor from into t =>
	Castable Opposite into (Straight from a (tt o)) =>
	Castable Opposite into (T_TT_I t tt o) =>
	t a -> into (from a (tt o)) (t o)
yokl x = component @Straight @Arrow @into @(T_TT_I t tt)
	`compose` wrap @into @(T_TT_I t tt _)
	`compose` yoneda @Straight @Functor @from x
yokl_u x = component @Straight @Arrow @into @(T_TT_I t tt)
	`compose` wrap @into @(T_TT_I t tt _)
	`compose` yoneda @Straight @Functor @from x
yokl_u_u x = component @Straight @Arrow @into @(T_TT_I t tt)
	`compose` wrap @into @(T_TT_I t tt _)
	`compose` yoneda @Straight @Functor @from x
yokl_u_u_u x = component @Straight @Arrow @into @(T_TT_I t tt)
	`compose` wrap @into @(T_TT_I t tt _)
	`compose` yoneda @Straight @Functor @from x
yokl_u_u_u_u x = component @Straight @Arrow @into @(T_TT_I t tt)
	`compose` wrap @into @(T_TT_I t tt _)
	`compose` yoneda @Straight @Functor @from x
yokl_u_u_u_u_u x = component @Straight @Arrow @into @(T_TT_I t tt)
	`compose` wrap @into @(T_TT_I t tt _)
	`compose` yoneda @Straight @Functor @from x
yokl_u_u_u_u_u_u x = component @Straight @Arrow @into @(T_TT_I t tt)
	`compose` wrap @into @(T_TT_I t tt _)
	`compose` yoneda @Straight @Functor @from x

yukl, yukl_u, yukl_u_u, yukl_u_u_u, yukl_u_u_u_u, yukl_u_u_u_u_u, yukl_u_u_u_u_u_u, yi_yukl, yi_yi_yukl, yi_yi_yi_yukl
	:: forall into tt t a o .
	Covariant Endo Semi Functor (->) t =>
	Component Natural Arrow into (T_TT_I t tt) t =>
	Covariant Yoneda Functor into into t =>
	Castable Opposite into (into Unit (tt o)) =>
	Castable Opposite into (Straight into Unit (tt o)) =>
	Castable Opposite into (T_TT_I t tt o) =>
	t a -> into (Supertype (into Unit (tt o))) (t o)
yukl x = component @Straight @Arrow @into @(T_TT_I t tt)
	`compose` wrap @into @(T_TT_I t tt _)
	`compose` yoneda @Straight @Functor (fu @Arrow Unit x)
	`compose` wrap @into @(into Unit (tt o))
yukl_u x = component @Straight @Arrow @into @(T_TT_I t tt)
	`compose` wrap @into @(T_TT_I t tt _)
	`compose` yoneda @Straight @Functor (fu @Arrow Unit x)
	`compose` wrap @into @(into Unit (tt o))
yukl_u_u x = component @Straight @Arrow @into @(T_TT_I t tt)
	`compose` wrap @into @(T_TT_I t tt _)
	`compose` yoneda @Straight @Functor (fu @Arrow Unit x)
	`compose` wrap @into @(into Unit (tt o))
yukl_u_u_u x = component @Straight @Arrow @into @(T_TT_I t tt)
	`compose` wrap @into @(T_TT_I t tt _)
	`compose` yoneda @Straight @Functor (fu @Arrow Unit x)
	`compose` wrap @into @(into Unit (tt o))
yukl_u_u_u_u x = component @Straight @Arrow @into @(T_TT_I t tt)
	`compose` wrap @into @(T_TT_I t tt _)
	`compose` yoneda @Straight @Functor (fu @Arrow Unit x)
	`compose` wrap @into @(into Unit (tt o))
yukl_u_u_u_u_u x = component @Straight @Arrow @into @(T_TT_I t tt)
	`compose` wrap @into @(T_TT_I t tt _)
	`compose` yoneda @Straight @Functor (fu @Arrow Unit x)
	`compose` wrap @into @(into Unit (tt o))
yukl_u_u_u_u_u_u x = component @Straight @Arrow @into @(T_TT_I t tt)
	`compose` wrap @into @(T_TT_I t tt _)
	`compose` yoneda @Straight @Functor (fu @Arrow Unit x)
	`compose` wrap @into @(into Unit (tt o))
yi_yukl x = component @Straight @Arrow @into @(T_TT_I t tt)
	`compose` wrap @into @(T_TT_I t tt _)
	`compose` yoneda @Straight @Functor (fu @Arrow Unit x)
	`compose` wrap @into @(into Unit (tt o))
yi_yi_yukl x = component @Straight @Arrow @into @(T_TT_I t tt)
	`compose` wrap @into @(T_TT_I t tt _)
	`compose` yoneda @Straight @Functor (fu @Arrow Unit x)
	`compose` wrap @into @(into Unit (tt o))
yi_yi_yi_yukl x = component @Straight @Arrow @into @(T_TT_I t tt)
	`compose` wrap @into @(T_TT_I t tt _)
	`compose` yoneda @Straight @Functor (fu @Arrow Unit x)
	`compose` wrap @into @(into Unit (tt o))

yoklKL :: forall from into tt t a o .
	Component Natural from into (T_TT_I t tt) (TT_T_I t tt) =>
	Covariant Yoneda Functor from into t =>
	Castable Opposite into (Straight from a (tt o)) =>
	Castable Straight into (TT_T_I t tt o) =>
	Castable Opposite into (T_TT_I t tt o) =>
	t a -> into (from a (tt o)) (tt (t o))
yoklKL x = rw @into @(TT_T_I t tt _)
	`compose` component @Straight @from @into @(T_TT_I t tt) @(TT_T_I t tt)
	`compose` wrap @into @(T_TT_I t tt _)
	`compose` yoneda @Straight @Functor @from x

yiokl :: forall from into tt t i a o .
	Component Natural from into (T_TT_I (U_I_II t i) tt) (U_I_II t i) =>
	Covariant Yoneda Functor from into (U_I_II t i) =>
	Castable Opposite into (U_I_II from a (tt o)) =>
	Castable Straight into (U_I_II t i o) =>
	Castable Opposite into (T_TT_I (U_I_II t i) tt o) =>
	t i a -> into (from a (tt o)) (t i o)
yiokl x = rw @into @(U_I_II t i o)
	`compose` component @Straight @from @into @(T_TT_I (U_I_II t i) tt)
	`compose` wrap @into @(T_TT_I (U_I_II t i) tt _)
	`compose` yoneda @Straight @Functor @from (U_I_II x)

yokl_yoklKL :: forall from into t tt ttt a o .
	Covariant Yoneda Functor from into t =>
	Covariant Endo Semi Functor from tt =>
	Covariant Endo Semi Functor from ttt =>
	Contravariant Endo Semi Functor (->) (U_II_I into (t (ttt o))) =>
	Component Natural (->) into (T_TT_I t tt) t =>
	Component Natural from from (T_TT_I ttt tt) (TT_T_I ttt tt) =>
	Castable Opposite into (That from (ttt a) (tt (ttt o))) =>
	Castable Opposite from (T_TT_I ttt tt o)=>
	Castable Straight from (TT_T_I ttt tt o) =>
	Castable Opposite into (T_TT_I t tt (ttt o)) =>
	t (ttt a) -> into (from a (tt o)) (t (ttt o))
yokl_yoklKL x = fai foklKL (yokl @from @into x)

yoklKL_yokl :: forall from into t tt ttt a o .
	Covariant Yoneda Functor from into t =>
	Covariant Endo Semi Functor from tt =>
	Covariant Endo Semi Functor from ttt =>
	Contravariant Endo Semi Functor (->) (U_II_I into (ttt (t o))) =>
	Component Natural from from (T_TT_I ttt tt) ttt =>
	Component Natural from into (T_TT_I t ttt) (TT_T_I t ttt) =>
	Castable Opposite into (That from (ttt a) (ttt o)) =>
	Castable Straight into (TT_T_I t ttt o) =>
	Castable Opposite into (T_TT_I t ttt o) =>
	Castable Opposite from (T_TT_I ttt tt o) =>
	t (ttt a) -> into (from a (tt o)) (ttt (t o))
yoklKL_yokl x = fai fokl (yoklKL @from @into x)

yoklKL_yoklKL :: forall from into t tt ttt a o .
	Covariant Yoneda Functor from into t =>
	Covariant Endo Semi Functor from tt =>
	Covariant Endo Semi Functor from ttt =>
	Component Natural from into (T_TT_I t ttt) (TT_T_I t ttt) =>
	Component Natural from from (T_TT_I tt ttt) (TT_T_I tt ttt) =>
	Contravariant Endo Semi Functor (->) (U_II_I into (ttt (t (tt o)))) =>
	Castable Opposite from (T_TT_I tt ttt o) =>
	Castable Straight from (TT_T_I tt ttt o) =>
	Castable Straight into (TT_T_I t ttt (tt o)) =>
	Castable Opposite into (T_TT_I t ttt (tt o)) =>
	Castable Opposite into (Straight from (tt a) (ttt (tt o))) =>
	t (tt a) -> into (from a (ttt o)) (ttt (t (tt o)))
yoklKL_yoklKL x = fai foklKL (yoklKL @from @into x)

fo_fo :: forall from into t tt a o .
	Covariant Semi Functor from into tt =>
	Covariant Endo Semi Functor into t =>
	from a o -> into (t (tt a)) (t (tt o))
fo_fo from = fo @into @into (fo @from @into from)

fo_fo_fo :: forall from into t tt h a o .
	Covariant Semi Functor from into h =>
	Covariant Endo Semi Functor into tt =>
	Covariant Endo Semi Functor into t =>
	from a o -> into (t (tt (h a))) (t (tt (h o)))
fo_fo_fo from = fo @into @into (fo @into @into (fo @from @into from))

fio :: forall from into t a o i .
	Covariant Semi Functor from into (U_I_II t i) =>
	Wrapper into (U_I_II t i a) =>
	Wrapper into (U_I_II t i o) =>
	from a o -> into (t i a) (t i o)
fio from = rw `compose` fo @_ @_ @(U_I_II _ _) from `compose` wrap

foi :: forall from into t a o i .
	Covariant Semi Functor from into (U_II_I t i) =>
	Wrapper into (U_II_I t i a) =>
	Wrapper into (U_II_I t i o) =>
	from a o -> into (t a i) (t o i)
foi from = rw `compose` fo @_ @_ @(U_II_I _ _) from `compose` wrap

fai :: forall from into t a o i .
	Contravariant Semi Functor from into (U_II_I t i) =>
	Wrapper into (U_II_I t i a) =>
	Wrapper into (U_II_I t i o) =>
	from a o -> into (t o i) (t a i)
fai from = rw `compose` fa @_ @_ @(U_II_I _ _) from `compose` wrap

fio_fo :: forall from into t tt e a o .
	Covariant Semi Functor into into (U_I_II t e) =>
	Covariant Semi Functor from into tt =>
	Wrapper into (U_I_II t e (tt a)) =>
	Wrapper into (U_I_II t e (tt o)) =>
	from a o -> into (t e (tt a)) (t e (tt o))
fio_fo from = fio @into @into (fo @from @into from)

o :: forall from into u i a o .
	Precategory into =>
	Covariant Yoneda Functor from into (U_I_II u i) =>
	Castable Opposite into (U_I_II from a o) =>
	Castable Straight into (U_I_II u i o) =>
	u i a -> into (from a o) (u i o)
o x = rw `compose` yo @from @into @(U_I_II u _) (U_I_II x)

a :: forall into from u e a o .
	Precategory into =>
	Contravariant Yoneda Functor from into (U_II_I u e) =>
	Castable Opposite into (Opposite from a o) =>
	Castable Straight into (Opposite u e o) =>
	u a e -> into (from o a) (u o e)
a x = rw `compose` ya @from @into @(U_II_I u _) (U_II_I x)

a_a :: forall from into u i o e b .
	Precategory into =>
	Contravariant Yoneda Functor from from (U_II_I u e) =>
	Contravariant Yoneda Functor from into (U_II_I from (u b e)) =>
	Castable Opposite from (Opposite from o b) =>
	Castable Straight from (Opposite u e b) =>
	Castable Opposite into (Opposite from (from b o) i) =>
	Castable Straight into (Opposite from (u b e) i) =>
	u o e -> into (from i (from b o)) (from i (u b e))
a_a = a @into @from `compose` a @from @from

o_a :: forall from into u i o e b .
	Contravariant Yoneda Functor from from (U_II_I u e) =>
	Covariant Yoneda Functor into from (U_I_II from (from i o)) =>
	Castable Opposite from (U_I_II into (u i e) b) =>
	Castable Straight from (U_I_II from (from i o) b) =>
	Castable Straight from (Opposite u e i) =>
	Castable Opposite from (Opposite from o i) =>
	u o e -> from (into (u i e) b) (from (from i o) b)
o_a = o @into @from `compose` a @from @from

o_rw :: forall from into u e a o .
	Precategory into =>
	Covariant Endo Semi Functor from (That from a) =>
	Covariant Yoneda Functor from into (U_I_II u e) =>
	Contravariant Yoneda Functor from into (U_II_I into (u e (Supertype o))) =>
	Castable Straight into (U_I_II u e o) =>
	Castable Straight from o =>
	Wrapper from (U_I_II from a o) =>
	Wrapper from (U_I_II from a (Supertype o)) =>
	Wrapper into (U_I_II from e (Supertype o)) =>
	Wrapper into (U_I_II from a (Supertype o)) =>
	Wrapper into (U_I_II u e (Supertype o)) =>
	u e a -> into (from a o) (u e (Supertype o))
o_rw x = fai @from (fio @from rw) (o x)

-- TODO: generalize
o_rw_o :: forall from u e a o .
	Covariant Yoneda Functor from (->) (That u e) =>
	Castable Straight from a =>
	u e a -> from (Supertype a) o -> u e o
o_rw_o x xx = x `o`rw @from `o` xx

a_o :: forall from into u o e i a .
	Category into =>
	Contravariant Yoneda Functor from into (U_II_I from (u i e)) =>
	Covariant Yoneda Functor from from (U_I_II u i) =>
	Castable Opposite from (U_I_II from a e) =>
	Castable Straight from (U_I_II u i e) =>
	Castable Straight into (Opposite from (u i e) o) =>
	Castable Opposite into (Opposite from (from a e) o) =>
	u i a -> into (from o (from a e)) (from o (u i e))
a_o = a @into @from `compose` o @from @from

u, u_u, u_u_u, u_u_u_u, u_u_u_u_u, u_u_u_u_u_u, u_u_u_u_u_u_u,
	u_u_u_u_u_u_u_u, u_u_u_u_u_u_u_u_u, u_u_u_u_u_u_u_u_u_u :: forall from into i a o .
	Precategory into =>
	Covariant Yoneda Functor from into (U_1_I from i) =>
	Castable Opposite into (U_I_II from a o) =>
	Castable Straight into (U_I_II from i o) =>
	Castable Opposite (->) (from Unit a) =>
	Castable Straight into (from Unit o) =>
	Castable Straight into (U_1_I from i o) =>
	Supertype (from Unit a) -> into (from a o) (Supertype (from Unit o))
u x = rw `compose` rw `compose` yo @from @into @(U_1_I from _)
	(U_1_I @from @i / wrap @(->) @(from _ _) x)
u_u x = rw `compose` rw `compose` yo @from @into @(U_1_I from _)
	(U_1_I @from @i / wrap @(->) @(from _ _) x)
u_u_u x = rw `compose` rw `compose` yo @from @into @(U_1_I from _)
	(U_1_I @from @i / wrap @(->) @(from _ _) x)
u_u_u_u x = rw `compose` rw `compose` yo @from @into @(U_1_I from _)
	(U_1_I @from @i / wrap @(->) @(from _ _) x)
u_u_u_u_u x = rw `compose` rw `compose` yo @from @into @(U_1_I from _)
	(U_1_I @from @i / wrap @(->) @(from _ _) x)
u_u_u_u_u_u x = rw `compose` rw `compose` yo @from @into @(U_1_I from _)
	(U_1_I @from @i / wrap @(->) @(from _ _) x)
u_u_u_u_u_u_u x = rw `compose` rw `compose` yo @from @into @(U_1_I from _)
	(U_1_I @from @i / wrap @(->) @(from _ _) x)
u_u_u_u_u_u_u_u x = rw `compose` rw `compose` yo @from @into @(U_1_I from _)
	(U_1_I @from @i / wrap @(->) @(from _ _) x)
u_u_u_u_u_u_u_u_u x = rw `compose` rw `compose` yo @from @into @(U_1_I from _)
	(U_1_I @from @i / wrap @(->) @(from _ _) x)
u_u_u_u_u_u_u_u_u_u x = rw `compose` rw `compose` yo @from @into @(U_1_I from _)
	(U_1_I @from @i / wrap @(->) @(from _ _) x)

ro :: forall from into hom t i .
	Covariant (Representable hom) Functor from into t =>
	Castable Straight into (Straight hom (Representation t) i) =>
	into (t i) (hom (Representation t) i)
ro = rw `compose` component @Straight @from @into @t @(Straight hom (Representation t))

ra :: forall from into hom t i .
	Contravariant (Representable hom) Functor from into t =>
	Castable Straight into (Opposite hom (Representation t) i) =>
	into (t i) (hom i (Representation t))
ra = rw `compose` component @Opposite @from @into @t @(Opposite hom (Representation t))

lj :: forall from into t tt a o .
	Adjoint Functor from into t tt =>
	Castable Straight into ((T_TT_I tt t) a) =>
	Castable Opposite into (I a) =>
	from (t a) o -> into a (tt o)
lj from = fo from
	`compose` rw @into
	`compose` component @Straight @from @into @I @(tt `T_TT_I` t)
	`compose` wrap @into

ilj :: forall from into t tt e ee a o .
	Adjoint Functor from into (U_I_II t e) (U_I_II tt ee) =>
	Castable Straight into ((T_TT_I (U_I_II tt ee) (U_I_II t e)) a) =>
	Castable Straight into (U_I_II tt ee o) =>
	Castable Opposite into (I a) =>
	Castable Straight from (U_I_II t e a) =>
	from (t e a) o -> into a (tt ee o)
ilj from = rw @into @(U_I_II tt _ _)
	`compose` fo (from `compose` rw @from @(U_I_II t _ _))
	`compose` rw @into @(T_TT_I _ _ _)
	`compose` component @Straight @from @into @I @(U_I_II tt ee `T_TT_I` U_I_II t e)
	`compose` wrap @into

rj :: forall from into t tt a o .
	Adjoint Functor from into t tt =>
	Castable Opposite from ((T_TT_I t tt) o) =>
	Castable Straight from (I o) =>
	into a (tt o) -> from (t a) o
rj from = rw @from @(I _)
	`compose` component @Straight @into @from @(t `T_TT_I` tt) @I
	`compose` wrap @from @((t `T_TT_I` tt) _)
	`compose` fo @into @from from

irj :: forall from into t tt e ee a o .
	Adjoint Functor from into (U_I_II t ee) (U_I_II tt e) =>
	Castable Opposite from ((T_TT_I (U_I_II t ee) (U_I_II tt e)) o) =>
	Castable Straight from (I o) =>
	Castable Opposite from (U_I_II t ee a) =>
	Castable Opposite into (U_I_II tt e o) =>
	into a (tt e o) -> from (t ee a) o
irj from = rw @from
	`compose` component @Straight @into @from @(U_I_II t ee `T_TT_I` U_I_II tt e) @I
	`compose` wrap @from @((U_I_II t ee `T_TT_I` U_I_II tt e) _)
	`compose` fo (wrap @into @(U_I_II tt e _) `compose` from)
	`compose` wrap @from @(U_I_II t ee _)

fr :: forall from into i o oo .
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
fr from_left from_right =
	_i (map @Straight @Straight (wrapped (right @Straight from_right))) `compose`
	i_ (map @Straight @Straight (wrapped (left @Straight from_left))) `compose`
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
lm from_left from_right = unwrap /
	_i (map @Straight @Straight (wrapped (right @Straight (wrap @_ @((->) Unit oo) from_right)))) `compose`
	i_ (map @Straight @Straight (wrapped (left @Straight (wrap @_ @((->) Unit o) from_left)))) `compose`
	wrapped (map @Straight @Straight @(->) @(->) @I @(Both (Product (->))) identity) `compose`
	wrapped (map @Straight @Straight @(->) @(->) @I @(Both (Product (->))) identity)

rf, yi_rf, yi_yi_rf :: forall from into i o oo .
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
rf from_left from_right =
	wrapped (map @Opposite @Opposite @from @into @I @(Both (Sum into)) identity) `compose`
	wrapped (map @Opposite @Opposite @from @into @I @(Both (Sum into)) identity) `compose`
	i_ (map @Straight @Straight (wrapped (left @Opposite from_left))) `compose`
	_i (map @Straight @Straight (wrapped (right @Opposite from_right)))
yi_rf from_left from_right =
	wrapped (map @Opposite @Opposite @from @into @I @(Both (Sum into)) identity) `compose`
	wrapped (map @Opposite @Opposite @from @into @I @(Both (Sum into)) identity) `compose`
	i_ (map @Straight @Straight (wrapped (left @Opposite from_left))) `compose`
	_i (map @Straight @Straight (wrapped (right @Opposite from_right)))
yi_yi_rf from_left from_right =
	wrapped (map @Opposite @Opposite @from @into @I @(Both (Sum into)) identity) `compose`
	wrapped (map @Opposite @Opposite @from @into @I @(Both (Sum into)) identity) `compose`
	i_ (map @Straight @Straight (wrapped (left @Opposite from_left))) `compose`
	_i (map @Straight @Straight (wrapped (right @Opposite from_right)))

dp :: forall u e ee t .
	Mapping Straight Straight (->) (->)
		(Day Straight (->) u LM t t e ee) t =>
	u (t e) (t ee) -> t (e `LM` ee)
dp = day @Straight @Arrow @t @u @LM identity identity

ds :: forall u e ee t .
	Mapping Straight Straight (->) (->)
		(Day Straight (->) u ML t t e ee) t =>
	u (t e) (t ee) -> t (e `ML` ee)
ds = day @Straight @Arrow @t @u @ML identity identity

dw :: forall u e ee t .
	Mapping Straight Straight (->) (->)
		(Day Straight (->) u MLM t t e ee) t =>
	u (t e) (t ee) -> t (ML e ee `ML` LM e ee)
dw = day @Straight @Arrow @t @u @MLM identity unwrap

dp_dp :: forall u e ee t tt .
	Mapping Straight Straight (->) (->)
		(Day Straight (->) u LM t t (tt e) (tt ee)) t =>
	Mapping Straight Straight (->) (->)
		(Day Straight (->) LM LM tt tt e ee) tt =>
	u (t (tt e)) (t (tt ee)) -> t (tt (e `LM` ee))
dp_dp = day @Straight @Arrow @t @u @LM identity
	(day @Straight @Arrow @tt @LM @LM identity identity)

w_rw :: forall into a o .
	Precategory into =>
	Castable Opposite into o =>
	Castable Straight into a =>
	into (Supertype a) (Supertype o) -> into a o
w_rw into = wrap @into `compose` into `compose` rw @into

rw_w :: forall into a o .
	Precategory into =>
	Castable Opposite into a =>
	Castable Straight into o =>
	into a o -> into (Supertype a) (Supertype o)
rw_w into = rw @into `compose` into `compose` wrap @into

rw_rw :: forall into a .
	Precategory into =>
	Castable Straight into a =>
	Castable Straight into (Supertype a) =>
	into a (Supertype (Supertype a))
rw_rw = rw @into `compose` rw @into

rw_rw_rw :: forall into a .
	Precategory into =>
	Castable Straight into a =>
	Castable Straight into (Supertype a) =>
	Castable Straight into (Supertype (Supertype a)) =>
	into a (Supertype (Supertype (Supertype a)))
rw_rw_rw = rw @into `compose` rw @into `compose` rw @into

o_yokl :: forall from into t tt a o e .
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
o_yokl = o `compose` yokl @from @into @tt @t

a_yokl :: forall from into t tt a o e .
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
a_yokl = a `compose` fokl @from @into @tt @t

fr_dp :: forall from t i o oo .
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
fr_dp from_left from_right = dp `compose`
	_i (map @Straight @Straight (wrapped (right @Straight from_right))) `compose`
	i_ (map @Straight @Straight (wrapped (left @Straight from_left))) `compose`
	wrapped (map @Straight @Straight @from @(->) @I @(Both (LM)) identity) `compose`
	wrapped (map @Straight @Straight @from @(->) @I @(Both (LM)) identity)

lm_dp :: forall o oo t .
	Covariant Monoidal Functor Arrow LM LM t =>
	t o -> t oo -> t (o `LM` oo)
lm_dp from_left from_right = dp (lm from_left from_right)

lm_ds :: forall o oo t .
	Covariant Monoidal Functor Arrow LM ML t =>
	t o -> t oo -> t (o `ML` oo)
lm_ds from_left from_right = ds (lm from_left from_right)

lm_dp_dp :: forall o oo t tt .
	Covariant Monoidal Functor Arrow LM LM t =>
	Covariant Monoidal Functor Arrow LM LM tt =>
	t (tt o) -> t (tt oo) -> t (tt (o `LM` oo))
lm_dp_dp from_left from_right = dp_dp @LM (lm from_left from_right)

-- TODO: generalize
dp_yo :: forall from e ee r t .
	Covariant Monoidal Functor from LM LM t =>
	t e `LM` t ee -> from (e `LM` ee) r -> t r
dp_yo x f = day @Straight @from @t @LM @LM identity f x

-- TODO: generalize
dp_yokl :: forall e ee from into t tt o .
	Covariant Monoidal Functor Arrow LM LM t =>
	Covariant Yoneda Functor from into t =>
	Component Natural Arrow into (T_TT_I t tt) t =>
	Castable Opposite into (Straight from (e `LM` ee) (tt o)) =>
	Castable Opposite into (T_TT_I t tt o) =>
	t e `LM` t ee -> into (from (e `LM` ee) (tt o)) (t o)
dp_yokl = yokl @from @into `compose` dp

-- TODO: generalize
dp_dp_yo :: forall from e ee r t tt .
	Covariant Monoidal Functor Arrow LM LM t =>
	Covariant Monoidal Functor from LM LM tt =>
	t (tt e) `LM` t (tt ee) -> from (e `LM` ee) r -> t (tt r)
dp_dp_yo x f = day @Straight @Arrow @t @LM @LM identity
	(day @Straight @from @tt @LM @LM identity f) x

jt :: forall into f g e .
	Component Natural (->) into (f `T_TT_I` g) (f `J` g) =>
	Castable Opposite into ((f `T_TT_I` g) e) =>
	into (f (g e)) ((f `J` g) e)
jt = component @Straight @(->) @into @(f `T_TT_I` g) @(f `J` g) @e
	`compose` wrap @into @((f `T_TT_I` g) e)

-- TODO: generalize
dp_dp_jt :: forall e ee t tt .
	Component Natural (->) (->) (t `T_TT_I` tt) (t `J` tt) =>
	Covariant Monoidal Functor (->) LM LM t =>
	Covariant Monoidal Functor (->) LM LM tt =>
	t (tt e) `LM` t (tt ee) -> (t `J` tt) (e `LM` ee)
dp_dp_jt = jt `compose` day @Straight @Arrow @t @LM @LM identity
	(day @Straight @(->) @tt @LM @LM identity identity)

-- TODO: generalize
dp_dp_jt_yokl :: forall from into e ee t tt ttt o .
	Covariant Yoneda Functor from into t =>
	Covariant Yoneda Functor from into (t `J` tt) =>
	Component Natural (->) (->) (t `T_TT_I` tt) (t `J` tt) =>
	Component Natural (->) into (T_TT_I (t `J` tt) ttt) (t `J` tt) =>
	Covariant Monoidal Functor (->) LM LM t =>
	Covariant Monoidal Functor (->) LM LM tt =>
	Castable Opposite into (Straight from (e `LM` ee) (ttt o)) =>
	Castable Opposite into (T_TT_I (J t tt) ttt o) =>
	t (tt e) `LM` t (tt ee) -> into (from (e `LM` ee) (ttt o)) ((t `J` tt) o)
dp_dp_jt_yokl = yokl @from @into `compose` dp_dp_jt

rwr_yoi :: forall into w o u e ee .
	Covariant Endo Semi Functor into (U_II_I u o) =>
	Castable Straight into (U_II_I u o ee) =>
	Castable Opposite into (U_II_I u o e) =>
	Castable Opposite into (w u ee o) =>
	Castable Straight into (w u e o) =>
	Castable Opposite Arrow (into Unit ee) =>
	(Supertype (w u e o) ~ u e o) =>
	(Supertype (w u ee o) ~ u ee o) =>
	into e ee -> into (w u e o) (w u ee o)
rwr_yoi = rwr `compose` i_ `compose` fo

yokl_rwr_yoi :: forall into w t o u e ee .
	Covariant Yoneda Functor into (->) t =>
	Covariant Endo Semi Functor (->) t =>
	Covariant Endo Semi Functor (->) (w u ee) =>
	Covariant Endo Semi Functor into (U_II_I u o) =>
	Component Natural (->) (->) (T_TT_I t (w u ee)) t =>
	(Supertype (w u e o) ~ u e o) =>
	(Supertype (w u ee o) ~ u ee o) =>
	Castable Opposite Arrow (into Unit ee) =>
	Castable Opposite into (U_II_I u o e) =>
	Castable Opposite into (w u ee o) =>
	Castable Straight into (U_II_I u o ee) =>
	Castable Straight into (w u e o) =>
	t (w u e o) -> into e ee -> t o
yokl_rwr_yoi x f = yokl @into @_ @(w u ee) @t x
	(rwr_yoi @into @w @o @u @e @ee f)

rwr_yui :: forall into w o u e ee .
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
rwr_yui = rwr `compose` i_ `compose` fu

-- TODO: find a way to generalize
yokl_rwr_yui :: forall w t o u e ee .
	Covariant Yoneda Functor (->) (->) t =>
	Covariant Endo Semi Functor (->) t =>
	Covariant Endo Semi Functor (->) (w u ee) =>
	Covariant Endo Semi Functor (->) (U_II_I u o) =>
	Mapping Constant Straight (->) (->) (U_II_I u o) (U_II_I u o) =>
	Component Natural (->) (->) (T_TT_I t (w u ee)) t =>
	(Supertype (w u e o) ~ u e o) =>
	(Supertype (w u ee o) ~ u ee o) =>
	Castable Opposite Arrow ((->) Unit ee) =>
	Castable Opposite (->) (U_II_I u o e) =>
	Castable Opposite (->) (w u ee o) =>
	Castable Straight (->) (U_II_I u o ee) =>
	Castable Straight (->) (w u e o) =>
	t (w u e o) -> Supertype (Unit -> ee) -> t o
yokl_rwr_yui x f = yokl @(->) @_ @(w u ee) @t x
	(rwr_yui @(->) @w @o @u @e @ee f)

-- TODO: generalize
yokl_rw_yokl :: forall t tt ttt a aa o .
	Covariant Yoneda Functor (->) (->) t =>
	Covariant Endo Semi Functor (->) t =>
	Covariant Endo Semi Functor (->) tt =>
	Covariant Endo Semi Functor (->) ttt =>
	Component Natural (->) (->) (T_TT_I t tt) t =>
	Component Natural (->) (->) (T_TT_I t ttt) t =>
	Castable Straight (->) a =>
	(Supertype a ~ tt aa) =>
	t a -> (aa -> ttt o) -> t o
yokl_rw_yokl x = yokl @(->) @(->) @ttt @t
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
fc = rw @(->) @(That into (t a) _)
	`compose` (fo @(->) @(->) `compose` fo @(->) @(->))
		(rj @(->) @(->) (wrap @_ @(That _ _ _)) `compose` wrap @_ @(That _ _ _))
	`compose` lj @(->) @(->) @(That LM (t a)) @(That into _)
		(monoidal_ @Straight @into @(->) @t @LM @LM identity (wrap identity)
			`compose` rw @(->) @(That LM (t a) (t (into a o))))

cc :: forall t e ee .
	Adjoint Functor (->) (->) (That LM (t e `LM` t ee)) (That (->) (t e `LM` t ee)) =>
	Monoidal Straight Functor (->) LM LM t =>
	t e -> t ee -> t (e `LM` ee)
cc e ee = monoidal_
	@Straight @(->) @(->) @t @LM @LM identity
	(wrap @(->) identity)
	(e `lm` ee)
