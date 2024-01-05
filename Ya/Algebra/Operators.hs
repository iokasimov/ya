{-# LANGUAGE AllowAmbiguousTypes #-}
module Ya.Algebra.Operators where

import Ya.Algebra.Abstract
import Ya.Algebra.Definition
import Ya.Algebra.Instances ()

infixl 9 `i`, `u`, `o`, `a`, `a_a`, `o_a`, `o_o`, `o_rw_o`, `a_o`, `a_yokl`
infixl 8 `i_i`, `u_u`, `yi`, `yo`, `ya`, `yu`, `fo`, `fa`, `fu`, `lj`, `rj`, `ro`, `ra`, `dp`, `ds`, `fr`, `lm`, `rf`, `cc`, `fc`, `jt`, `dp_yo`, `dp_dp`, `yo_yo`, `fo_fo`, `rw_rw`, `fr_dp`, `lm_dp`, `lm_ds`, `fo_fo_fo`, `dp_dp_yo`, `dp_yokl`, `dp_dp_jt`, `dp_dp_jt_yokl`, `rw_rw_rw`, `lm_dp_dp`, `rw_rf`, `u_o`
infixl 7 `i_i_i`, `u_u_u`, `yai`, `fio`, `foi`, `yoi`, `fai`, `yui`, `yi_o`, `ilj`, `rij`, `fio_fo`, `w_rw`, `rw_w`, `rwr_yoi`, `rwr_yui`
infixl 6 `i_i_i_i`, `u_u_u_u`, `yi_yi`, `yi_yu`, `yi_rf`, `fokl`, `yokl`, `yukl`, `yokl_yoklKL`, `yokl_u`, `yukl_u`, `yokl_u_u`, `yukl_u_u`, `yokl_u_u_u`, `yukl_u_u_u`, `yukl_u_u_u_u`, `yokl_u_u_u_u`, `yukl_u_u_u_u_u_u`, `yokl_u_u_u_u_u_u`, `yukl_u_u_u_u_u`, `yokl_rwr_yoi`, `yokl_rwr_yui`, `yokl_u_u_u_u_u`, `yokl_rw_yokl`
infixl 5 `i_i_i_i_i`, `u_u_u_u_u`, `yiokl`
infixl 4 `i_i_i_i_i_i`, `u_u_u_u_u_u`, `yi_yi_yi`, `yi_yi_yu`, `yi_yi_rf`, `yi_yokl`, `yoklKL`, `yoklKL_yokl`, `yoklKL_yoklKL`, `yi_yukl`
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
	Castable Opposite Arrow (into () o) =>
	Supertype (into () o) -> into (t a) (t o)
fu = map @Constant @Straight @into @into `compose` wrap @Arrow @(into () o)

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
	Covariant Yoneda from into t =>
	Castable Opposite into (U_I_II from a o) =>
	t a -> into (from a o) (t o)
yo x = yoneda @Straight x

yoi :: forall from into t e a o .
	Precategory into =>
	Covariant Yoneda from into (This t e) =>
	Castable Opposite into (Straight from a o) =>
	Castable Straight into (This t e o) =>
	t a e -> into (from a o) (t o e)
yoi x = compose rw (yoneda @Straight @from @into @(This t e) (wrap x))

yu, yi_yu, yi_yi_yu, yi_yi_yi_yu  :: forall into t a o .
	Covariant Yoneda into into t =>
	Covariant Endo Semi Functor (->) t =>
	Castable Opposite into (into () o) =>
	Castable Opposite into (U_I_II into () o) =>
	t a -> into (Supertype (into () o)) (t o)
yu x = yoneda @U_I_II (fu @Arrow () x)
	`compose` wrap @into @(into () o)
yi_yu x = yoneda @U_I_II (fu @Arrow () x)
	`compose` wrap @into @(into () o)
yi_yi_yu x = yoneda @U_I_II (fu @Arrow () x)
	`compose` wrap @into @(into () o)
yi_yi_yi_yu x = yoneda @U_I_II (fu @Arrow () x)
	`compose` wrap @into @(into () o)

yui :: forall into t e a o .
	Covariant Yoneda into into (U_II_I t e) =>
	Covariant Endo Semi Functor (->) (U_II_I t e) =>
	Castable Opposite into (into () o) =>
	Castable Opposite into (U_I_II into () o) =>
	Castable Straight into (U_II_I t e o) =>
	t a e -> into (Supertype (into () o)) (t o e)
yui x = rw @into @(U_II_I t e _) `compose` yu @into (wrap @(->) @(U_II_I t e _) x)

yo_yo :: forall from into t tt a o .
	Precategory into =>
	Covariant Functor from from tt =>
	Covariant Yoneda from into t =>
	Contravariant Endo Semi Functor Arrow (U_II_I into (t (tt o))) =>
	Castable Opposite into (U_I_II from (tt a) (tt o)) =>
	t (tt a) -> into (from a o) (t (tt o))
yo_yo x = fai fo (yo @from @into x)

-- TODO: yo_yo : t (tt a) -> into (from a b) (tt a -> into (from b o) (t (tt o)))

ya :: forall from into t a o .
	Precategory into =>
	Contravariant Yoneda from into t =>
	Castable Opposite into (Opposite from a o) =>
	t a -> into (from o a) (t o)
ya = yoneda @Opposite 

yai :: forall from into t e a o .
	Precategory into =>
	Contravariant Yoneda from into (This t e) =>
	Castable Opposite into (Opposite from a o) =>
	Castable Straight into (This t e o) =>
	t a e -> into (from o a) (t o e)
yai x = compose rw (yoneda @Opposite @from @into @(This t e) (wrap x))

yokl, yi_yokl, yokl_u, yokl_u_u, yokl_u_u_u, yokl_u_u_u_u, yokl_u_u_u_u_u, yokl_u_u_u_u_u_u :: forall from into tt t a o .
	Component Natural Arrow into (T_TT_I t tt) t =>
	Covariant Yoneda from into t =>
	Castable Opposite into (Straight from a (tt o)) =>
	Castable Opposite into (T_TT_I t tt o) =>
	t a -> into (from a (tt o)) (t o)
yokl x = component @Straight @Arrow @into @(T_TT_I t tt)
	`compose` wrap @into @(T_TT_I t tt _)
	`compose` yoneda @Straight @from x
yi_yokl x = component @Straight @Arrow @into @(T_TT_I t tt)
	`compose` wrap @into @(T_TT_I t tt _)
	`compose` yoneda @Straight @from x
yokl_u x = component @Straight @Arrow @into @(T_TT_I t tt)
	`compose` wrap @into @(T_TT_I t tt _)
	`compose` yoneda @Straight @from x
yokl_u_u x = component @Straight @Arrow @into @(T_TT_I t tt)
	`compose` wrap @into @(T_TT_I t tt _)
	`compose` yoneda @Straight @from x
yokl_u_u_u x = component @Straight @Arrow @into @(T_TT_I t tt)
	`compose` wrap @into @(T_TT_I t tt _)
	`compose` yoneda @Straight @from x
yokl_u_u_u_u x = component @Straight @Arrow @into @(T_TT_I t tt)
	`compose` wrap @into @(T_TT_I t tt _)
	`compose` yoneda @Straight @from x
yokl_u_u_u_u_u x = component @Straight @Arrow @into @(T_TT_I t tt)
	`compose` wrap @into @(T_TT_I t tt _)
	`compose` yoneda @Straight @from x
yokl_u_u_u_u_u_u x = component @Straight @Arrow @into @(T_TT_I t tt)
	`compose` wrap @into @(T_TT_I t tt _)
	`compose` yoneda @Straight @from x

yukl, yukl_u, yukl_u_u, yukl_u_u_u, yukl_u_u_u_u, yukl_u_u_u_u_u, yukl_u_u_u_u_u_u, yi_yukl, yi_yi_yukl, yi_yi_yi_yukl
	:: forall into tt t a o .
	Covariant Endo Semi Functor (->) t =>
	Component Natural Arrow into (T_TT_I t tt) t =>
	Covariant Yoneda into into t =>
	Castable Opposite into (into () (tt o)) =>
	Castable Opposite into (Straight into () (tt o)) =>
	Castable Opposite into (T_TT_I t tt o) =>
	t a -> into (Supertype (into () (tt o))) (t o)
yukl x = component @Straight @Arrow @into @(T_TT_I t tt)
	`compose` wrap @into @(T_TT_I t tt _)
	`compose` yoneda @Straight (fu @Arrow () x)
	`compose` wrap @into @(into () (tt o))
yukl_u x = component @Straight @Arrow @into @(T_TT_I t tt)
	`compose` wrap @into @(T_TT_I t tt _)
	`compose` yoneda @Straight (fu @Arrow () x)
	`compose` wrap @into @(into () (tt o))
yukl_u_u x = component @Straight @Arrow @into @(T_TT_I t tt)
	`compose` wrap @into @(T_TT_I t tt _)
	`compose` yoneda @Straight (fu @Arrow () x)
	`compose` wrap @into @(into () (tt o))
yukl_u_u_u x = component @Straight @Arrow @into @(T_TT_I t tt)
	`compose` wrap @into @(T_TT_I t tt _)
	`compose` yoneda @Straight (fu @Arrow () x)
	`compose` wrap @into @(into () (tt o))
yukl_u_u_u_u x = component @Straight @Arrow @into @(T_TT_I t tt)
	`compose` wrap @into @(T_TT_I t tt _)
	`compose` yoneda @Straight (fu @Arrow () x)
	`compose` wrap @into @(into () (tt o))
yukl_u_u_u_u_u x = component @Straight @Arrow @into @(T_TT_I t tt)
	`compose` wrap @into @(T_TT_I t tt _)
	`compose` yoneda @Straight (fu @Arrow () x)
	`compose` wrap @into @(into () (tt o))
yukl_u_u_u_u_u_u x = component @Straight @Arrow @into @(T_TT_I t tt)
	`compose` wrap @into @(T_TT_I t tt _)
	`compose` yoneda @Straight (fu @Arrow () x)
	`compose` wrap @into @(into () (tt o))
yi_yukl x = component @Straight @Arrow @into @(T_TT_I t tt)
	`compose` wrap @into @(T_TT_I t tt _)
	`compose` yoneda @Straight (fu @Arrow () x)
	`compose` wrap @into @(into () (tt o))
yi_yi_yukl x = component @Straight @Arrow @into @(T_TT_I t tt)
	`compose` wrap @into @(T_TT_I t tt _)
	`compose` yoneda @Straight (fu @Arrow () x)
	`compose` wrap @into @(into () (tt o))
yi_yi_yi_yukl x = component @Straight @Arrow @into @(T_TT_I t tt)
	`compose` wrap @into @(T_TT_I t tt _)
	`compose` yoneda @Straight (fu @Arrow () x)
	`compose` wrap @into @(into () (tt o))

yoklKL :: forall from into tt t a o .
	Component Natural from into (T_TT_I t tt) (TT_T_I t tt) =>
	Covariant Yoneda from into t =>
	Castable Opposite into (Straight from a (tt o)) =>
	Castable Straight into (TT_T_I t tt o) =>
	Castable Opposite into (T_TT_I t tt o) =>
	t a -> into (from a (tt o)) (tt (t o))
yoklKL x = rw @into @(TT_T_I t tt _)
	`compose` component @Straight @from @into @(T_TT_I t tt) @(TT_T_I t tt)
	`compose` wrap @into @(T_TT_I t tt _)
	`compose` yoneda @Straight @from x

yiokl :: forall from into tt t i a o .
	Component Natural from into (T_TT_I (U_I_II t i) tt) (U_I_II t i) =>
	Covariant Yoneda from into (U_I_II t i) =>
	Castable Opposite into (U_I_II from a (tt o)) =>
	Castable Straight into (U_I_II t i o) =>
	Castable Opposite into (T_TT_I (U_I_II t i) tt o) =>
	t i a -> into (from a (tt o)) (t i o)
yiokl x = rw @into @(U_I_II t i o)
	`compose` component @Straight @from @into @(T_TT_I (U_I_II t i) tt)
	`compose` wrap @into @(T_TT_I (U_I_II t i) tt _)
	`compose` yoneda @Straight @from (U_I_II x)

yokl_yoklKL :: forall from into t tt ttt a o .
	Covariant Yoneda from into t =>
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
	Covariant Yoneda from into t =>
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
	Covariant Yoneda from into t =>
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

o, u_o, yi_o :: forall from into u i a o .
	Precategory into =>
	Covariant Yoneda from into (U_I_II u i) =>
	Castable Opposite into (U_I_II from a o) =>
	Castable Straight into (U_I_II u i o) =>
	u i a -> into (from a o) (u i o)
o x = rw `compose` yo @from @into @(U_I_II u _) (U_I_II x)
u_o x = rw `compose` yo @from @into @(U_I_II u _) (U_I_II x)
yi_o x = rw `compose` yo @from @into @(U_I_II u _) (U_I_II x)

a :: forall into from u e a o .
	Precategory into =>
	Contravariant Yoneda from into (U_II_I u e) =>
	Castable Opposite into (Opposite from a o) =>
	Castable Straight into (Opposite u e o) =>
	u a e -> into (from o a) (u o e)
a x = rw `compose` ya @from @into @(U_II_I u _) (U_II_I x)

a_a :: forall from into u i o e b .
	Precategory into =>
	Contravariant Yoneda from from (U_II_I u e) =>
	Contravariant Yoneda from into (U_II_I from (u b e)) =>
	Castable Opposite from (Opposite from o b) =>
	Castable Straight from (Opposite u e b) =>
	Castable Opposite into (Opposite from (from b o) i) =>
	Castable Straight into (Opposite from (u b e) i) =>
	u o e -> into (from i (from b o)) (from i (u b e))
a_a = a @into @from `compose` a @from @from

o_a :: forall from u uu i o e ee a b .
	Covariant Yoneda from (->) (Straight u e) =>
	Contravariant Yoneda from (->) (Opposite u e) =>
	Contravariant Endo Semi Functor from (Opposite uu ee) =>
	Contravariant Endo Semi Functor (->) (Opposite (->) (u e (uu a ee))) =>
	Castable Opposite (->) (U_I_II from (uu o ee) (uu a ee)) =>
	Castable Straight (->) (U_I_II u e (uu a ee)) =>
	Wrapper from (U_II_I uu ee a) =>
	Wrapper from (U_II_I uu ee o) =>
	u e (uu o ee) -> from a o -> u e (uu a ee)
o_a x = fai @(->) @(->) fai (o @from @(->) x)

o_o :: forall from u uu i o e ee a b .
	Covariant Yoneda from (->) (Straight u e) =>
	Contravariant Yoneda from (->) (Opposite u e) =>
	Covariant Endo Semi Functor from (Straight uu ee) =>
	Covariant Endo Semi Functor (->) (Straight (->) (u e (uu a ee))) =>
	Castable Opposite (->) (U_I_II from (uu o ee) (uu a ee)) =>
	Castable Straight (->) (U_I_II u e (uu a ee)) =>
	Wrapper from (Straight uu ee a) =>
	Wrapper from (Straight uu ee o) =>
	u e (uu ee a) -> from a o -> u e (uu ee o)
o_o x = fai @(->) @(->) fio (o @from @(->) x)

o_rw :: forall from into u e a o .
	Precategory into =>
	Covariant Endo Semi Functor from (That from a) =>
	Covariant Yoneda from into (U_I_II u e) =>
	Contravariant Semi Functor from (->) (U_II_I into (u e (Supertype o))) =>
	Contravariant Yoneda from into (U_II_I into (u e (Supertype o))) =>
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
	Covariant Yoneda from (->) (That u e) =>
	Castable Straight from a =>
	u e a -> from (Supertype a) o -> u e o
o_rw_o x xx = x `o`rw @from `o` xx

a_o :: forall from into u o e i a .
	Category into =>
	Contravariant Yoneda from into (U_II_I from (u i e)) =>
	Covariant Yoneda from from (U_I_II u i) =>
	Castable Opposite from (U_I_II from a e) =>
	Castable Straight from (U_I_II u i e) =>
	Castable Straight into (Opposite from (u i e) o) =>
	Castable Opposite into (Opposite from (from a e) o) =>
	u i a -> into (from o (from a e)) (from o (u i e))
a_o = a @into @from `compose` o @from @from

u, u_u, u_u_u, u_u_u_u, u_u_u_u_u, u_u_u_u_u_u, u_u_u_u_u_u_u,
	u_u_u_u_u_u_u_u, u_u_u_u_u_u_u_u_u, u_u_u_u_u_u_u_u_u_u :: forall from into i a o .
	Precategory into =>
	Covariant Yoneda from into (U_1_I from i) =>
	Castable Opposite into (U_I_II from a o) =>
	Castable Straight into (U_I_II from i o) =>
	Castable Opposite (->) (from () a) =>
	Castable Straight into (from () o) =>
	Castable Straight into (U_1_I from i o) =>
	Supertype (from () a) -> into (from a o) (Supertype (from () o))
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

ro :: forall into hom t i .
	Category into =>
	Covariant (Representable hom) into into t =>
	Castable Straight into (Straight hom (Representation t) i) =>
	into (t i) (hom (Representation t) i)
ro = rw `compose` map @Straight @Straight @into @into @t @(Straight hom (Representation t)) identity

ra :: forall into hom t i .
	Category into =>
	Contravariant (Representable hom) into into t =>
	Castable Straight into (Opposite hom (Representation t) i) =>
	into (t i) (hom i (Representation t))
ra = rw `compose` map @Opposite @Straight @into @into @t @(Opposite hom (Representation t)) identity

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

rij :: forall from into t tt e ee a o .
	Adjoint Functor from into (U_I_II t ee) (U_I_II tt e) =>
	Castable Opposite from ((T_TT_I (U_I_II t ee) (U_I_II tt e)) o) =>
	Castable Straight from (I o) =>
	Castable Opposite from (U_I_II t ee a) =>
	Castable Opposite into (U_I_II tt e o) =>
	into a (tt e o) -> from (t ee a) o
rij from = rw @from
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
	Covariant Functor (->) (->) (This (Product (->)) (Product (->) () ())) =>
	Castable Straight (->) (Both (Product (->)) (Product (->) () ())) =>
	Castable Straight (->) (That (Product (->)) o oo) =>
	Castable Opposite (->) (This (Product (->)) () ()) =>
	Castable Opposite (->) (That (Product (->)) () ()) =>
	Castable Straight (->) (Both (Product (->)) ()) =>
	Castable Straight (->) (This (Product (->)) (Product (->) () ()) o) =>
	Castable Opposite (->) (This (Product (->)) (Product (->) () ()) (Product (->) () ())) =>
	Wrapper (->) (That (Product (->)) o (Product (->) () ())) =>
	(forall e . Wrapper (->) (I e)) =>
	Castable Opposite (->) ((->) () o) =>
	Castable Opposite (->) ((->) () oo) =>
	Castable Straight (->) ((->) () (Product (->) o oo)) =>
	Supertype ((->) () o) -> Supertype ((->) () oo) -> Supertype ((->) () (Product (->) o oo))
lm from_left from_right = unwrap /
	_i (map @Straight @Straight (wrapped (right @Straight (wrap @_ @((->) () oo) from_right)))) `compose`
	i_ (map @Straight @Straight (wrapped (left @Straight (wrap @_ @((->) () o) from_left)))) `compose`
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

rw_rf :: forall from into e i o oo .
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
	(Supertype e ~ (Sum into o oo)) =>
	Castable Straight into e =>
	from o i -> from oo i -> into e i
rw_rf from_left from_right = rf from_left from_right `compose` rw

-- TODO: to test
rwr_rf :: forall from into r eee e ee .
	Category from =>
	Limit Opposite from into =>
	Covariant Functor into into (That (Sum into) e) =>
	Covariant Functor into into (This (Sum into) (Sum into (Supertype r) (Supertype r))) =>
	Castable Opposite into (Both (Sum into) (Sum into (Supertype r) (Supertype r))) =>
	Castable Opposite into (That (Sum into) e ee) =>
	Castable Straight into (That (Sum into) (Supertype r) (Supertype r)) =>
	Castable Straight into (This (Sum into) (Supertype r) (Supertype r)) =>
	Castable Opposite into (Both (Sum into) (Supertype r)) =>
	Castable Straight into (That (Sum into) e (Sum into (Supertype r) (Supertype r))) =>
	Castable Opposite into (This (Sum into) (Sum into (Supertype r) (Supertype r)) e) =>
	Castable Straight into (This (Sum into) (Sum into (Supertype r) (Supertype r)) (Sum into (Supertype r) (Supertype r))) =>
	(Supertype eee ~ Sum into e ee) =>
	(forall eeee . Wrapper into (I eeee)) =>
	Castable Opposite into r =>
	Castable Straight into eee =>
	from e (Supertype r) -> from ee (Supertype r) -> into eee r
rwr_rf from_left from_right = rwr /
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
	Covariant Yoneda from into t =>
	Covariant Yoneda into into (U_I_II into (from a (tt o))) =>
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
	Covariant Yoneda into into (U_I_II into (from a (tt o))) =>
	Contravariant Yoneda from into (U_II_I into (tt o)) =>
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
	Covariant Yoneda from into t =>
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
	Component Natural (->) into (f `T_TT_I` g) (f `JT` g) =>
	Castable Opposite into ((f `T_TT_I` g) e) =>
	into (f (g e)) ((f `JT` g) e)
jt = component @Straight @(->) @into @(f `T_TT_I` g) @(f `JT` g) @e
	`compose` wrap @into @((f `T_TT_I` g) e)

-- TODO: generalize
dp_dp_jt :: forall e ee t tt .
	Component Natural (->) (->) (t `T_TT_I` tt) (t `JT` tt) =>
	Covariant Monoidal Functor (->) LM LM t =>
	Covariant Monoidal Functor (->) LM LM tt =>
	t (tt e) `LM` t (tt ee) -> (t `JT` tt) (e `LM` ee)
dp_dp_jt = jt `compose` day @Straight @Arrow @t @LM @LM identity
	(day @Straight @(->) @tt @LM @LM identity identity)

-- TODO: generalize
dp_dp_jt_yokl :: forall from into e ee t tt ttt o .
	Covariant Yoneda from into t =>
	Covariant Yoneda from into (t `JT` tt) =>
	Component Natural (->) (->) (t `T_TT_I` tt) (t `JT` tt) =>
	Component Natural (->) into (T_TT_I (t `JT` tt) ttt) (t `JT` tt) =>
	Covariant Monoidal Functor (->) LM LM t =>
	Covariant Monoidal Functor (->) LM LM tt =>
	Castable Opposite into (Straight from (e `LM` ee) (ttt o)) =>
	Castable Opposite into (T_TT_I (JT t tt) ttt o) =>
	t (tt e) `LM` t (tt ee) -> into (from (e `LM` ee) (ttt o)) ((t `JT` tt) o)
dp_dp_jt_yokl = yokl @from @into `compose` dp_dp_jt

-- TODO: generalize
rwr_foi :: forall into w o u e ee .
	Covariant Endo Semi Functor into (U_II_I u o) =>
	Castable Straight into (U_II_I u o ee) =>
	Castable Opposite into (U_II_I u o e) =>
	Castable Opposite into (w u ee o) =>
	Castable Straight into (w u e o) =>
	(Supertype (w u e o) ~ u e o) =>
	(Supertype (w u ee o) ~ u ee o) =>
	into e ee -> into (w u e o) (w u ee o)
rwr_foi = rwr `compose` i_ `compose` fo

-- TODO: try to simplify
rwr_yoi :: forall from into w o u e ee .
	Precategory into =>
	Covariant Yoneda from into (U_II_I u o) =>
	Castable Opposite into (w u ee o) =>
	Castable Straight (->) (w u e o) =>
	Castable Straight into (U_II_I u o ee) =>
	Castable Opposite into (U_I_II from e ee) =>
	(Supertype (w u e o) ~ u e o) =>
	(Supertype (w u ee o) ~ u ee o) =>
	w u e o -> into (from e ee) (w u ee o)
rwr_yoi x = wrap @into `compose` yoi (unwrap x)

-- TODO: generalize
o_rwr_yoi :: forall from into w a o u e ee .
	Precategory into =>
	Covariant Endo Semi Functor into (U_II_I u o) =>
	Covariant Yoneda into (->) (U_I_II from a) =>
	Castable Straight into (w u e o) =>
	Castable Opposite into (w u ee o) =>
	Castable Straight into (U_II_I u o ee) =>
	Castable Opposite into (U_II_I u o e) =>
	(Supertype (w u e o) ~ u e o) =>
	(Supertype (w u ee o) ~ u ee o) =>
	from a (w u e o) -> into e ee -> from a (w u ee o)
o_rwr_yoi x f = x `o` rwr_foi @into @w @o @u @e @ee f

yokl_rwr_yoi :: forall into w t o u e ee .
	Covariant Yoneda into (->) t =>
	Covariant Endo Semi Functor (->) t =>
	Covariant Endo Semi Functor (->) (w u ee) =>
	Covariant Endo Semi Functor into (U_II_I u o) =>
	Component Natural (->) (->) (T_TT_I t (w u ee)) t =>
	(Supertype (w u e o) ~ u e o) =>
	(Supertype (w u ee o) ~ u ee o) =>
	Castable Opposite Arrow (into () ee) =>
	Castable Opposite into (U_II_I u o e) =>
	Castable Opposite into (w u ee o) =>
	Castable Straight into (U_II_I u o ee) =>
	Castable Straight into (w u e o) =>
	t (w u e o) -> into e ee -> t o
yokl_rwr_yoi x f = yokl @into @_ @(w u ee) @t x
	(rwr_foi @into @w @o @u @e @ee f)

rwr_yui :: forall into w o u e ee .
	Covariant Endo Semi Functor into (U_II_I u o) =>
	Mapping Constant Straight into into (U_II_I u o) (U_II_I u o) =>
	Castable Straight into (U_II_I u o ee) =>
	Castable Opposite into (U_II_I u o e) =>
	Castable Opposite into (w u ee o) =>
	Castable Straight into (w u e o) =>
	Castable Opposite Arrow (into () ee) =>
	(Supertype (w u e o) ~ u e o) =>
	(Supertype (w u ee o) ~ u ee o) =>
	Supertype (into () ee) -> into (w u e o) (w u ee o)
rwr_yui = rwr `compose` i_ `compose` fu

-- TODO: find a way to generalize
yokl_rwr_yui :: forall w t o u e ee .
	Covariant Yoneda (->) (->) t =>
	Covariant Endo Semi Functor (->) t =>
	Covariant Endo Semi Functor (->) (w u ee) =>
	Covariant Endo Semi Functor (->) (U_II_I u o) =>
	Mapping Constant Straight (->) (->) (U_II_I u o) (U_II_I u o) =>
	Component Natural (->) (->) (T_TT_I t (w u ee)) t =>
	(Supertype (w u e o) ~ u e o) =>
	(Supertype (w u ee o) ~ u ee o) =>
	Castable Opposite Arrow ((->) () ee) =>
	Castable Opposite (->) (U_II_I u o e) =>
	Castable Opposite (->) (w u ee o) =>
	Castable Straight (->) (U_II_I u o ee) =>
	Castable Straight (->) (w u e o) =>
	t (w u e o) -> Supertype (() -> ee) -> t o
yokl_rwr_yui x f = yokl @(->) @_ @(w u ee) @t x
	(rwr_yui @(->) @w @o @u @e @ee f)

-- TODO: generalize
yokl_rw_yokl :: forall t tt ttt a aa o .
	Covariant Yoneda (->) (->) t =>
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
