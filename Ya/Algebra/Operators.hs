{-# LANGUAGE AllowAmbiguousTypes #-}
module Ya.Algebra.Operators where

import Ya.Algebra.Abstract
import Ya.Algebra.Definition
import Ya.Algebra.Instances ()

infixl 9 `_'`, `i`, `u`, `u'`, `v`, `ho`, `ho'`, `ha`, `ha'`, `_j`, `j'`, `j'_j'`, `ha_ha`, `ha_ha'`, `ha'_ha`, `ha'_ha'`, `ho_ha`, `ho_ho`, `ha_ho`, `ho_yo`, `ho'_yo`, `ho_yioi`, `ha_yo`, `ha_yioi`, `ho_yu`, `ho_yi'_ho`, `ho_yokl`, `ho_yukl`, `ho_yoklKL`, `ha_yokl`, `ha_yukl` --, `ho_rwr_yoi`, `ho_rwr_yio`
infixl 8 `yi'`, `vv`, `i_i`, `uu`, `yi`, `yo`, `ya`, `yu`, `fo`, `fa`, `fu`, `lj`, `rj`, `ro`, `ra`, `dp`, `ds`, `fr`, `cn`, `cn'`, `cn_dp`, `cn'_dp`, `lm`, `rf`, `cc`, `fc`, `jt`, `dp_yo`, `dp_dp`, `yo_yo`, `fo_fo`, `fr_dp`, `lm_dp`, `lm_ds`, `fo_fo_fo`, `dp_dp_yo`, `dp_yokl`, `dp_yoklKL`, `dp_dp_jt`, `dp_dp_jt_yokl`, `yi'_yi'_yi'_o`, `lm_dp_dp`, `rf'`, `hoo`, `hoo'`, `hoo_ha`, `hoo_yo`, `hoo_yokl`, `hoo_yukl`, `hoo_yoklKL`, `haa`, `haa'`, `yi_yi'`
infixl 7 `yii'`, `vvv`, `i_i_i`, `uuu`, `yai`, `yai_yai`, `fio`, `foi`, `yoi`, `yoo`, `yii`, `yio`, `yio_yo`, `fai`, `fai'`, `yui`, `yiu`, `yi_ho`, `ilj`, `rij`, `fio_fo`, `w_rw`, `rw_w`, `hooo`, `hooo'`, `hooo_yo`, `hooo_yokl`, `hooo_yukl`, `haaa`, `haaa'` --, `rwr_yoi`, `rwr_yui`
infixl 6 `yiii'`, `yi'_yi'`, `vvvv`, `i_i_i_i`, `uuuu`, `yi_yi`, `yiii`, `yioi`, `yi_yo`, `yi_yu`, `yi_lm`, `yi_lm_ds`, `yi_rf`, `yi_rf'`, `yi'_rf'`, `yi_cn'_dp`, `fokl`, `fukl`, `yokl`, `yokl_ha`, `yokl_u`, `yukl`, `yolk`, `yokl_yoklKL`, `yokl_yi'_yokl`, `yi_cn_dp`, `yi_lm_dp`, `hoooo`, `hoooo'`, `hoooo_yo`, `hoooo_yokl`, `hoooo_yukl`, `haaaa`, `haaaa'`--, `yokl_rwr_yoi`, `yokl_rwr_yui`
infixl 5 `yiiii'`, `yii'_yi'`, `vvvvv`, `i_i_i_i_i`, `yiiii`, `uuuuu`, `yiokl`, `hooooo`, `hooooo'`, `hooooo_yo`, `hooooo_yokl`, `hooooo_yukl`, `haaaaa`, `haaaaa'`
infixl 4 `yiiiii'`, `yi'_yi'_yi'`, `yi_yi'_yi'`, `yiii'_yi'`, `vvvvvv`, `i_i_i_i_i_i`, `yiiiii`, `uuuuuu`, `yi_yi_yo`, `yi_yi_yi`, `yi_yi_yu`, `yi_yi_lm`, `yi_yi_lm_ds`, `yi_yi_rf`, `yi_yi_rf'`, `yi_yi_cn'_dp`, `yi_yokl`, `yi_yokl_ha`, `yoklKL`, `yoklKL_yokl`, `yoklKL_yoklKL`, `yi_yukl`, `yi_yokl_yoklKL`, `yi_yi_yi'`, `yi_yi_lm_dp`, `hoooooo`, `hoooooo'`, `hoooooo_yo`, `hoooooo_yokl`, `hoooooo_yukl`, `haaaaaa`, `haaaaaa'`
infixl 3 `vvvvvvv`, `i_i_i_i_i_i_i`, `yiiiiii`, `uuuuuuu`, `hooooooo_yokl`, `hooooooo_yukl`, `haaaaaaa`, `haaaaaaa'`
infixl 2 `vvvvvvvv`, `i_i_i_i_i_i_i_i`, `yiiiiiii`, `yi_yi_yi_yo`, `uuuuuuuu`, `yi_yi_yi_yi`, `yi_yi_yi'_yi'`, `yi_yi_yi_yu`, `yi_yi_yi_lm`, `yi_yi_yi_rf`, `yi_yi_yi_rf'`, `yi_yi_yi_yi'`, `yi_yi'_yi'_yi'`, `yi_yi_yi_lm_dp`, `yi_yi_yi_cn'_dp`, `yi_yi_yokl_ha`, `yi_yi_yukl`, `yi_yoklKL`, `yi_yi_yokl_yoklKL`, `hoooooooo_yokl`, `hoooooooo_yukl`, `haaaaaaaa`, `haaaaaaaa'`
infixl 1 `vvvvvvvvv`, `i_i_i_i_i_i_i_i_i`, `yiiiiiiii`, `uuuuuuuuu`, `hooooooooo_yokl`, `hooooooooo_yukl`, `haaaaaaaaa`, `haaaaaaaaa'`
infixl 0 `i_i_i_i_i_i_i_i_i_i`, `uuuuuuuuuu`, `yi_yi_yi_yi_yo`, `yi_yi_yi_yi_yi`, `yi_yi_yi_yi_lm`, `yi_yi_yi_yi_lm_dp`, `yi_yi_yi_yokl_ha`, `yi_yi_yi_yukl`, `yi_yi_yi_yokl_yoklKL`, `yi_yi_yoklKL`

i, i_i, i_i_i, i_i_i_i, i_i_i_i_i, i_i_i_i_i_i, i_i_i_i_i_i_i, i_i_i_i_i_i_i_i, i_i_i_i_i_i_i_i_i, i_i_i_i_i_i_i_i_i_i :: Category into => into e e
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

_' :: forall into e .
 Castable Straight into e =>
 into e (Supertype e)
_' = unwrap

yi, yii, yiii, yiiii, yiiiii, yiiiiii, yiiiiiii, yiiiiiiii, yi_yi, yi_yi_yi, yi_yi_yi_yi, yi_yi_yi_yi_yi
 :: Category into => into e e
yi = identity

yii = yi
yiii = yi
yiiii = yi
yiiiii = yi
yiiiiii = yi
yiiiiiii = yi
yiiiiiiii = yi
yi_yi = yi
yi_yi_yi = yi
yi_yi_yi_yi = yi
yi_yi_yi_yi_yi = yi

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
 Castable Opposite (->) (into () o) =>
 Supertype (into () o) -> into (t a) (t o)
fu = map @Constant @Straight @into @into `compose` wrap @(into () o)

fokl :: forall from into t tt a o .
 Component Natural from into (T_TT_I t tt) t =>
 Castable Opposite into (T_TT_I t tt o) =>
 from a (tt o) -> into (t a) (t o)
fokl from = component @Straight @from @into @(t `T_TT_I` tt) @t
 `compose` wr `compose` fo from

fukl :: forall into t tt a o .
 Component Natural into into (T_TT_I t tt) t =>
 Mapping Constant Straight into into t t =>
 Castable Opposite into (T_TT_I t tt o) =>
 Castable Opposite (->) (into () (tt o)) =>
 Castable Opposite into (T_TT_I t t o) =>
 Supertype (into () (tt o)) -> into (t a) (t o)
fukl from = map @Straight @Straight @into @into @(t `T_TT_I` tt) @t identity
 `compose` wr `compose` fu @into from

foklKL :: forall from into t tt a o .
 Covariant Semi Functor from into t =>
 Component Natural from into (T_TT_I t tt) (TT_T_I t tt) =>
 Castable Opposite into (T_TT_I t tt o) =>
 Castable Straight into (TT_T_I t tt o) =>
 from a (tt o) -> into (t a) (tt (t o))
foklKL from = wrapped
 (component @Straight @from @into @(t `T_TT_I` tt) @(t `TT_T_I` tt))
 `compose` fo from

yo, yoo, yi_yo, yi_yi_yo, yi_yi_yi_yo, yi_yi_yi_yi_yo :: forall from into t a o .
 Precategory into =>
 Covariant Yoneda from into t =>
 Castable Opposite into (U_I_II from a o) =>
 t a -> into (from a o) (t o)
yo x = yoneda @Straight x

yoo = yo
yi_yo = yo
yi_yi_yo = yo
yi_yi_yi_yo = yo
yi_yi_yi_yi_yo = yo

yoi :: forall from into t e a o .
 Precategory into =>
 Covariant Yoneda from into (This t e) =>
 Castable Opposite into (Straight from a o) =>
 Castable Straight into (This t e o) =>
 t a e -> into (from a o) (t o e)
yoi x = compose unwrap (yoneda @Straight @from @into @(This t e) (wrap x))

yio :: forall from into t e a o .
 Precategory into =>
 Covariant Yoneda from into (That t e) =>
 Castable Opposite into (Straight from a o) =>
 Castable Straight into (That t e o) =>
 t e a -> into (from a o) (t e o)
yio x = compose unwrap (yoneda @Straight @from @into @(That t e) (wrap x))

yioi :: forall from into w e eee a o .
 Precategory into =>
 Covariant Yoneda from into (W_III_I_II w eee e) =>
 Castable Opposite into (U_I_II from a o) =>
 Castable Straight into (W_III_I_II w eee e o) =>
 w e a eee -> into (from a o) (w e o eee)
yioi x = compose unwrap (yoneda @Straight @from @into @(W_III_I_II _ _ _) (wrap x))

yu, yi_yu, yi_yi_yu, yi_yi_yi_yu  :: forall into t a o .
 Covariant Yoneda into into t =>
 Covariant Endo Semi Functor (->) t =>
 Castable Opposite into (into () o) =>
 Castable Opposite into (U_I_II into () o) =>
 t a -> into (Supertype (into () o)) (t o)
yu x = yoneda @U_I_II (fu @(->) () x) `compose` wr @into @(into () o)

yi_yu = yu
yi_yi_yu = yu
yi_yi_yi_yu = yu

yui :: forall into t e a o .
 Covariant Yoneda into into (U_II_I t e) =>
 Covariant Endo Semi Functor (->) (U_II_I t e) =>
 Castable Opposite into (into () o) =>
 Castable Opposite into (U_I_II into () o) =>
 Castable Straight into (U_II_I t e o) =>
 t a e -> into (Supertype (into () o)) (t o e)
yui x = unwrap @into @(U_II_I t e _)
 `compose` yu @into (wrap @(U_II_I t e _) x)

yiu :: forall into t e a o .
 Covariant Yoneda into into (U_I_II t e) =>
 Covariant Endo Semi Functor (->) (U_I_II t e) =>
 Castable Opposite into (into () o) =>
 Castable Opposite into (U_I_II into () o) =>
 Castable Straight into (U_I_II t e o) =>
 t e a -> into (Supertype (into () o)) (t e o)
yiu x = unwrap @into @(U_I_II t e _)
 `compose` yu @into (wrap @(U_I_II t e _) x)

yo_yo :: forall from into t tt a o .
 Precategory into =>
 Covariant Functor from from tt =>
 Covariant Yoneda from into t =>
 Contravariant Endo Semi Functor (->) (U_II_I into (t (tt o))) =>
 Castable Opposite into (U_I_II from (tt a) (tt o)) =>
 t (tt a) -> into (from a o) (t (tt o))
yo_yo x = fai fo (yo @from @into x)

yio_yo :: forall from into t tt e a o .
 Precategory into =>
 Contravariant Endo Semi Functor (->) (This into (t e (tt o))) =>
 Covariant Yoneda from into (That t e) =>
 Covariant Functor from from tt =>
 Castable Opposite into (Straight from (tt a) (tt o)) =>
 Castable Straight into (That t e (tt o)) =>
 t e (tt a) -> into (from a o) (t e (tt o))
yio_yo x = fai fo (yio @from @into x)

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
yai x = compose unwrap (yoneda @Opposite @from @into @(This t e) (wr x))

yai_yai :: forall from into t tt e ee a (o :: *) .
 Precategory from =>
 Precategory into =>
 Contravariant Yoneda from into (This t ee) =>
 Contravariant Endo Semi Functor from (This tt e) =>
 Contravariant Endo Semi Functor (->) (This into (t (tt o e) ee)) =>
 Wrapper from (U_II_I tt e o) =>
 Wrapper from (U_II_I tt e a) =>
 Castable Straight into (U_II_I t ee (tt o e)) =>
 Castable Opposite into (U_II_I from (tt a e) (tt o e)) =>
 t (tt a e) ee -> into (from a o) (t (tt o e) ee)
yai_yai x = fai fai (yai @from @into x)

yokl, yi_yokl :: forall from into tt t a o .
 Component Natural (->) into (T_TT_I t tt) t =>
 Covariant Yoneda from into t =>
 Castable Opposite into (Straight from a (tt o)) =>
 Castable Opposite into (T_TT_I t tt o) =>
 t a -> into (from a (tt o)) (t o)
yokl x = component @Straight @(->) @into @(T_TT_I t tt)
 `compose` wr @into @(T_TT_I t tt _)
 `compose` yoneda @Straight @from x

yi_yokl = yokl

yukl, yi_yukl, yi_yi_yukl, yi_yi_yi_yukl
 :: forall into tt t a o .
 Covariant Endo Semi Functor (->) t =>
 Component Natural (->) into (T_TT_I t tt) t =>
 Covariant Yoneda into into t =>
 Castable Opposite into (into () (tt o)) =>
 Castable Opposite into (Straight into () (tt o)) =>
 Castable Opposite into (T_TT_I t tt o) =>
 t a -> into (Supertype (into () (tt o))) (t o)
yukl x = component @Straight @(->) @into @(T_TT_I t tt)
 `compose` wr @into @(T_TT_I t tt _)
 `compose` yoneda @Straight (fu @(->) () x)
 `compose` wr @into @(into () (tt o))
yi_yukl x = component @Straight @(->) @into @(T_TT_I t tt)
 `compose` wr @into @(T_TT_I t tt _)
 `compose` yoneda @Straight (fu @(->) () x)
 `compose` wr @into @(into () (tt o))
yi_yi_yukl x = component @Straight @(->) @into @(T_TT_I t tt)
 `compose` wr @into @(T_TT_I t tt _)
 `compose` yoneda @Straight (fu @(->) () x)
 `compose` wr @into @(into () (tt o))
yi_yi_yi_yukl x = component @Straight @(->) @into @(T_TT_I t tt)
 `compose` wr @into @(T_TT_I t tt _)
 `compose` yoneda @Straight (fu @(->) () x)
 `compose` wr @into @(into () (tt o))

-- TODO: try to generalize
yolk :: forall from into tt t a o .
 Precategory into =>
 Component Natural (->) (->) t (T_TT_I t tt) =>
 Covariant Yoneda from into t =>
 Castable Opposite into (Straight from (tt a) o) =>
 t a -> into (from (tt a) o) (t o)
yolk = yoneda @Straight @from @into `compose` unwrap
 `compose` component @Straight @(->) @(->) @t @(T_TT_I t tt)

yoklKL, yi_yoklKL, yi_yi_yoklKL :: forall from into tt t a o .
 Unlabelable into tt =>
 Component Natural from into (T_TT_I t tt) (TT_T_I t tt) =>
 Covariant Yoneda from into t =>
 Castable Opposite into (Straight from a (tt o)) =>
 Castable Straight into (TT_T_I t tt o) =>
 Castable Opposite into (T_TT_I t tt o) =>
 t a -> into (from a (tt o)) (Unlabeled tt (t o))
yoklKL x = unlabel
 `compose` unwrap @into @(TT_T_I t tt _)
 `compose` component @Straight @from @into @(T_TT_I t tt) @(TT_T_I t tt)
 `compose` wr @into @(T_TT_I t tt _)
 `compose` yoneda @Straight @from x

yi_yoklKL = yoklKL
yi_yi_yoklKL = yoklKL

yiokl :: forall from into tt t i a o .
 Component Natural from into (T_TT_I (U_I_II t i) tt) (U_I_II t i) =>
 Covariant Yoneda from into (U_I_II t i) =>
 Castable Opposite into (U_I_II from a (tt o)) =>
 Castable Straight into (U_I_II t i o) =>
 Castable Opposite into (T_TT_I (U_I_II t i) tt o) =>
 t i a -> into (from a (tt o)) (t i o)
yiokl x = unwrap @into @(U_I_II t i o)
 `compose` component @Straight @from @into @(T_TT_I (U_I_II t i) tt)
 `compose` wr @into @(T_TT_I (U_I_II t i) tt _)
 `compose` yoneda @Straight @from (U_I_II x)

yokl_yoklKL, yi_yokl_yoklKL, yi_yi_yokl_yoklKL, yi_yi_yi_yokl_yoklKL
 :: forall from into t tt ttt a o .
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

yi_yokl_yoklKL = yokl_yoklKL
yi_yi_yokl_yoklKL = yokl_yoklKL
yi_yi_yi_yokl_yoklKL = yokl_yoklKL

yoklKL_yokl :: forall from into t tt ttt a o .
 Unlabelable into ttt =>
 Covariant Yoneda from into t =>
 Covariant Endo Semi Functor from tt =>
 Covariant Endo Semi Functor from ttt =>
 Contravariant Endo Semi Functor (->) (U_II_I into (Unlabeled ttt (t o))) =>
 Component Natural from from (T_TT_I ttt tt) ttt =>
 Component Natural from into (T_TT_I t ttt) (TT_T_I t ttt) =>
 Castable Opposite into (That from (ttt a) (ttt o)) =>
 Castable Straight into (TT_T_I t ttt o) =>
 Castable Opposite into (T_TT_I t ttt o) =>
 Castable Opposite from (T_TT_I ttt tt o) =>
 t (ttt a) -> into (from a (tt o)) (Unlabeled ttt (t o))
yoklKL_yokl x = fai fokl (yoklKL @from @into x)

yoklKL_yoklKL :: forall from into t tt ttt a o .
 Unlabelable into ttt =>
 Covariant Yoneda from into t =>
 Covariant Endo Semi Functor from tt =>
 Covariant Endo Semi Functor from ttt =>
 Component Natural from into (T_TT_I t ttt) (TT_T_I t ttt) =>
 Component Natural from from (T_TT_I tt ttt) (TT_T_I tt ttt) =>
 Contravariant Endo Semi Functor (->) (U_II_I into (Unlabeled ttt (t (tt o)))) =>
 Castable Opposite from (T_TT_I tt ttt o) =>
 Castable Straight from (TT_T_I tt ttt o) =>
 Castable Straight into (TT_T_I t ttt (tt o)) =>
 Castable Opposite into (T_TT_I t ttt (tt o)) =>
 Castable Opposite into (Straight from (tt a) (ttt (tt o))) =>
 t (tt a) -> into (from a (ttt o)) (Unlabeled ttt (t (tt o)))
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
fio from = unwrap `compose` fo @_ @_ @(U_I_II _ _) from `compose` wr

fioi :: forall from into t a o i ii .
 Covariant Semi Functor from into (W_III_I_II t ii i) =>
 Wrapper into (W_III_I_II t ii i a) =>
 Wrapper into (W_III_I_II t ii i o) =>
 from a o -> into (t i a ii) (t i o ii)
fioi from = unwrap `compose` fo @_ @_ @(W_III_I_II _ _ _) from `compose` wr

foi :: forall from into t a o i .
 Covariant Semi Functor from into (U_II_I t i) =>
 Wrapper into (U_II_I t i a) =>
 Wrapper into (U_II_I t i o) =>
 from a o -> into (t a i) (t o i)
foi from = unwrap `compose` fo @_ @_ @(U_II_I _ _) from `compose` wr

fai :: forall from into t a o i .
 Contravariant Semi Functor from into (U_II_I t i) =>
 Wrapper into (U_II_I t i a) =>
 Wrapper into (U_II_I t i o) =>
 from a o -> into (t o i) (t a i)
fai from = unwrap `compose` fa @_ @_ @(U_II_I _ _) from `compose` wr

fai' :: forall from into t a o i .
 Contravariant Semi Functor from into (U_II_I t i) =>
 Contravariant Semi Functor into into (U_II_I t i) =>
 Wrapper into (U_II_I t i a) =>
 Wrapper into (U_II_I t i (Supertype a)) =>
 Wrapper into (U_II_I t i o) =>
 Wrapper into a =>
 from (Supertype a) o -> into (t o i) (t a i)
fai' from = fai @into unwrap `compose` unwrap
 `compose` fa @_ @_ @(U_II_I _ _) from `compose` wr

fio_fo :: forall from into t tt e a o .
 Covariant Semi Functor into into (U_I_II t e) =>
 Covariant Semi Functor from into tt =>
 Wrapper into (U_I_II t e (tt a)) =>
 Wrapper into (U_I_II t e (tt o)) =>
 from a o -> into (t e (tt a)) (t e (tt o))
fio_fo from = fio @into @into (fo @from @into from)

ho, hoo, hooo, hoooo, hooooo, hoooooo, yi_ho :: forall from into u i a o .
 Precategory from =>
 Precategory into =>
 Covariant Yoneda from into (U_I_II u i) =>
 Castable Straight into (U_I_II u i o) =>
 Castable Opposite into (U_I_II from a o) =>
 u i a -> into (from a o) (u i o)
ho x = unwrap `compose` (yo @from @into @(U_I_II u _) (U_I_II x))

hoo = ho
hooo = ho
hoooo = ho
hooooo = ho
hoooooo = ho
yi_ho = ho

ho', hoo', hooo', hoooo', hooooo', hoooooo' :: forall from into u i a o .
 Precategory from =>
 Precategory into =>
 Covariant Yoneda from into (U_I_II u i) =>
 Contravariant Semi Functor from into (U_II_I from o) =>
 Covariant Semi Functor from into (U_I_II from o) =>
 Castable Straight from a =>
 Castable Straight into (U_I_II u i o) =>
 Castable Opposite into (U_I_II from a o) =>
 Wrapper into (U_II_I from o a) =>
 Wrapper into (U_II_I from o (Supertype a)) =>
 u i a -> into (from (Supertype a) o) (u i o)
ho' x = unwrap `compose` yo @from @into @(U_I_II u _) (U_I_II x) `compose` fai @from yi'

hoo' = ho'
hooo' = ho'
hoooo' = ho'
hooooo' = ho'
hoooooo' = ho'

ha, haa, haaa, haaaa, haaaaa, haaaaaa, haaaaaaa, haaaaaaaa, haaaaaaaaa :: forall from u e a o .
 Contravariant Yoneda from (->) (U_II_I u e) =>
 u a e -> from o a -> u o e
ha x = unwrap `compose` ya @from @(->) @(U_II_I u _) (U_II_I x)

haa = ha
haaa = ha
haaaa = ha
haaaaa = ha
haaaaaa = ha
haaaaaaa = ha
haaaaaaaa = ha
haaaaaaaaa = ha

ha', haa', haaa', haaaa', haaaaa', haaaaaa', haaaaaaa', haaaaaaaa', haaaaaaaaa' :: forall from u e a o .
 Contravariant Yoneda from (->) (U_II_I u e) =>
 Castable Straight from o =>
 u a e -> from (Supertype o) a -> u o e
ha' x = unwrap `compose` ya @from @(->) @(U_II_I u _) (U_II_I x) `compose` fai @from yi'

haa' = ha'
haaa' = ha'
haaaa' = ha'
haaaaa' = ha'
haaaaaa' = ha'
haaaaaaa' = ha'
haaaaaaaa' = ha'
haaaaaaaaa' = ha'

-- This it the `right` version of this operator, however I cannot use it as I need
-- ha_ha :: forall from u uu a o e ee .
 -- Contravariant Yoneda u (->) (Opposite u e) =>
 -- Contravariant Semi Functor from u (Opposite uu ee) =>
 -- Wrapper u (Opposite uu ee o) =>
 -- Wrapper u (Opposite uu ee a) =>
 -- u (uu a ee) e -> from a o -> u (uu o ee) e
-- ha_ha x = fai @(->) @(->) fai (a @u x)

-- TODO: generalize
-- This is not `right` version, but I can use it as I want to
ha_ha :: forall from into u a o e ee .
 Category into =>
 Contravariant Yoneda from (->) (Opposite u e) =>
 Contravariant Yoneda into (->) (Opposite (->) (u o e)) =>
 u a e -> into ee (from o a) -> ee -> u o e
ha_ha = ha @into `compose` ha @from

-- TODO: generalize
ha'_ha :: forall from into u a o e ee .
 Category into =>
 Contravariant Yoneda from (->) (Opposite u e) =>
 Contravariant Yoneda into (->) (Opposite (->) (u o e)) =>
 Castable Straight into ee =>
 u a e -> into (Supertype ee) (from o a) -> ee -> u o e
ha'_ha = ha' @into `compose` ha @from

-- TODO: generalize
ha_ha' :: forall from into u a o e ee .
 Category into =>
 Contravariant Yoneda from (->) (Opposite u e) =>
 Contravariant Yoneda into (->) (Opposite (->) (u o e)) =>
 Castable Straight from o =>
 u a e -> into ee (from (Supertype o) a) -> ee -> u o e
ha_ha' = ha @into `compose` ha' @from

-- TODO: generalize
ha'_ha' :: forall from into u a o e ee .
 Category into =>
 Contravariant Yoneda from (->) (Opposite u e) =>
 Contravariant Yoneda into (->) (Opposite (->) (u o e)) =>
 Castable Straight into ee =>
 Castable Straight from o =>
 u a e -> into (Supertype ee) (from (Supertype o) a) -> ee -> u o e
ha'_ha' = ha' @into `compose` ha' @from

ho_ha, hoo_ha  :: forall from u uu o e ee a .
 Covariant Yoneda u (->) (Straight u e) =>
 Contravariant Yoneda u (->) (Opposite u e) =>
 Contravariant Semi Functor from u (Opposite uu ee) =>
 Contravariant Endo Semi Functor (->) (Opposite (->) (u e (uu a ee))) =>
 Wrapper u (U_II_I uu ee a) =>
 Wrapper u (U_II_I uu ee o) =>
 Wrapper from (U_I_II u e (uu a ee)) =>
 Wrapper from (U_I_II u (uu o ee) (uu a ee)) =>
 u e (uu o ee) -> from a o -> u e (uu a ee)
ho_ha x = fai @(->) @(->) fai (ho @u x)

hoo_ha = ho_ha

ho_ho :: forall from u uu o e ee a .
 Covariant Yoneda u from (Straight u e) =>
 Contravariant Yoneda (->) (->) (Opposite u e) =>
 Covariant Semi Functor from u (Straight uu ee) =>
 Covariant Endo Semi Functor (->) (Straight (->) (u e (uu a ee))) =>
 Contravariant Semi Functor (->) (->) (Opposite from (u e (uu ee o))) =>
 Wrapper u (Straight uu ee a) =>
 Wrapper u (Straight uu ee o) =>
 Wrapper from (Straight uu ee o) =>
 Wrapper from (Straight u e (uu ee o)) =>
 Wrapper from (Straight u (uu ee a) (uu ee o)) =>
 u e (uu ee a) -> from (from a o) (u e (uu ee o))
ho_ho x = fai fio (ho @u x)

ha_ho :: forall from u uu o e ee a .
 Covariant Yoneda u (->) (Straight u e) =>
 Contravariant Yoneda u (->) (Opposite u e) =>
 Covariant Semi Functor from u (Opposite uu ee) =>
 Contravariant Endo Semi Functor (->) (Opposite (->) (u e (uu a ee))) =>
 Wrapper u (U_II_I uu ee a) =>
 Wrapper u (U_II_I uu ee o) =>
 u (uu o ee) e -> from a o -> u (uu a ee) e
ha_ho x = fai @(->) @(->) foi (ha @u x)

ho_yo, hoo_yo, hooo_yo, hoooo_yo, hooooo_yo, hoooooo_yo :: forall from u t o e a .
 Covariant Yoneda from (->) (Straight u e) =>
 Contravariant Yoneda from (->) (Opposite u e) =>
 Covariant Endo Semi Functor from t =>
 Mapping Constant Straight from (->) t t =>
 u e (t a) -> from a o -> u e (t o)
ho_yo x = fai (fo @from) (ho @from x)

hoo_yo = ho_yo
hooo_yo = ho_yo
hoooo_yo = ho_yo
hooooo_yo = ho_yo
hoooooo_yo = ho_yo

ho'_yo :: forall from u t o e a .
 Covariant Yoneda from (->) (Straight u e) =>
 Contravariant Yoneda from (->) (Opposite u e) =>
 Contravariant Semi Functor from (->) (Opposite u (t a)) =>
 Covariant Endo Semi Functor from t =>
 -- Mapping Constant Straight from (->) t t =>
 Castable Straight from e =>
 u (Supertype e) (t a) -> from a o -> u e (t o)
ho'_yo x = fai (fo @from) (ho @from (fai @from yi' x))

ho_yioi :: forall from u t o e ee eee a .
 Covariant Yoneda from (->) (Straight u e) =>
 Contravariant Yoneda from (->) (Opposite u e) =>
 Covariant Endo Semi Functor from (W_III_I_II t eee ee) =>
 Wrapper from (W_III_I_II t eee ee a) =>
 Wrapper from (W_III_I_II t eee ee o) =>
 u e (t ee a eee) -> from a o -> u e (t ee o eee)
ho_yioi x = fai (fioi @from) (ho @from x)

ha_yo :: forall from u t o e a .
 Covariant Yoneda from (->) (Straight u e) =>
 Contravariant Yoneda from (->) (Opposite u e) =>
 Covariant Endo Semi Functor from t =>
 Mapping Constant Straight from (->) t t =>
 u (t a) e -> from o a -> u (t o) e
ha_yo x = fai (fo @from) (ha @from x)

ha_yioi :: forall from u t o e ee eee a .
 Covariant Yoneda from (->) (Straight u e) =>
 Contravariant Yoneda from (->) (Opposite u e) =>
 Covariant Endo Semi Functor from (W_III_I_II t eee ee) =>
 Wrapper from (W_III_I_II t eee ee a) =>
 Wrapper from (W_III_I_II t eee ee o) =>
 u (t ee a eee) e -> from o a -> u (t ee o eee) e
ha_yioi x = fai (fioi @from) (ha @from x)

ho_yu :: forall u t o e a .
 Covariant Yoneda (->) (->) (Straight u e) =>
 Contravariant Yoneda (->) (->) (Opposite u e) =>
 Covariant Endo Semi Functor (->) t =>
 Mapping Constant Straight (->) (->) t t =>
 Castable Opposite (->) (u () o) =>
 u e (t a) -> o -> u e (t o)
ho_yu x = fai @(->) @(->) (fu @(->)) (ho @(->) x)

-- TODO: replace with `ho'`
ho_yi' :: forall from u e a o .
 Covariant Endo Semi Functor from (That from a) =>
 Covariant Yoneda from (->) (U_I_II u e) =>
 Contravariant Semi Functor from (->) (U_II_I (->) (u e (Supertype o))) =>
 Contravariant Yoneda from (->) (U_II_I (->) (u e (Supertype o))) =>
 Castable Straight (->) (U_I_II u e o) =>
 Castable Straight from o =>
 Wrapper from (U_I_II from a o) =>
 Wrapper from (U_I_II from a (Supertype o)) =>
 u e a -> from a o -> u e (Supertype o)
ho_yi' x = fai @from (fio @from unwrap) (ho x)

-- TODO: replace with `ho'_ho`
ho_yi'_ho :: forall from u e a o .
 Covariant Yoneda from (->) (That u e) =>
 Castable Straight from a =>
 u e a -> from (Supertype a) o -> u e o
ho_yi'_ho x xx = x `ho` unwrap @from `ho` xx

u, uu, uuu, uuuu, uuuuu, uuuuuu, uuuuuuu,
 uuuuuuuu, uuuuuuuuu, uuuuuuuuuu :: forall from into i a o .
 Precategory into =>
 Covariant Yoneda from into (U_1_I from i) =>
 Castable Opposite into (U_I_II from a o) =>
 Castable Straight into (U_I_II from i o) =>
 Castable Opposite (->) (from () a) =>
 Castable Straight into (from () o) =>
 Castable Straight into (U_1_I from i o) =>
 Supertype (from () a) -> into (from a o) (Supertype (from () o))
u x = unwrap `compose` unwrap `compose` yo @from @into @(U_1_I from _)
 (U_1_I @from @i / wrap @(from _ _) x)
uu x = unwrap `compose` unwrap `compose` yo @from @into @(U_1_I from _)
 (U_1_I @from @i / wrap @(from _ _) x)
uuu x = unwrap `compose` unwrap `compose` yo @from @into @(U_1_I from _)
 (U_1_I @from @i / wrap @(from _ _) x)
uuuu x = unwrap `compose` unwrap `compose` yo @from @into @(U_1_I from _)
 (U_1_I @from @i / wrap @(from _ _) x)
uuuuu x = unwrap `compose` unwrap `compose` yo @from @into @(U_1_I from _)
 (U_1_I @from @i / wrap @(from _ _) x)
uuuuuu x = unwrap `compose` unwrap `compose` yo @from @into @(U_1_I from _)
 (U_1_I @from @i / wrap @(from _ _) x)
uuuuuuu x = unwrap `compose` unwrap `compose` yo @from @into @(U_1_I from _)
 (U_1_I @from @i / wrap @(from _ _) x)
uuuuuuuu x = unwrap `compose` unwrap `compose` yo @from @into @(U_1_I from _)
 (U_1_I @from @i / wrap @(from _ _) x)
uuuuuuuuu x = unwrap `compose` unwrap `compose` yo @from @into @(U_1_I from _)
 (U_1_I @from @i / wrap @(from _ _) x)
uuuuuuuuuu x = unwrap `compose` unwrap `compose` yo @from @into @(U_1_I from _)
 (U_1_I @from @i / wrap @(from _ _) x)

u' :: forall from into i a o .
 Precategory into =>
 Precategory from =>
 Covariant Yoneda from into (U_1_I from i) =>
 Contravariant Endo Semi Functor from (U_II_I from o) =>
 Castable Opposite into (U_I_II from a o) =>
 Castable Opposite (->) (from () a) =>
 Castable Straight into (from () o) =>
 Castable Straight from a =>
 Wrapper from (U_II_I from o a) =>
 Wrapper from (U_II_I from o (Supertype a)) =>
 Castable Straight into (U_I_II from i o) =>
 Castable Straight into (U_1_I from i o) =>
 Contravariant Yoneda from (->) (U_II_I into (Supertype (from () o))) =>
 Supertype (from () a) -> into (from (Supertype a) o) (Supertype (from () o))
u' x = u @from @into @i x `yai_yai` unwrap @from @a

v :: (a -> o) -> a -> e -> o
v from x y = from (constant x y)

vv = v
vvv = v
vvvv = v
vvvvv = v
vvvvvv = v
vvvvvvv = v
vvvvvvvv = v
vvvvvvvvv = v

ro :: forall into hom t i .
 Category into =>
 Covariant (Representable hom) into into t =>
 Castable Straight into (Straight hom (Representation t) i) =>
 into (t i) (hom (Representation t) i)
ro = unwrap `compose` map @Straight @Straight @into @into @t @(Straight hom (Representation t)) identity

ra :: forall into hom t i .
 Category into =>
 Contravariant (Representable hom) into into t =>
 Castable Straight into (Opposite hom (Representation t) i) =>
 into (t i) (hom i (Representation t))
ra = unwrap `compose` map @Opposite @Straight @into @into @t @(Opposite hom (Representation t)) identity

lj :: forall from into t tt a o .
 Adjoint Functor from into t tt =>
 Castable Straight into ((T_TT_I tt t) a) =>
 Castable Opposite into (Identity a) =>
 from (t a) o -> into a (tt o)
lj from = fo from
 `compose` unwrap @into
 `compose` component @Straight @from @into @Identity @(tt `T_TT_I` t)
 `compose` wr @into

ilj :: forall from into t tt e ee a o .
 Adjoint Functor from into (U_I_II t e) (U_I_II tt ee) =>
 Castable Straight into ((T_TT_I (U_I_II tt ee) (U_I_II t e)) a) =>
 Castable Straight into (U_I_II tt ee o) =>
 Castable Opposite into (Identity a) =>
 Castable Straight from (U_I_II t e a) =>
 from (t e a) o -> into a (tt ee o)
ilj from = unwrap @into @(U_I_II tt _ _)
 `compose` fo (from `compose` unwrap @from @(U_I_II t _ _))
 `compose` unwrap @into @(T_TT_I _ _ _)
 `compose` component @Straight @from @into @Identity @(U_I_II tt ee `T_TT_I` U_I_II t e)
 `compose` wr @into

_j :: forall from into t tt e a o .
 Adjoint Functor from into (U_II_I t e) (U_I_II tt e) =>
 Castable Straight into ((U_I_II tt e `T_TT_I` U_II_I t e) a) =>
 Castable Straight into (U_I_II tt e o) =>
 Castable Opposite into (Identity a) =>
 Castable Straight from (U_II_I t e a) =>
 from (t a e) o -> into a (tt e o)
_j from = unwrap @into @(U_I_II tt _ _)
 `compose` fo (from `compose` unwrap @from @(U_II_I t _ _))
 `compose` unwrap @into @(T_TT_I _ _ _)
 `compose` component @Straight @from @into @Identity @(U_I_II tt e `T_TT_I` U_II_I t e)
 `compose` wr @into

j' :: forall from into t tt e a o .
 Adjoint Functor from into (U_II_I t e) (U_I_II tt e) =>
 Castable Opposite from ((T_TT_I (U_II_I t e) (U_I_II tt e)) o) =>
 Castable Straight from (Identity o) =>
 Castable Opposite from (U_II_I t e a) =>
 Castable Opposite into (U_I_II tt e o) =>
 into a (tt e o) -> from (t a e) o
j' from = unwrap @from
 `compose` component @Straight @into @from @(U_II_I t e `T_TT_I` U_I_II tt e) @Identity
 `compose` wr @from @((U_II_I t e `T_TT_I` U_I_II tt e) _)
 `compose` fo (wr @into @(U_I_II tt e _) `compose` from)
 `compose` wr @from @(U_II_I t e _)

j'_j' :: forall from into t tt ttt tttt e ee a o .
 Adjoint Functor from from (U_II_I t ee) (U_I_II tttt ee) =>
 Adjoint Functor from into (U_II_I ttt e) (U_I_II tt e) =>
 Castable Opposite from (U_II_I t ee a) =>
 Castable Opposite into (U_I_II tt e o) =>
 Castable Opposite into (U_I_II tt e (tttt ee o)) =>
 Castable Straight from (Identity o) =>
 Castable Straight from (Identity (tttt ee o)) =>
 Castable Opposite from (Identity (U_I_II tttt ee o)) =>
 Castable Opposite from (U_II_I ttt e a) =>
 Castable Opposite from (U_I_II tttt ee o) =>
 Castable Opposite from (U_II_I t ee (ttt a e)) =>
 Castable Opposite from ((T_TT_I (U_II_I ttt e) (U_I_II tt e)) (tttt ee o)) =>
 Castable Opposite from ((T_TT_I (U_II_I t ee) (U_I_II tttt ee)) o) =>
 into a (tt e (tttt ee o)) -> from (t (ttt a e) ee) o
j'_j' = j' @from @from `compose` j' @from @into

-- TODO: define `j'_j'_j'`, `j'_j'_j'_j'`, `j'_j'_j'_j'_j',

rj :: forall from into t tt a o .
 Adjoint Functor from into t tt =>
 Castable Opposite from ((T_TT_I t tt) o) =>
 Castable Straight from (Identity o) =>
 into a (tt o) -> from (t a) o
rj from = unwrap @from @(Identity _)
 `compose` component @Straight @into @from @(t `T_TT_I` tt) @Identity
 `compose` wr @from @((t `T_TT_I` tt) _)
 `compose` fo @into @from from

rij :: forall from into t tt e ee a o .
 Adjoint Functor from into (U_I_II t ee) (U_I_II tt e) =>
 Castable Opposite from ((T_TT_I (U_I_II t ee) (U_I_II tt e)) o) =>
 Castable Straight from (Identity o) =>
 Castable Opposite from (U_I_II t ee a) =>
 Castable Opposite into (U_I_II tt e o) =>
 into a (tt e o) -> from (t ee a) o
rij from = unwrap @from
 `compose` component @Straight @into @from @(U_I_II t ee `T_TT_I` U_I_II tt e) @Identity
 `compose` wr @from @((U_I_II t ee `T_TT_I` U_I_II tt e) _)
 `compose` fo (wr @into @(U_I_II tt e _) `compose` from)
 `compose` wr @from @(U_I_II t ee _)

fr :: forall into a o oo .
 Limit Straight into into =>
 Covariant Functor into into (That (Product into) o) =>
 Covariant Functor into into (This (Product into) (Product into a a)) =>
 (forall e ee . Wrapper into (That (Product into) e ee)) =>
 (forall e ee . Wrapper into (This (Product into) e ee)) =>
 (forall e . Wrapper into (Both (Product into) e)) =>
 (forall e . Wrapper into (Identity e)) =>
 into a o -> into a oo -> into a (Product into o oo)
fr from_left from_right =
 _i (map @Straight @Straight (wrapped (right @Straight from_right))) `compose`
 i_ (map @Straight @Straight (wrapped (left @Straight from_left))) `compose`
 wrapped (map @Straight @Straight @into @into @Identity @(Both (Product into)) identity) `compose`
 wrapped (map @Straight @Straight @into @into @Identity @(Both (Product into)) identity)

cn :: forall into a aa o oo .
 Cone Straight into into (Object Straight into) =>
 Functor Straight into into (That (Product into) o) =>
 Functor Straight into into (That (Product into) aa) =>
 Functor Straight into into (This (Product into) aa) =>
 Wrapper into (That (Product into) o aa) =>
 Wrapper into (That (Product into) o oo) =>
 Wrapper into (This (Product into) aa o) =>
 Wrapper into (This (Product into) aa a) =>
 into a o -> into aa oo -> into (Product into a aa) (Product into o oo)
cn from_left from_right = fio from_right `compose` foi from_left

cn' :: forall into e a aa o oo .
 Cone Straight into into (Object Straight into) =>
 Functor Straight into into (That (Product into) o) =>
 Functor Straight into into (That (Product into) aa) =>
 Functor Straight into into (This (Product into) aa) =>
 Wrapper into (That (Product into) o aa) =>
 Wrapper into (That (Product into) o oo) =>
 Wrapper into (This (Product into) aa o) =>
 Wrapper into (This (Product into) aa a) =>
 Castable Straight into e =>
 (Supertype e ~ (Product into a aa)) =>
 into a o -> into aa oo -> into e (Product into o oo)
cn' from_left from_right = fio from_right `compose` foi from_left `compose` unwrap @into

-- TODO: try to generalize
cn_dp, yi_cn_dp :: forall t a aa o oo .
 Mapping Straight Straight (->) (->) (Day Straight (->) (Product (->)) (Product (->)) t t o oo) t =>
 Arrow a (t o) -> Arrow aa (t oo) -> Arrow (Product (->) a aa) (t (Product Arrow o oo))
cn_dp from_left from_right = dp `compose` cn from_left from_right

yi_cn_dp = cn_dp

-- TODO: try to generalize
cn'_dp, yi_cn'_dp, yi_yi_cn'_dp, yi_yi_yi_cn'_dp :: forall e t a aa o oo .
 Mapping Straight Straight (->) (->) (Day Straight (->) (Product (->)) (Product (->)) t t o oo) t =>
 Castable Straight (->) e =>
 (Supertype e ~ Product (->) a aa) =>
 Arrow a (t o) -> Arrow aa (t oo) -> Arrow e (t (Product Arrow o oo))
cn'_dp from_left from_right = dp `compose` cn from_left from_right `compose` unwrap

yi_cn'_dp = cn'_dp
yi_yi_cn'_dp = cn'_dp
yi_yi_yi_cn'_dp = cn'_dp

-- TODO: try to generalize
lm, yi_lm, yi_yi_lm, yi_yi_yi_lm, yi_yi_yi_yi_lm :: forall o oo .
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
 (forall e . Wrapper (->) (Identity e)) =>
 Castable Opposite (->) ((->) () o) =>
 Castable Opposite (->) ((->) () oo) =>
 Castable Straight (->) ((->) () (Product (->) o oo)) =>
 Supertype ((->) () o) -> Supertype ((->) () oo) -> Supertype ((->) () (Product (->) o oo))
lm from_left from_right = unwrap /
 _i (map @Straight @Straight (wrapped (right @Straight (wr @_ @((->) () oo) from_right)))) `compose`
 i_ (map @Straight @Straight (wrapped (left @Straight (wr @_ @((->) () o) from_left)))) `compose`
 wrapped (map @Straight @Straight @(->) @(->) @Identity @(Both (Product (->))) identity) `compose`
 wrapped (map @Straight @Straight @(->) @(->) @Identity @(Both (Product (->))) identity)

yi_lm = lm
yi_yi_lm = lm
yi_yi_yi_lm = lm
yi_yi_yi_yi_lm = lm

rf, yi_rf, yi_yi_rf, yi_yi_yi_rf :: forall from i o oo .
 Category from =>
 Limit Opposite from from =>
 Covariant Functor from from (That (Sum from) o) =>
 Covariant Functor from from (This (Sum from) (Sum from i i)) =>
 (forall ee eee . Wrapper from (That (Sum from) ee eee)) =>
 (forall ee eee . Wrapper from (This (Sum from) ee eee)) =>
 (forall ee . Wrapper from (Both (Sum from) ee)) =>
 (forall ee . Wrapper from (Identity ee)) =>
 from o i -> from oo i -> from (Sum from o oo) i
rf from_left from_right =
 wrapped (map @Opposite @Opposite @from @from @Identity @(Both (Sum from)) identity) `compose`
 wrapped (map @Opposite @Opposite @from @from @Identity @(Both (Sum from)) identity) `compose`
 i_ (map @Straight @Straight (wrapped (left @Opposite from_left))) `compose`
 _i (map @Straight @Straight (wrapped (right @Opposite from_right))) -- `compose`

yi_rf = rf
yi_yi_rf = rf
yi_yi_yi_rf = rf

rf', yi_rf', yi_yi_rf', yi_yi_yi_rf' :: forall from e i o oo .
 Category from =>
 Limit Opposite from from =>
 Covariant Functor from from (That (Sum from) o) =>
 Covariant Functor from from (This (Sum from) (Sum from i i)) =>
 (forall ee eee . Wrapper from (That (Sum from) ee eee)) =>
 (forall ee eee . Wrapper from (This (Sum from) ee eee)) =>
 (forall ee . Wrapper from (Both (Sum from) ee)) =>
 (forall ee . Wrapper from (Identity ee)) =>
 (Supertype e ~ (Sum from o oo)) =>
 Castable Straight from e =>
 from o i -> from oo i -> from e i
rf' from_left from_right = rf from_left from_right `compose` unwrap

yi_rf' = rf'
yi_yi_rf' = rf'
yi_yi_yi_rf' = rf'

yi'_rf' :: forall from e ee i o oo .
 Category from =>
 Limit Opposite from from =>
 Covariant Functor from from (That (Sum from) o) =>
 Covariant Functor from from (This (Sum from) (Sum from i i)) =>
 (forall ee eee . Wrapper from (That (Sum from) ee eee)) =>
 (forall ee eee . Wrapper from (This (Sum from) ee eee)) =>
 (forall ee . Wrapper from (Both (Sum from) ee)) =>
 (forall ee . Wrapper from (Identity ee)) =>
 (Supertype e ~ ee) =>
 (Supertype ee ~ (Sum from o oo)) =>
 Castable Straight from e =>
 Castable Straight from ee =>
 from o i -> from oo i -> from e i
yi'_rf' from_left from_right = rf' from_left from_right `compose` yi'

-- TODO: to test
rwr_rf :: forall from into r o a aa .
 Category from =>
 Limit Opposite from into =>
 Covariant Functor into into (That (Sum into) a) =>
 Covariant Functor into into (This (Sum into) (Sum into (Supertype r) (Supertype r))) =>
 Castable Opposite into (Both (Sum into) (Sum into (Supertype r) (Supertype r))) =>
 Castable Opposite into (That (Sum into) a aa) =>
 Castable Straight into (That (Sum into) (Supertype r) (Supertype r)) =>
 Castable Straight into (This (Sum into) (Supertype r) (Supertype r)) =>
 Castable Opposite into (Both (Sum into) (Supertype r)) =>
 Castable Straight into (That (Sum into) a (Sum into (Supertype r) (Supertype r))) =>
 Castable Opposite into (This (Sum into) (Sum into (Supertype r) (Supertype r)) a) =>
 Castable Straight into (This (Sum into) (Sum into (Supertype r) (Supertype r)) (Sum into (Supertype r) (Supertype r))) =>
 (Supertype o ~ Sum into a aa) =>
 (forall eeee . Wrapper into (Identity eeee)) =>
 Castable Opposite into r =>
 Castable Straight into o =>
 from a (Supertype r) -> from aa (Supertype r) -> into o r
rwr_rf from_left from_right = rwr /
 wrapped (map @Opposite @Opposite @from @into @Identity @(Both (Sum into)) identity) `compose`
 wrapped (map @Opposite @Opposite @from @into @Identity @(Both (Sum into)) identity) `compose`
 i_ (map @Straight @Straight (wrapped (left @Opposite from_left))) `compose`
 _i (map @Straight @Straight (wrapped (right @Opposite from_right)))

dp :: forall u e ee t .
 Mapping Straight Straight (->) (->) (Day Straight (->) u LM t t e ee) t =>
 u (t e) (t ee) -> t (e `LM` ee)
dp = day @Straight @(->) @t @u @LM identity identity

ds :: forall u e ee t .
 Mapping Straight Straight (->) (->) (Day Straight (->) u ML t t e ee) t =>
 u (t e) (t ee) -> t (e `ML` ee)
ds = day @Straight @(->) @t @u @ML identity identity

dw :: forall u e ee t .
 Mapping Straight Straight (->) (->)
 (Day Straight (->) u MLM t t e ee) t =>
 u (t e) (t ee) -> t (ML e ee `ML` LM e ee)
dw = day @Straight @(->) @t @u @MLM identity unwrap

dp_dp :: forall u e ee t tt .
 Mapping Straight Straight (->) (->)
 (Day Straight (->) u LM t t (tt e) (tt ee)) t =>
 Mapping Straight Straight (->) (->)
 (Day Straight (->) LM LM tt tt e ee) tt =>
 u (t (tt e)) (t (tt ee)) -> t (tt (e `LM` ee))
dp_dp = day @Straight @(->) @t @u @LM identity
 (day @Straight @(->) @tt @LM @LM identity identity)

yi', yii', yiii', yiiii', yiiiii', yi_yi', yi_yi_yi', yi_yi_yi_yi' ::
 Castable Straight into i =>
 into i (Supertype i)
yi' = unwrap

yii' = yi'
yiii' = yi'
yiiii' = yi'
yiiiii' = yi'
yi_yi' = yi'
yi_yi_yi' = yi'
yi_yi_yi_yi' = yi'

w_rw :: forall into a o .
 Precategory into =>
 Castable Opposite into o =>
 Castable Straight into a =>
 into (Supertype a) (Supertype o) -> into a o
w_rw into = wr @into `compose` into `compose` unwrap @into

rw_w :: forall into a o .
 Precategory into =>
 Castable Opposite into a =>
 Castable Straight into o =>
 into a o -> into (Supertype a) (Supertype o)
rw_w into = unwrap @into `compose` into `compose` wr @into

yi'_yi', yii'_yi', yiii'_yi', yi_yi'_yi', yi_yi_yi'_yi' :: forall into a .
 Precategory into =>
 Castable Straight into a =>
 Castable Straight into (Supertype a) =>
 into a (Supertype (Supertype a))
yi'_yi' = unwrap @into `compose` unwrap @into

yii'_yi' = yi'_yi'
yiii'_yi' = yi'_yi'
yi_yi'_yi' = yi'_yi'
yi_yi_yi'_yi' = yi'_yi'

yi'_yi'_yi', yi_yi'_yi'_yi' :: forall into a .
 Precategory into =>
 Castable Straight into a =>
 Castable Straight into (Supertype a) =>
 Castable Straight into (Supertype (Supertype a)) =>
 into a (Supertype (Supertype (Supertype a)))
yi'_yi'_yi' = unwrap @into `compose` unwrap @into `compose` unwrap @into

yi_yi'_yi'_yi' = yi'_yi'_yi'

-- TODO: try to generalize
yi'_yi'_yi'_o :: forall a e o oo .
 Castable Straight (->) a =>
 Castable Straight (->) (Supertype a) =>
 Castable Straight (->) (Supertype (Supertype a)) =>
 ((e `ARR` o) ~ Supertype (Supertype (Supertype a))) =>
 a `ARR` e `ARR` (o `ARR` oo) `ARR` oo
yi'_yi'_yi'_o x e f = f (unwrap (unwrap (unwrap x)) e)

-- TODO: define `rw_o`
-- TODO: define `rw_rw_o`
-- TODO: define `rw_ha`
-- TODO: define `rw_rw_ha`
-- TODO: define `rw_rw_rw_ha`

ho_yokl, hoo_yokl, hooo_yokl, hoooo_yokl, hooooo_yokl, hoooooo_yokl, hooooooo_yokl, hoooooooo_yokl, hooooooooo_yokl :: forall from u t tt a o e .
 Covariant Endo Semi Functor from tt =>
 Covariant Endo Semi Functor from t =>
 Mapping Straight Straight from from (T_TT_I t tt) t =>
 Covariant Yoneda from (->) (Straight u e) =>
 (forall ee . Wrapper from (T_TT_I t tt ee)) =>
 u e (t a) -> from a (tt o) -> u e (t o)
ho_yokl x = fai fokl (ho @from x)

hoo_yokl = ho_yokl
hooo_yokl = ho_yokl
hoooo_yokl = ho_yokl
hooooo_yokl = ho_yokl
hoooooo_yokl = ho_yokl
hooooooo_yokl = ho_yokl
hoooooooo_yokl = ho_yokl
hooooooooo_yokl = ho_yokl

ho_yukl, hoo_yukl, hooo_yukl, hoooo_yukl, hooooo_yukl, hoooooo_yukl, hooooooo_yukl, hoooooooo_yukl, hooooooooo_yukl :: forall from t tt a o e .
 Covariant Endo Semi Functor from tt =>
 Covariant Endo Semi Functor from t =>
 Mapping Constant Straight from from t t =>
 Mapping Straight Straight from from (T_TT_I t tt) t =>
 Covariant Yoneda from (->) (Straight from e) =>
 Castable Opposite from (T_TT_I t t o) =>
 Castable Opposite (->) (from () (tt o)) =>
 (forall ee . Wrapper from (T_TT_I t tt ee)) =>
 from e (t a) -> Supertype (from () (tt o)) -> from e (t o)
ho_yukl x = fai (fukl @from @t @tt) (ho @from x)

hoo_yukl x = fai (fukl @from @t @tt) (ho @from x)
hooo_yukl x = fai (fukl @from @t @tt) (ho @from x)
hoooo_yukl x = fai (fukl @from @t @tt) (ho @from x)
hooooo_yukl x = fai (fukl @from @t @tt) (ho @from x)
hoooooo_yukl x = fai (fukl @from @t @tt) (ho @from x)
hooooooo_yukl x = fai (fukl @from @t @tt) (ho @from x)
hoooooooo_yukl x = fai (fukl @from @t @tt) (ho @from x)
hooooooooo_yukl x = fai (fukl @from @t @tt) (ho @from x)

ha_yokl :: forall from u t tt a o e .
 Covariant Functor (->) (->) tt =>
 Covariant Functor from (->) t =>
 Covariant Functor from (->) tt =>
 Covariant Functor from from tt =>
 Covariant Functor from from t =>
 Mapping Straight Straight from from (T_TT_I t tt) t =>
 Contravariant Yoneda from (->) (U_II_I (->) (tt o)) =>
 Contravariant Yoneda from (->) (U_II_I u e) =>
 (forall ee . Wrapper from (T_TT_I t tt ee)) =>
 u (t o) e -> from a (tt o) -> u (t a) e
ha_yokl x = fai fokl (ha @from x)

-- TODO: try to gereralize
yokl_ha, yi_yokl_ha, yi_yi_yokl_ha, yi_yi_yi_yokl_ha :: forall from t tt a o e .
 Covariant Functor (->) (->) tt =>
 Contravariant Functor (->) (->) (Opposite from (t o)) =>
 Covariant Functor from from (Straight from e) =>
 Contravariant Functor from from (Opposite from o) =>
 Covariant Functor (->) from t =>
 Covariant Functor from from t =>
 Covariant Functor (->) (->) t =>
 Covariant Functor (->) from tt =>
 Covariant Functor from from tt =>
 Covariant Yoneda from from t =>
 Contravariant Yoneda from (->) (Opposite from (tt o)) =>
 Mapping Straight Straight (->) from (T_TT_I t tt) t =>
 (forall ee . Wrapper from ((t `T_TT_I` tt) ee)) =>
 Wrapper from (U_II_I from o a) =>
 Wrapper from (U_II_I from e (tt o)) =>
 Wrapper from (U_I_II from e (tt o)) =>
 Wrapper from (U_II_I from o e) =>
 Wrapper from (U_I_II from e a) =>
 t e -> from a (tt o) -> from (from e a) (t o)
yokl_ha x f = yokl x `compose` fio f

yi_yokl_ha = yokl_ha
yi_yi_yokl_ha = yokl_ha
yi_yi_yi_yokl_ha = yokl_ha

yokl_u :: forall from t tt a o e .
  Precategory from =>
  Covariant Yoneda from from t =>
  Mapping Straight Straight from from (U_I_II from e) (U_I_II from e) =>
  Mapping Constant Straight from from (U_I_II from e) (U_I_II from e) =>
  Covariant Semi Functor from from t =>
  Covariant Semi Functor (->) from t =>
  Covariant Semi Functor from (->) tt =>
  Covariant Semi Functor (->) from tt =>
  Mapping Straight Straight (->) from (T_TT_I t tt) t =>
  (forall ee . Wrapper from ((t `T_TT_I` tt) ee)) =>
  Castable Opposite from (T_TT_I t tt o) =>
  Wrapper from (U_I_II from e (tt o)) =>
  Castable Opposite from (U_I_II from e a) =>
  Castable Opposite (->) (from () (tt o)) =>
  t e -> Supertype (from () (tt o)) -> from (from e a) (t o)
yokl_u x f = yokl @_ @_ @tt x `compose` _i (fu @from f)

-- yokl_o :: forall from u t tt a o e .
 -- Category from =>
 -- -- Covariant Endo Semi Functor from tt =>
 -- Covariant Functor from from (Straight u e) =>
 -- Covariant Functor (->) u t =>
 -- Covariant Functor u u t =>
 -- -- Mapping Straight Straight from from (T_TT_I t tt) t =>
 -- Covariant Yoneda from u t =>
 -- Covariant Yoneda u from (Straight u e) =>
 -- Covariant Yoneda from from (Opposite u (t o)) =>
 -- -- Covariant Yoneda from from t =>
 -- -- (forall ee . Wrapper from (T_TT_I t tt ee)) =>
 -- -- t (from a o) -> from (u e a) (t o)
 -- t (u e a) -> u (from a o) (t o)
-- yokl_o x = fai fio (yokl @from @u x)

ho_yoklKL, hoo_yoklKL :: forall from u t tt a o e .
 Unlabelable from tt =>
 Covariant Semi Functor from (->) (Straight u e) =>
 Covariant Endo Semi Functor from tt =>
 Covariant Endo Semi Functor from t =>
 Mapping Straight Straight from from (T_TT_I t tt) (TT_T_I t tt) =>
 Covariant Yoneda from (->) (Straight u e) =>
 (forall ee . Wrapper from (T_TT_I t tt ee)) =>
 (forall ee . Wrapper from (TT_T_I t tt ee)) =>
 u e (t a) -> from a (tt o) -> u e (Unlabeled tt (t o))
ho_yoklKL x = fio @from unlabel `compose` fai foklKL (ho @from x)

hoo_yoklKL = ho_yoklKL

ha_yukl :: forall from t tt a o e .
 Covariant Functor (->) (->) tt =>
 Covariant Functor from from t =>
 Covariant Functor from from tt =>
 Contravariant Yoneda from (->) (U_II_I from (tt o)) =>
 Mapping Straight Straight from from (T_TT_I tt t) tt =>
 Mapping Constant Straight from from tt tt =>
 Castable Opposite from (T_TT_I tt t o) =>
 (forall ee . Wrapper from (T_TT_I tt t ee)) =>
 Castable Opposite from (T_TT_I tt tt o) =>
 Castable Opposite (->) (from () (t o)) =>
 Supertype (from () (t o)) -> from e (tt a) -> from e (tt o)
ha_yukl = ha `compose` fukl @from @tt @t

fr_dp :: forall from t i o oo .
 Category from =>
 Limit Straight from (->) =>
 Covariant Functor (->) (->) (That (LM) o) =>
 Covariant Functor (->) (->) (This (LM) (LM i i)) =>
 Covariant Monoidal Functor (->) LM LM t =>
 Castable Straight (->) (Both (LM) (LM i i)) =>
 Castable Straight (->) (That (LM) o oo) =>
 Castable Opposite (->) (This (LM) i i) =>
 Castable Opposite (->) (That (LM) i i) =>
 Castable Straight (->) (Both (LM) i) =>
 Castable Straight (->) (This (LM) (LM i i) o) =>
 Castable Opposite (->) (This (LM) (LM i i) (LM i i)) =>
 Wrapper (->) (That (LM) o (LM i i)) =>
 (forall e . Wrapper (->) (Identity e)) =>
 from i (t o) -> from i (t oo) -> i -> t (LM o oo)
fr_dp from_left from_right = dp `compose`
 _i (map @Straight @Straight (wrapped (right @Straight from_right))) `compose`
 i_ (map @Straight @Straight (wrapped (left @Straight from_left))) `compose`
 wrapped (map @Straight @Straight @from @(->) @Identity @(Both (LM)) identity) `compose`
 wrapped (map @Straight @Straight @from @(->) @Identity @(Both (LM)) identity)

lm_dp, yi_lm_dp, yi_yi_lm_dp, yi_yi_yi_lm_dp, yi_yi_yi_yi_lm_dp :: forall o oo t .
 Covariant Monoidal Functor (->) LM LM t =>
 t o -> t oo -> t (o `LM` oo)
lm_dp from_left from_right = dp (lm from_left from_right)

yi_lm_dp = lm_dp
yi_yi_lm_dp = lm_dp
yi_yi_yi_lm_dp = lm_dp
yi_yi_yi_yi_lm_dp = lm_dp

lm_ds, yi_lm_ds, yi_yi_lm_ds :: forall o oo t .
 Covariant Monoidal Functor (->) LM ML t =>
 t o -> t oo -> t (o `ML` oo)
lm_ds from_left from_right = ds (lm from_left from_right)

yi_lm_ds = lm_ds
yi_yi_lm_ds = lm_ds

lm_dp_dp :: forall o oo t tt .
 Covariant Monoidal Functor (->) LM LM t =>
 Covariant Monoidal Functor (->) LM LM tt =>
 t (tt o) -> t (tt oo) -> t (tt (o `LM` oo))
lm_dp_dp from_left from_right = dp_dp @LM (lm from_left from_right)

-- TODO: generalize
dp_yo :: forall from e ee r t .
 Covariant Monoidal Functor from LM LM t =>
 t e `LM` t ee -> from (e `LM` ee) r -> t r
dp_yo x f = day @Straight @from @t @LM @LM identity f x

-- TODO: generalize
dp_yokl :: forall e ee from into t tt o .
 Covariant Monoidal Functor (->) LM LM t =>
 Covariant Yoneda from into t =>
 Component Natural (->) into (T_TT_I t tt) t =>
 Castable Opposite into (Straight from (e `LM` ee) (tt o)) =>
 Castable Opposite into (T_TT_I t tt o) =>
 t e `LM` t ee -> into (from (e `LM` ee) (tt o)) (t o)
dp_yokl = yokl @from @into `compose` dp

-- TODO: generalize
dp_yoklKL :: forall e ee from into t tt o .
 Unlabelable into tt =>
 Component Natural from into (T_TT_I t tt) (TT_T_I t tt) =>
 Covariant Monoidal Functor (->) LM LM t =>
 Covariant Yoneda from into t =>
 Castable Opposite into (Straight from (e `LM` ee) (tt o)) =>
 Castable Opposite into (T_TT_I t tt o) =>
 Castable Straight into (TT_T_I t tt o) =>
 t e `LM` t ee -> into (from (e `LM` ee) (tt o)) (Unlabeled tt (t o))
dp_yoklKL = yoklKL @from @into `compose` dp

-- TODO: generalize
dp_dp_yo :: forall from e ee r t tt .
 Covariant Monoidal Functor (->) LM LM t =>
 Covariant Monoidal Functor from LM LM tt =>
 t (tt e) `LM` t (tt ee) -> from (e `LM` ee) r -> t (tt r)
dp_dp_yo x f = day @Straight @(->) @t @LM @LM identity
 (day @Straight @from @tt @LM @LM identity f) x

jt :: forall into f g e .
 Component Natural (->) into (f `T_TT_I` g) (f `JT` g) =>
 Castable Opposite into ((f `T_TT_I` g) e) =>
 into (f (g e)) ((f `JT` g) e)
jt = component @Straight @(->) @into @(f `T_TT_I` g) @(f `JT` g) @e
 `compose` wr @into @((f `T_TT_I` g) e)

-- TODO: generalize
dp_dp_jt :: forall e ee t tt .
 Component Natural (->) (->) (t `T_TT_I` tt) (t `JT` tt) =>
 Covariant Monoidal Functor (->) LM LM t =>
 Covariant Monoidal Functor (->) LM LM tt =>
 t (tt e) `LM` t (tt ee) -> (t `JT` tt) (e `LM` ee)
dp_dp_jt = jt `compose` day @Straight @(->) @t @LM @LM identity
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

-- TODO: generalize
rwr_fio :: forall into w o u e ee .
 Covariant Endo Semi Functor into (U_I_II u o) =>
 Castable Straight into (U_I_II u o ee) =>
 Castable Opposite into (U_I_II u o e) =>
 Castable Opposite into (w u o ee) =>
 Castable Straight into (w u o e) =>
 (Supertype (w u o e) ~ u o e) =>
 (Supertype (w u o ee) ~ u o ee) =>
 into e ee -> into (w u o e) (w u o ee)
rwr_fio = rwr `compose` _i `compose` fo

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
rwr_yoi x = wr @into `compose` yoi (unwrap x)

-- -- TODO: generalize
-- o_rwr_yoi :: forall from into w a o u e ee .
--  Precategory into =>
--  Covariant Endo Semi Functor into (U_II_I u o) =>
--  Covariant Yoneda into (->) (U_I_II from a) =>
--  Castable Straight into (w u e o) =>
--  Castable Opposite into (w u ee o) =>
--  Castable Straight into (U_II_I u o ee) =>
--  Castable Opposite into (U_II_I u o e) =>
--  (Supertype (w u e o) ~ u e o) =>
--  (Supertype (w u ee o) ~ u ee o) =>
--  from a (w u e o) -> into e ee -> from a (w u ee o)
-- o_rwr_yoi x f = x `ho` rwr_foi @into @w @o @u @e @ee f

-- -- TODO: generalize
-- o_rwr_yio :: forall from into w a o u e ee .
--  Precategory into =>
--  Covariant Endo Semi Functor into (U_I_II u o) =>
--  Covariant Yoneda into (->) (U_I_II from a) =>
--  Castable Straight into (w u o e) =>
--  Castable Opposite into (w u o ee) =>
--  Castable Straight into (U_I_II u o ee) =>
--  Castable Opposite into (U_I_II u o e) =>
--  (Supertype (w u o e) ~ u o e) =>
--  (Supertype (w u o ee) ~ u o ee) =>
--  from a (w u o e) -> into e ee -> from a (w u o ee)
-- o_rwr_yio x f = x `ho` rwr_fio @into @w @o @u @e @ee f

-- yokl_rwr_yoi :: forall into w t o u e ee .
--  Covariant Yoneda into (->) t =>
--  Covariant Endo Semi Functor (->) t =>
--  Covariant Endo Semi Functor (->) (w u ee) =>
--  Covariant Endo Semi Functor into (U_II_I u o) =>
--  Component Natural (->) (->) (T_TT_I t (w u ee)) t =>
--  (Supertype (w u e o) ~ u e o) =>
--  (Supertype (w u ee o) ~ u ee o) =>
--  Castable Opposite (->) (into () ee) =>
--  Castable Opposite into (U_II_I u o e) =>
--  Castable Opposite into (w u ee o) =>
--  Castable Straight into (U_II_I u o ee) =>
--  Castable Straight into (w u e o) =>
--  t (w u e o) -> into e ee -> t o
-- yokl_rwr_yoi x f = yokl @into @_ @(w u ee) @t x
--  (rwr_foi @into @w @o @u @e @ee f)

-- rwr_yui :: forall into w o u e ee .
--  Covariant Endo Semi Functor into (U_II_I u o) =>
--  Mapping Constant Straight into into (U_II_I u o) (U_II_I u o) =>
--  Castable Straight into (U_II_I u o ee) =>
--  Castable Opposite into (U_II_I u o e) =>
--  Castable Opposite into (w u ee o) =>
--  Castable Straight into (w u e o) =>
--  Castable Opposite (->) (into () ee) =>
--  (Supertype (w u e o) ~ u e o) =>
--  (Supertype (w u ee o) ~ u ee o) =>
--  Supertype (into () ee) -> into (w u e o) (w u ee o)
-- rwr_yui = rwr `compose` i_ `compose` fu

-- TODO: find a way to generalize
-- yokl_rwr_yui :: forall w t o u e ee .
--  Covariant Yoneda (->) (->) t =>
--  Covariant Endo Semi Functor (->) t =>
--  Covariant Endo Semi Functor (->) (w u ee) =>
--  Covariant Endo Semi Functor (->) (U_II_I u o) =>
--  Mapping Constant Straight (->) (->) (U_II_I u o) (U_II_I u o) =>
--  Component Natural (->) (->) (T_TT_I t (w u ee)) t =>
--  (Supertype (w u e o) ~ u e o) =>
--  (Supertype (w u ee o) ~ u ee o) =>
--  Castable Opposite (->) ((->) () ee) =>
--  Castable Opposite (->) (U_II_I u o e) =>
--  Castable Opposite (->) (w u ee o) =>
--  Castable Straight (->) (U_II_I u o ee) =>
--  Castable Straight (->) (w u e o) =>
--  t (w u e o) -> Supertype (() -> ee) -> t o
-- yokl_rwr_yui x f = yokl @(->) @_ @(w u ee) @t x
--  (rwr_yui @(->) @w @o @u @e @ee f)

-- TODO: generalize
yokl_yi'_yokl :: forall t tt ttt a aa o .
 Covariant Yoneda (->) (->) t =>
 Covariant Endo Semi Functor (->) t =>
 Covariant Endo Semi Functor (->) tt =>
 Covariant Endo Semi Functor (->) ttt =>
 Component Natural (->) (->) (T_TT_I t tt) t =>
 Component Natural (->) (->) (T_TT_I t ttt) t =>
 Castable Straight (->) a =>
 (Supertype a ~ tt aa) =>
 t a -> (aa -> ttt o) -> t o
yokl_yi'_yokl x = yokl @(->) @(->) @ttt @t
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
fc = unwrap @(->) @(That into (t a) _)
 `compose` (fo @(->) @(->) `compose` fo @(->) @(->))
 (rj @(->) @(->) (wr @_ @(That _ _ _)) `compose` wr @_ @(That _ _ _))
 `compose` lj @(->) @(->) @(That LM (t a)) @(That into _)
 (monoidal_ @Straight @into @(->) @t @LM @LM identity (wrap identity)
 `compose` unwrap @(->) @(That LM (t a) (t (into a o))))

cc :: forall t e ee .
 Adjoint Functor (->) (->) (That LM (t e `LM` t ee)) (That (->) (t e `LM` t ee)) =>
 Monoidal Straight Functor (->) LM LM t =>
 t e -> t ee -> t (e `LM` ee)
cc e ee = monoidal_
 @Straight @(->) @(->) @t @LM @LM identity
 (wrap identity)
 (e `lm` ee)
