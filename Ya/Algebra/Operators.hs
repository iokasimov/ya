{-# LANGUAGE AllowAmbiguousTypes #-}
module Ya.Algebra.Operators where

import Ya.Algebra.Abstract
import Ya.Algebra.Definition
import Ya.Algebra.Instances ()

infixl 9 `_'`, `__'`, `___'`

infixl 9 `ho`, `ho'ho`, `ho'ha`, `ho_`, `_ho`, `___ho`, `ho'yo`, `ho_'yo`, `ho'yioi`, `ho'yu`, `ho'_yi'ho`, `ho'yokl`, `ho'yukl`, `ho'yoklKL`
infixl 8 `hoo`, `hoo_`, `hoo'ha`, `hoo'yo`, `hoo'yokl`, `hoo'yukl`, `hoo'yoklKL`
infixl 7 `hooo`, `hooo_`, `hooo'yo`, `hooo'yokl`, `hooo'yukl`
infixl 6 `hoooo`, `hoooo_`, `hoooo'yo`, `hoooo'yokl`, `hoooo'yukl`
infixl 5 `hooooo`, `hooooo_`, `hooooo'yo`, `hooooo'yokl`, `hooooo'yukl`
infixl 4 `hoooooo`, `hoooooo_`, `hoooooo'yo`, `hoooooo'yokl`, `hoooooo'yukl`
infixl 3 `hooooooo`, `hooooooo'yokl`, `hooooooo'yukl`
infixl 2 `hoooooooo`, `hoooooooo'yokl`, `hoooooooo'yukl`
infixl 1 `hooooooooo`, `hooooooooo'yokl`, `hooooooooo'yukl`

infixl 9 `ha`, `ha'ha`, `ha'ho`, `ha_`, `ha_'ha`, `ha'yo`, `ha'yioi`, `ha'yokl`, `ha'yukl`
infixl 8 `haa`, `haa_`
infixl 7 `haaa`, `haaa_`
infixl 6 `haaaa`, `haaaa_`
infixl 5 `haaaaa`, `haaaaa_`
infixl 4 `haaaaaa`, `haaaaaa_`
infixl 3 `haaaaaaa`, `haaaaaaa_`
infixl 2 `haaaaaaaa`, `haaaaaaaa_`
infixl 1 `haaaaaaaaa`, `haaaaaaaaa_`

infixl 9 `hu`, `hu_`, `_hu`
infixl 8 `huu`
infixl 7 `huuu`
infixl 6 `huuuu`
infixl 5 `huuuuu`
infixl 4 `huuuuuu`
infixl 3 `huuuuuuu`
infixl 2 `huuuuuuuu`
infixl 1 `huuuuuuuuu`

infixl 9 `v`, `hv`, `hd`, `hj`, `hj'hj`
infixl 8 `_yi`, `__yi`, `vv`, `yi`, `yo`, `ya`, `yu`, `fo`, `fa`, `fu`, `lj`, `rj`, `ro`, `ra`, `yp`, `ds`, `fr`, `cn`, `cnz`, `cn'yp`, `cnz'yp`, `lm`, `rf`, `cc`, `fc`, `jt`, `yp'yo`, `yp'yp`, `yo'yo`, `fo'fo`, `fr'yp`, `lm'yp`, `lm'ds`, `fo'fo'fo`, `yp'yp'yo`, `yp'yokl`, `yp'yoklKL`, `yp'yp'jt`, `yp'yp'jt'yokl`, `lm'yp'yp`, `rfz`, `yi'_yi`
infixl 7 `_yii`, `__yii`, `vvv`, `yai`, `yai'yai`, `fio`, `foi`, `yoi`, `yoo`, `yii`, `yio`, `yio'yo`, `fai`, `fai_`, `yui`, `yiu`, `yi'ho`, `ilj`, `rij`, `fio'fo`, `w'rw`, `rw'w`
infixl 6 `_yiii`, `__yiii`, `vvvv`, `yi'yi`, `yiii`, `yioi`, `yi'yo`, `yi'yu`, `yi'lm`, `yi'lm'ds`, `yi'rf`, `yi'rfz`, `_yi'rfz`, `yi'cnz'yp`, `fokl`, `fukl`, `yokl`, `yokl'ha`, `yokl'u`, `yukl`, `yolk`, `yokl'yoklKL`, `yokl'_yi'yokl`, `yi'cn'yp`, `yi'lm'yp`
infixl 5 `_yiiii`, `vvvvv`, `yiiii`, `yiokl`
infixl 4 `_yiiiii`, `__yiiiii`, `vvvvvv`, `yiiiii`, `yi'yi'yo`, `yi'yi'yi`, `yi'yi'yu`, `yi'yi'lm`, `yi'yi'lm'ds`, `yi'yi'rf`, `yi'yi'rfz`, `yi'yi'cnz'yp`, `yi'yokl`, `yi'yokl'ha`, `yoklKL`, `yoklKL'yokl`, `yoklKL'yoklKL`, `yi'yukl`, `yi'yokl'yoklKL`, `yi'yi'_yi`, `yi'yi'lm'yp`
infixl 3 `vvvvvvv`, `yiiiiii`
infixl 2 `vvvvvvvv`, `yiiiiiii`, `yi'yi'yi'yo`, `yi'yi'yi'yi`, `yi'yi'yi'yu`, `yi'yi'yi'lm`, `yi'yi'yi'rf`, `yi'yi'yi'rfz`, `yi'yi'yi'_yi`, `yi'_yi'_yi'_yi`, `yi'yi'yi'lm'yp`, `yi'yi'yi'cnz'yp`, `yi'yi'yokl'ha`, `yi'yi'yukl`, `yi'yoklKL`, `yi'yi'yokl'yoklKL`
infixl 1 `vvvvvvvvv`, `yiiiiiiii`
infixl 0 `yi'yi'yi'yi'yo`, `yi'yi'yi'yi'yi`, `yi'yi'yi'yi'lm`, `yi'yi'yi'yi'lm'yp`, `yi'yi'yi'yokl'ha`, `yi'yi'yi'yukl`, `yi'yi'yi'yokl'yoklKL`, `yi'yi'yoklKL`

_' :: forall into e .
 Castable Straight into e =>
 into e (Supertype e)
_' = unwrap

__' :: forall into e .
 Precategory into =>
 Castable Straight into e =>
 Castable Straight into (Supertype e) =>
 into e (Supertype (Supertype e))
__' = unwrap `compose` unwrap

___' :: forall into e .
 Precategory into =>
 Castable Straight into e =>
 Castable Straight into (Supertype e) =>
 Castable Straight into (Supertype (Supertype e)) =>
 into e (Supertype (Supertype (Supertype e)))
___' = unwrap `compose` unwrap `compose` unwrap

yi, yii, yiii, yiiii, yiiiii, yiiiiii, yiiiiiii, yiiiiiiii
 , yi'yi, yi'yi'yi, yi'yi'yi'yi, yi'yi'yi'yi'yi
 :: Category into => into e e
yi = identity

yii = yi
yiii = yi
yiiii = yi
yiiiii = yi
yiiiiii = yi
yiiiiiii = yi
yiiiiiiii = yi

yi'yi = yi
yi'yi'yi = yi
yi'yi'yi'yi = yi
yi'yi'yi'yi'yi = yi

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

yo, yoo, yi'yo, yi'yi'yo, yi'yi'yi'yo, yi'yi'yi'yi'yo :: forall from into t a o .
 Precategory into =>
 Covariant Yoneda from into t =>
 Castable Opposite into (U_I_II from a o) =>
 t a -> into (from a o) (t o)
yo x = yoneda @Straight x

yoo = yo
yi'yo = yo
yi'yi'yo = yo
yi'yi'yi'yo = yo
yi'yi'yi'yi'yo = yo

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

yu, yi'yu, yi'yi'yu, yi'yi'yi'yu  :: forall into t a o .
 Covariant Yoneda into into t =>
 Covariant Endo Semi Functor (->) t =>
 Castable Opposite into (into () o) =>
 Castable Opposite into (U_I_II into () o) =>
 t a -> into (Supertype (into () o)) (t o)
yu x = yoneda @U_I_II (fu @(->) () x) `compose` wr @into @(into () o)

yi'yu = yu
yi'yi'yu = yu
yi'yi'yi'yu = yu

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

yo'yo :: forall from into t tt a o .
 Precategory into =>
 Covariant Functor from from tt =>
 Covariant Yoneda from into t =>
 Contravariant Endo Semi Functor (->) (U_II_I into (t (tt o))) =>
 Castable Opposite into (U_I_II from (tt a) (tt o)) =>
 t (tt a) -> into (from a o) (t (tt o))
yo'yo x = fai fo (yo @from @into x)

yio'yo :: forall from into t tt e a o .
 Precategory into =>
 Contravariant Endo Semi Functor (->) (This into (t e (tt o))) =>
 Covariant Yoneda from into (That t e) =>
 Covariant Functor from from tt =>
 Castable Opposite into (Straight from (tt a) (tt o)) =>
 Castable Straight into (That t e (tt o)) =>
 t e (tt a) -> into (from a o) (t e (tt o))
yio'yo x = fai fo (yio @from @into x)

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

yai'yai :: forall from into t tt e ee a o .
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
yai'yai x = fai fai (yai @from @into x)

yokl, yi'yokl :: forall from into tt t a o .
 Component Natural (->) into (T_TT_I t tt) t =>
 Covariant Yoneda from into t =>
 Castable Opposite into (Straight from a (tt o)) =>
 Castable Opposite into (T_TT_I t tt o) =>
 t a -> into (from a (tt o)) (t o)
yokl x = component @Straight @(->) @into @(T_TT_I t tt)
 `compose` wr @into @(T_TT_I t tt _)
 `compose` yoneda @Straight @from x

yi'yokl = yokl

yukl, yi'yukl, yi'yi'yukl, yi'yi'yi'yukl
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
yi'yukl x = component @Straight @(->) @into @(T_TT_I t tt)
 `compose` wr @into @(T_TT_I t tt _)
 `compose` yoneda @Straight (fu @(->) () x)
 `compose` wr @into @(into () (tt o))
yi'yi'yukl x = component @Straight @(->) @into @(T_TT_I t tt)
 `compose` wr @into @(T_TT_I t tt _)
 `compose` yoneda @Straight (fu @(->) () x)
 `compose` wr @into @(into () (tt o))
yi'yi'yi'yukl x = component @Straight @(->) @into @(T_TT_I t tt)
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

yoklKL, yi'yoklKL, yi'yi'yoklKL :: forall from into tt t a o .
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

yi'yoklKL = yoklKL
yi'yi'yoklKL = yoklKL

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

yokl'yoklKL, yi'yokl'yoklKL, yi'yi'yokl'yoklKL, yi'yi'yi'yokl'yoklKL
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
yokl'yoklKL x = fai foklKL (yokl @from @into x)

yi'yokl'yoklKL = yokl'yoklKL
yi'yi'yokl'yoklKL = yokl'yoklKL
yi'yi'yi'yokl'yoklKL = yokl'yoklKL

yoklKL'yokl :: forall from into t tt ttt a o .
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
yoklKL'yokl x = fai fokl (yoklKL @from @into x)

yoklKL'yoklKL :: forall from into t tt ttt a o .
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
yoklKL'yoklKL x = fai foklKL (yoklKL @from @into x)

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

fai_ :: forall from into t a o i .
 Contravariant Semi Functor from into (U_II_I t i) =>
 Contravariant Semi Functor into into (U_II_I t i) =>
 Wrapper into (U_II_I t i a) =>
 Wrapper into (U_II_I t i (Supertype a)) =>
 Wrapper into (U_II_I t i o) =>
 Wrapper into a =>
 from (Supertype a) o -> into (t o i) (t a i)
fai_ from = fai @into unwrap `compose` unwrap
 `compose` fa @_ @_ @(U_II_I _ _) from `compose` wr

fio'fo :: forall from into t tt e a o .
 Covariant Semi Functor into into (U_I_II t e) =>
 Covariant Semi Functor from into tt =>
 Wrapper into (U_I_II t e (tt a)) =>
 Wrapper into (U_I_II t e (tt o)) =>
 from a o -> into (t e (tt a)) (t e (tt o))
fio'fo from = fio @into @into (fo @from @into from)

fiu :: forall from into t a o e .
 Covariant Semi Functor into into (U_I_II t e) =>
 Mapping Constant Straight into into (U_I_II t e) (U_I_II t e) =>
 Castable Opposite (->) (into () o) =>
 Castable Straight into (U_I_II t e o) =>
 Castable Opposite into (U_I_II t e a) =>
 Supertype (into () o) -> into (t e a) (t e o)
fiu from = unwrap `compose` fu @_ @(U_I_II _ _) from `compose` wr

ho, hoo, hooo, hoooo, hooooo, hoooooo, hooooooo, hoooooooo, hooooooooo, yi'ho :: forall from into u i a o .
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
hooooooo = ho
hoooooooo = ho
hooooooooo = ho
yi'ho = ho

ho_, hoo_, hooo_, hoooo_, hooooo_, hoooooo_, hooooooo_, hoooooooo_, hooooooooo_
 :: forall from into u i a o .
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
ho_ x = yio @from @into @u x `compose` fai @from _'

hoo_ = ho_
hooo_ = ho_
hoooo_ = ho_
hooooo_ = ho_
hoooooo_ = ho_
hooooooo_ = ho_
hoooooooo_ = ho_
hooooooooo_ = ho_

_ho, _hoo, _hooo, _hoooo, _hooooo, _hoooooo, _hooooooo, _hoooooooo, _hooooooooo
 :: forall from into u i a o .
 Precategory from =>
 Precategory into =>
 Covariant Yoneda from into (U_I_II u i) =>
 Contravariant Semi Functor from (->) (U_II_I u a) =>
 Covariant Semi Functor from into (U_I_II from o) =>
 Castable Straight from i =>
 Castable Straight into (U_I_II u i o) =>
 Castable Opposite into (U_I_II from a o) =>
 Wrapper into (U_II_I from o a) =>
 Wrapper into (U_II_I from o (Supertype a)) =>
 u (Supertype i) a -> into (from a o) (u i o)
_ho = yio @from @into @u `compose` fai @from _'

_hoo = _ho
_hooo = _ho
_hoooo = _ho
_hooooo = _ho
_hoooooo = _ho
_hooooooo = _ho
_hoooooooo = _ho
_hooooooooo = _ho

ha, haa, haaa, haaaa, haaaaa, haaaaaa, haaaaaaa, haaaaaaaa, haaaaaaaaa :: forall from u e a o .
 Contravariant Yoneda from (->) (U_II_I u e) =>
 u a e -> from o a -> u o e
ha x = _' `compose` ya @from @(->) @(U_II_I u _) (U_II_I x)

haa = ha
haaa = ha
haaaa = ha
haaaaa = ha
haaaaaa = ha
haaaaaaa = ha
haaaaaaaa = ha
haaaaaaaaa = ha

ha_, haa_, haaa_, haaaa_, haaaaa_, haaaaaa_, haaaaaaa_, haaaaaaaa_, haaaaaaaaa_ :: forall from u e a o .
 Contravariant Yoneda from (->) (U_II_I u e) =>
 Castable Straight from o =>
 u a e -> from (Supertype o) a -> u o e
ha_ x = _' `compose` ya @from @(->) @(U_II_I u _) (U_II_I x) `compose` fai @from _'

haa_ = ha_
haaa_ = ha_
haaaa_ = ha_
haaaaa_ = ha_
haaaaaa_ = ha_
haaaaaaa_ = ha_
haaaaaaaa_ = ha_
haaaaaaaaa_ = ha_

ha'ha :: forall from u uu a o e ee .
 Contravariant Yoneda u (->) (Opposite u e) =>
 Contravariant Semi Functor from u (Opposite uu ee) =>
 Wrapper u (Opposite uu ee a) =>
 Wrapper u (Opposite uu ee o) =>
 u (uu a ee) e -> from a o -> u (uu o ee) e
ha'ha x = fai @(->) @(->) fai (ha @u x)

hv :: forall from u a o .
 Contravariant Yoneda from (->) (U_II_I u o) =>
 Castable Straight (->) (u () o) =>
 u a o -> from () a -> Supertype (u () o)
hv x from = _' (x `ha` from)

ha_'ha :: forall from u uu a o e ee .
 Contravariant Yoneda u (->) (Opposite u e) =>
 Contravariant Semi Functor from u (Opposite uu ee) =>
 Contravariant Semi Functor u u (Opposite uu ee) =>
 Wrapper u (Opposite uu ee (Supertype a)) =>
 Wrapper u (Opposite uu ee o) =>
 Wrapper u (Opposite uu ee a) =>
 Wrapper u a =>
 u (uu a ee) e -> from (Supertype a) o -> u (uu o ee) e
ha_'ha x = fai @(->) @(->) fai_ (ha @u x)

ho'ha, hoo'ha  :: forall from u uu o e ee a .
 Covariant Yoneda u (->) (Straight u e) =>
 Contravariant Yoneda u (->) (Opposite u e) =>
 Contravariant Semi Functor from u (Opposite uu ee) =>
 Contravariant Endo Semi Functor (->) (Opposite (->) (u e (uu a ee))) =>
 Wrapper u (U_II_I uu ee a) =>
 Wrapper u (U_II_I uu ee o) =>
 Wrapper from (U_I_II u e (uu a ee)) =>
 Wrapper from (U_I_II u (uu o ee) (uu a ee)) =>
 u e (uu o ee) -> from a o -> u e (uu a ee)
ho'ha x = fai @(->) @(->) fai (ho @u x)

hoo'ha = ho'ha

ho'ho :: forall from u uu o e ee a .
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
ho'ho x = fai fio (ho @u x)

ha'ho :: forall from u uu o e ee a .
 Covariant Yoneda u (->) (Straight u e) =>
 Contravariant Yoneda u (->) (Opposite u e) =>
 Covariant Semi Functor from u (Opposite uu ee) =>
 Contravariant Endo Semi Functor (->) (Opposite (->) (u e (uu a ee))) =>
 Wrapper u (U_II_I uu ee a) =>
 Wrapper u (U_II_I uu ee o) =>
 u (uu o ee) e -> from a o -> u (uu a ee) e
ha'ho x = fai @(->) @(->) foi (ha @u x)

ho'yo, hoo'yo, hooo'yo, hoooo'yo, hooooo'yo, hoooooo'yo :: forall from u t o e a .
 Covariant Yoneda from (->) (Straight u e) =>
 Contravariant Yoneda from (->) (Opposite u e) =>
 Covariant Endo Semi Functor from t =>
 Mapping Constant Straight from (->) t t =>
 u e (t a) -> from a o -> u e (t o)
ho'yo x = fai (fo @from) (ho @from x)

hoo'yo = ho'yo
hooo'yo = ho'yo
hoooo'yo = ho'yo
hooooo'yo = ho'yo
hoooooo'yo = ho'yo

ho_'yo :: forall from u t o e a .
 Covariant Yoneda from (->) (Straight u e) =>
 Contravariant Yoneda from (->) (Opposite u e) =>
 Contravariant Semi Functor from (->) (Opposite u (t a)) =>
 Covariant Endo Semi Functor from t =>
 -- Mapping Constant Straight from (->) t t =>
 Castable Straight from e =>
 u (Supertype e) (t a) -> from a o -> u e (t o)
ho_'yo x = fai (fo @from) (ho @from (fai @from _yi x))

ho'yioi :: forall from u t o e ee eee a .
 Covariant Yoneda from (->) (Straight u e) =>
 Contravariant Yoneda from (->) (Opposite u e) =>
 Covariant Endo Semi Functor from (W_III_I_II t eee ee) =>
 Wrapper from (W_III_I_II t eee ee a) =>
 Wrapper from (W_III_I_II t eee ee o) =>
 u e (t ee a eee) -> from a o -> u e (t ee o eee)
ho'yioi x = fai (fioi @from) (ho @from x)

ha'yo :: forall from u t o e a .
 Covariant Yoneda from (->) (Straight u e) =>
 Contravariant Yoneda from (->) (Opposite u e) =>
 Covariant Endo Semi Functor from t =>
 Mapping Constant Straight from (->) t t =>
 u (t a) e -> from o a -> u (t o) e
ha'yo x = fai (fo @from) (ha @from x)

ha'yioi :: forall from u t o e ee eee a .
 Covariant Yoneda from (->) (Straight u e) =>
 Contravariant Yoneda from (->) (Opposite u e) =>
 Covariant Endo Semi Functor from (W_III_I_II t eee ee) =>
 Wrapper from (W_III_I_II t eee ee a) =>
 Wrapper from (W_III_I_II t eee ee o) =>
 u (t ee a eee) e -> from o a -> u (t ee o eee) e
ha'yioi x = fai (fioi @from) (ha @from x)

ho'yu :: forall u t o e a .
 Covariant Yoneda (->) (->) (Straight u e) =>
 Contravariant Yoneda (->) (->) (Opposite u e) =>
 Covariant Endo Semi Functor (->) t =>
 Mapping Constant Straight (->) (->) t t =>
 Castable Opposite (->) (u () o) =>
 u e (t a) -> o -> u e (t o)
ho'yu x = fai @(->) @(->) (fu @(->)) (ho @(->) x)

-- TODO: replace with `ho_`
ho'_yi :: forall from u e a o .
 Covariant Endo Semi Functor from (That from a) =>
 Covariant Yoneda from (->) (U_I_II u e) =>
 Contravariant Semi Functor from (->) (U_II_I (->) (u e (Supertype o))) =>
 Contravariant Yoneda from (->) (U_II_I (->) (u e (Supertype o))) =>
 Castable Straight (->) (U_I_II u e o) =>
 Castable Straight from o =>
 Wrapper from (U_I_II from a o) =>
 Wrapper from (U_I_II from a (Supertype o)) =>
 u e a -> from a o -> u e (Supertype o)
ho'_yi x = fai @from (fio @from _') (ho x)

-- TODO: replace with `ho_'ho`
ho'_yi'ho :: forall from u e a o .
 Covariant Yoneda from (->) (That u e) =>
 Castable Straight from a =>
 u e a -> from (Supertype a) o -> u e o
ho'_yi'ho x xx = x `ho` _' @from `ho` xx

hu, huu, huuu, huuuu, huuuuu, huuuuuu, huuuuuuu, huuuuuuuu, huuuuuuuuu, huuuuuuuuuu :: forall from into a o .
 Precategory into =>
 Covariant Yoneda from into (U_1_I from ()) =>
 Castable Opposite into (U_I_II from a o) =>
 Castable Straight into (U_I_II from () o) =>
 Castable Straight into (U_1_I from () o) =>
 Castable Opposite (->) (from () a) =>
 Castable Straight into (from () o) =>
 Supertype (from () a) -> into (from a o) (Supertype (from () o))
hu x = _' `compose` _' `compose` yo @from @into @(U_1_I from ()) (U_1_I @from @() / wrap @(from () _) x)

huu = hu
huuu = hu
huuuu = hu
huuuuu = hu
huuuuuu = hu
huuuuuuu = hu
huuuuuuuu = hu
huuuuuuuuu = hu
huuuuuuuuuu = hu

_hu :: forall from into a a' o .
 Precategory into =>
 ((Supertype (from () a)) ~ Supertype a') =>
 Covariant Yoneda from into (U_1_I from ()) =>
 Castable Opposite into (U_I_II from a o) =>
 Castable Straight into (U_I_II from () o) =>
 Castable Straight into (U_1_I from () o) =>
 Castable Opposite (->) (from () a) =>
 Castable Straight into (from () o) =>
 Castable Straight (->) a' =>
 a' -> into (from a o) (Supertype (from () o))
_hu x = _' `compose` _' `compose` yo @from @into @(U_1_I from ())
 (U_1_I @from @() (wrap @(from () _) (unwrap x)))

hu_ :: forall from into a o .
 Precategory into =>
 Precategory from =>
 Covariant Yoneda from into (U_1_I from ()) =>
 Contravariant Endo Semi Functor from (U_II_I from o) =>
 Castable Opposite into (U_I_II from a o) =>
 Castable Opposite (->) (from () a) =>
 Castable Straight into (from () o) =>
 Castable Straight from a =>
 Wrapper from (U_II_I from o a) =>
 Wrapper from (U_II_I from o (Supertype a)) =>
 Castable Straight into (U_I_II from () o) =>
 Castable Straight into (U_1_I from () o) =>
 Contravariant Yoneda from (->) (U_II_I into (Supertype (from () o))) =>
 Supertype (from () a) -> into (from (Supertype a) o) (Supertype (from () o))
hu_ x = hu @from @into @a x `yai'yai` _' @from @a

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
ro = _' `compose` map @Straight @Straight @into @into @t @(Straight hom (Representation t)) identity

ra :: forall into hom t i .
 Category into =>
 Contravariant (Representable hom) into into t =>
 Castable Straight into (Opposite hom (Representation t) i) =>
 into (t i) (hom i (Representation t))
ra = _' `compose` map @Opposite @Straight @into @into @t @(Opposite hom (Representation t)) identity

lj :: forall from into t tt a o .
 Adjoint Functor from into t tt =>
 Castable Straight into ((T_TT_I tt t) a) =>
 Castable Opposite into (Identity a) =>
 from (t a) o -> into a (tt o)
lj from = fo from
 `compose` _' @into
 `compose` component @Straight @from @into @Identity @(tt `T_TT_I` t)
 `compose` wr @into

ilj :: forall from into t tt e ee a o .
 Adjoint Functor from into (U_I_II t e) (U_I_II tt ee) =>
 Castable Straight into ((T_TT_I (U_I_II tt ee) (U_I_II t e)) a) =>
 Castable Straight into (U_I_II tt ee o) =>
 Castable Opposite into (Identity a) =>
 Castable Straight from (U_I_II t e a) =>
 from (t e a) o -> into a (tt ee o)
ilj from = _' @into @(U_I_II tt _ _)
 `compose` fo (from `compose` _' @from @(U_I_II t _ _))
 `compose` _' @into @(T_TT_I _ _ _)
 `compose` component @Straight @from @into @Identity @(U_I_II tt ee `T_TT_I` U_I_II t e)
 `compose` wr @into

hd :: forall from into t tt e a o .
 Adjoint Functor from into (U_II_I t e) (U_I_II tt e) =>
 Castable Straight into ((U_I_II tt e `T_TT_I` U_II_I t e) a) =>
 Castable Straight into (U_I_II tt e o) =>
 Castable Opposite into (Identity a) =>
 Castable Straight from (U_II_I t e a) =>
 from (t a e) o -> into a (tt e o)
hd from = _' @into @(U_I_II tt _ _)
 `compose` fo (from `compose` _' @from @(U_II_I t _ _))
 `compose` _' @into @(T_TT_I _ _ _)
 `compose` component @Straight @from @into @Identity @(U_I_II tt e `T_TT_I` U_II_I t e)
 `compose` wr @into

hj :: forall from into t tt e a o .
 Adjoint Functor from into (U_II_I t e) (U_I_II tt e) =>
 Castable Opposite from ((T_TT_I (U_II_I t e) (U_I_II tt e)) o) =>
 Castable Straight from (Identity o) =>
 Castable Opposite from (U_II_I t e a) =>
 Castable Opposite into (U_I_II tt e o) =>
 into a (tt e o) -> from (t a e) o
hj from = _' @from
 `compose` component @Straight @into @from @(U_II_I t e `T_TT_I` U_I_II tt e) @Identity
 `compose` wr @from @((U_II_I t e `T_TT_I` U_I_II tt e) _)
 `compose` fo (wr @into @(U_I_II tt e _) `compose` from)
 `compose` wr @from @(U_II_I t e _)

hj'hj :: forall from into t tt ttt tttt e ee a o .
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
hj'hj = hj @from @from `compose` hj @from @into

-- TODO: define `j'_j'_j'`, `j'_j'_j'_j'`, `j'_j'_j'_j'_j',

rj :: forall from into t tt a o .
 Adjoint Functor from into t tt =>
 Castable Opposite from ((T_TT_I t tt) o) =>
 Castable Straight from (Identity o) =>
 into a (tt o) -> from (t a) o
rj from = _' @from @(Identity _)
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
rij from = _' @from
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

cnz :: forall into e a aa o oo .
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
cnz from_left from_right = fio from_right `compose` foi from_left `compose` _' @into

-- TODO: try to generalize
cn'yp, yi'cn'yp :: forall t a aa o oo .
 Mapping Straight Straight (->) (->) (Day Straight (->) (Product (->)) (Product (->)) t t o oo) t =>
 Arrow a (t o) -> Arrow aa (t oo) -> Arrow (Product (->) a aa) (t (Product Arrow o oo))
cn'yp from_left from_right = yp `compose` cn from_left from_right

yi'cn'yp = cn'yp

-- TODO: try to generalize
cnz'yp, yi'cnz'yp, yi'yi'cnz'yp, yi'yi'yi'cnz'yp :: forall e t a aa o oo .
 Mapping Straight Straight (->) (->) (Day Straight (->) (Product (->)) (Product (->)) t t o oo) t =>
 Castable Straight (->) e =>
 (Supertype e ~ Product (->) a aa) =>
 Arrow a (t o) -> Arrow aa (t oo) -> Arrow e (t (Product Arrow o oo))
cnz'yp from_left from_right = yp `compose` cn from_left from_right `compose` _'

yi'cnz'yp = cnz'yp
yi'yi'cnz'yp = cnz'yp
yi'yi'yi'cnz'yp = cnz'yp

-- TODO: try to generalize
lm, yi'lm, yi'yi'lm, yi'yi'yi'lm, yi'yi'yi'yi'lm :: forall o oo .
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
lm from_left from_right = _' /
 _i (map @Straight @Straight (wrapped (right @Straight (wr @_ @((->) () oo) from_right)))) `compose`
 i_ (map @Straight @Straight (wrapped (left @Straight (wr @_ @((->) () o) from_left)))) `compose`
 wrapped (map @Straight @Straight @(->) @(->) @Identity @(Both (Product (->))) identity) `compose`
 wrapped (map @Straight @Straight @(->) @(->) @Identity @(Both (Product (->))) identity)

yi'lm = lm
yi'yi'lm = lm
yi'yi'yi'lm = lm
yi'yi'yi'yi'lm = lm

rf, yi'rf, yi'yi'rf, yi'yi'yi'rf :: forall from i o oo .
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

yi'rf = rf
yi'yi'rf = rf
yi'yi'yi'rf = rf

rfz, yi'rfz, yi'yi'rfz, yi'yi'yi'rfz :: forall from e i o oo .
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
rfz from_left from_right = rf from_left from_right `compose` _'

yi'rfz = rfz
yi'yi'rfz = rfz
yi'yi'yi'rfz = rfz

_yi'rfz :: forall from e ee i o oo .
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
_yi'rfz from_left from_right = rfz from_left from_right `compose` _yi

-- TODO: to test
rwr'rf :: forall from into r o a aa .
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
rwr'rf from_left from_right = rwr /
 wrapped (map @Opposite @Opposite @from @into @Identity @(Both (Sum into)) identity) `compose`
 wrapped (map @Opposite @Opposite @from @into @Identity @(Both (Sum into)) identity) `compose`
 i_ (map @Straight @Straight (wrapped (left @Opposite from_left))) `compose`
 _i (map @Straight @Straight (wrapped (right @Opposite from_right)))

yp :: forall u e ee t .
 Mapping Straight Straight (->) (->) (Day Straight (->) u LM t t e ee) t =>
 u (t e) (t ee) -> t (e `LM` ee)
yp = day @Straight @(->) @t @u @LM identity identity

ds :: forall u e ee t .
 Mapping Straight Straight (->) (->) (Day Straight (->) u ML t t e ee) t =>
 u (t e) (t ee) -> t (e `ML` ee)
ds = day @Straight @(->) @t @u @ML identity identity

dw :: forall u e ee t .
 Mapping Straight Straight (->) (->)
 (Day Straight (->) u MLM t t e ee) t =>
 u (t e) (t ee) -> t (ML e ee `ML` LM e ee)
dw = day @Straight @(->) @t @u @MLM identity _'

yp'yp :: forall u e ee t tt .
 Mapping Straight Straight (->) (->)
 (Day Straight (->) u LM t t (tt e) (tt ee)) t =>
 Mapping Straight Straight (->) (->)
 (Day Straight (->) LM LM tt tt e ee) tt =>
 u (t (tt e)) (t (tt ee)) -> t (tt (e `LM` ee))
yp'yp = day @Straight @(->) @t @u @LM identity
 (day @Straight @(->) @tt @LM @LM identity identity)

_yi, _yii, _yiii, _yiiii, _yiiiii
 , yi'_yi, yi'yi'_yi, yi'yi'yi'_yi ::
 Castable Straight into i =>
 into i (Supertype i)
_yi = _'

_yii = _yi
_yiii = _yi
_yiiii = _yi
_yiiiii = _yi
yi'_yi = _yi
yi'yi'_yi = _yi
yi'yi'yi'_yi = _yi

w'rw :: forall into a o .
 Precategory into =>
 Castable Opposite into o =>
 Castable Straight into a =>
 into (Supertype a) (Supertype o) -> into a o
w'rw into = wr @into `compose` into `compose` _' @into

rw'w :: forall into a o .
 Precategory into =>
 Castable Opposite into a =>
 Castable Straight into o =>
 into a o -> into (Supertype a) (Supertype o)
rw'w into = _' @into `compose` into `compose` wr @into

__yi, __yii, __yiii, __yiiii, __yiiiii :: forall into a .
 Precategory into =>
 Castable Straight into a =>
 Castable Straight into (Supertype a) =>
 into a (Supertype (Supertype a))
__yi = _' @into `compose` _' @into

__yii = __yi
__yiii = __yi
__yiiii = __yi
__yiiiii = __yi

_yi'_yi'_yi, yi'_yi'_yi'_yi :: forall into a .
 Precategory into =>
 Castable Straight into a =>
 Castable Straight into (Supertype a) =>
 Castable Straight into (Supertype (Supertype a)) =>
 into a (Supertype (Supertype (Supertype a)))
_yi'_yi'_yi = _' @into `compose` _' @into `compose` _' @into

yi'_yi'_yi'_yi = _yi'_yi'_yi

-- TODO: try to generalize
___ho :: forall a e o oo .
 Castable Straight (->) a =>
 Castable Straight (->) (Supertype a) =>
 Castable Straight (->) (Supertype (Supertype a)) =>
 ((e `ARR` o) ~ Supertype (Supertype (Supertype a))) =>
 a `ARR` e `ARR` (o `ARR` oo) `ARR` oo
___ho x e f = f (_' (_' (_' x)) e)

-- TODO: define `rw'o`
-- TODO: define `rw'rw'o`
-- TODO: define `rw'ha`
-- TODO: define `rw'rw'ha`
-- TODO: define `rw'rw'rw'ha`

ho'yokl, hoo'yokl, hooo'yokl, hoooo'yokl, hooooo'yokl, hoooooo'yokl, hooooooo'yokl, hoooooooo'yokl, hooooooooo'yokl :: forall from u t tt a o e .
 Covariant Endo Semi Functor from tt =>
 Covariant Endo Semi Functor from t =>
 Mapping Straight Straight from from (T_TT_I t tt) t =>
 Covariant Yoneda from (->) (Straight u e) =>
 (forall ee . Wrapper from (T_TT_I t tt ee)) =>
 u e (t a) -> from a (tt o) -> u e (t o)
ho'yokl x = fai fokl (ho @from x)

hoo'yokl = ho'yokl
hooo'yokl = ho'yokl
hoooo'yokl = ho'yokl
hooooo'yokl = ho'yokl
hoooooo'yokl = ho'yokl
hooooooo'yokl = ho'yokl
hoooooooo'yokl = ho'yokl
hooooooooo'yokl = ho'yokl

ho'yukl, hoo'yukl, hooo'yukl, hoooo'yukl, hooooo'yukl, hoooooo'yukl, hooooooo'yukl, hoooooooo'yukl, hooooooooo'yukl :: forall from t tt a o e .
 Covariant Endo Semi Functor from tt =>
 Covariant Endo Semi Functor from t =>
 Mapping Constant Straight from from t t =>
 Mapping Straight Straight from from (T_TT_I t tt) t =>
 Covariant Yoneda from (->) (Straight from e) =>
 Castable Opposite from (T_TT_I t t o) =>
 Castable Opposite (->) (from () (tt o)) =>
 (forall ee . Wrapper from (T_TT_I t tt ee)) =>
 from e (t a) -> Supertype (from () (tt o)) -> from e (t o)
ho'yukl x = fai (fukl @from @t @tt) (ho @from x)

hoo'yukl x = fai (fukl @from @t @tt) (ho @from x)
hooo'yukl x = fai (fukl @from @t @tt) (ho @from x)
hoooo'yukl x = fai (fukl @from @t @tt) (ho @from x)
hooooo'yukl x = fai (fukl @from @t @tt) (ho @from x)
hoooooo'yukl x = fai (fukl @from @t @tt) (ho @from x)
hooooooo'yukl x = fai (fukl @from @t @tt) (ho @from x)
hoooooooo'yukl x = fai (fukl @from @t @tt) (ho @from x)
hooooooooo'yukl x = fai (fukl @from @t @tt) (ho @from x)

ha'yokl :: forall from u t tt a o e .
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
ha'yokl x = fai fokl (ha @from x)

-- TODO: try to gereralize
yokl'ha, yi'yokl'ha, yi'yi'yokl'ha, yi'yi'yi'yokl'ha :: forall from t tt a o e .
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
yokl'ha x f = yokl x `compose` fio f

yi'yokl'ha = yokl'ha
yi'yi'yokl'ha = yokl'ha
yi'yi'yi'yokl'ha = yokl'ha

yokl'u :: forall from t tt a o e .
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
yokl'u x f = yokl @_ @_ @tt x `compose` _i (fu @from f)

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

ho'yoklKL, hoo'yoklKL :: forall from u t tt a o e .
 Unlabelable from tt =>
 Covariant Semi Functor from (->) (Straight u e) =>
 Covariant Endo Semi Functor from tt =>
 Covariant Endo Semi Functor from t =>
 Mapping Straight Straight from from (T_TT_I t tt) (TT_T_I t tt) =>
 Covariant Yoneda from (->) (Straight u e) =>
 (forall ee . Wrapper from (T_TT_I t tt ee)) =>
 (forall ee . Wrapper from (TT_T_I t tt ee)) =>
 u e (t a) -> from a (tt o) -> u e (Unlabeled tt (t o))
ho'yoklKL x = fio @from unlabel `compose` fai foklKL (ho @from x)

hoo'yoklKL = ho'yoklKL

ha'yukl :: forall from t tt a o e .
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
ha'yukl = ha `compose` fukl @from @tt @t

fr'yp :: forall from t i o oo .
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
fr'yp from_left from_right = yp `compose`
 _i (map @Straight @Straight (wrapped (right @Straight from_right))) `compose`
 i_ (map @Straight @Straight (wrapped (left @Straight from_left))) `compose`
 wrapped (map @Straight @Straight @from @(->) @Identity @(Both (LM)) identity) `compose`
 wrapped (map @Straight @Straight @from @(->) @Identity @(Both (LM)) identity)

lm'yp, yi'lm'yp, yi'yi'lm'yp, yi'yi'yi'lm'yp, yi'yi'yi'yi'lm'yp :: forall o oo t .
 Covariant Monoidal Functor (->) LM LM t =>
 t o -> t oo -> t (o `LM` oo)
lm'yp from_left from_right = yp (lm from_left from_right)

yi'lm'yp = lm'yp
yi'yi'lm'yp = lm'yp
yi'yi'yi'lm'yp = lm'yp
yi'yi'yi'yi'lm'yp = lm'yp

lm'ds, yi'lm'ds, yi'yi'lm'ds :: forall o oo t .
 Covariant Monoidal Functor (->) LM ML t =>
 t o -> t oo -> t (o `ML` oo)
lm'ds from_left from_right = ds (lm from_left from_right)

yi'lm'ds = lm'ds
yi'yi'lm'ds = lm'ds

lm'yp'yp :: forall o oo t tt .
 Covariant Monoidal Functor (->) LM LM t =>
 Covariant Monoidal Functor (->) LM LM tt =>
 t (tt o) -> t (tt oo) -> t (tt (o `LM` oo))
lm'yp'yp from_left from_right = yp'yp @LM (lm from_left from_right)

-- TODO: generalize
yp'yo :: forall from e ee r t .
 Covariant Monoidal Functor from LM LM t =>
 t e `LM` t ee -> from (e `LM` ee) r -> t r
yp'yo x f = day @Straight @from @t @LM @LM identity f x

-- TODO: generalize
yp'yokl :: forall e ee from into t tt o .
 Covariant Monoidal Functor (->) LM LM t =>
 Covariant Yoneda from into t =>
 Component Natural (->) into (T_TT_I t tt) t =>
 Castable Opposite into (Straight from (e `LM` ee) (tt o)) =>
 Castable Opposite into (T_TT_I t tt o) =>
 t e `LM` t ee -> into (from (e `LM` ee) (tt o)) (t o)
yp'yokl = yokl @from @into `compose` yp

-- TODO: generalize
yp'yoklKL :: forall e ee from into t tt o .
 Unlabelable into tt =>
 Component Natural from into (T_TT_I t tt) (TT_T_I t tt) =>
 Covariant Monoidal Functor (->) LM LM t =>
 Covariant Yoneda from into t =>
 Castable Opposite into (Straight from (e `LM` ee) (tt o)) =>
 Castable Opposite into (T_TT_I t tt o) =>
 Castable Straight into (TT_T_I t tt o) =>
 t e `LM` t ee -> into (from (e `LM` ee) (tt o)) (Unlabeled tt (t o))
yp'yoklKL = yoklKL @from @into `compose` yp

-- TODO: generalize
yp'yp'yo :: forall from e ee r t tt .
 Covariant Monoidal Functor (->) LM LM t =>
 Covariant Monoidal Functor from LM LM tt =>
 t (tt e) `LM` t (tt ee) -> from (e `LM` ee) r -> t (tt r)
yp'yp'yo x f = day @Straight @(->) @t @LM @LM identity
 (day @Straight @from @tt @LM @LM identity f) x

jt :: forall into f g e .
 Component Natural (->) into (f `T_TT_I` g) (f `JT` g) =>
 Castable Opposite into ((f `T_TT_I` g) e) =>
 into (f (g e)) ((f `JT` g) e)
jt = component @Straight @(->) @into @(f `T_TT_I` g) @(f `JT` g) @e
 `compose` wr @into @((f `T_TT_I` g) e)

-- TODO: generalize
yp'yp'jt :: forall e ee t tt .
 Component Natural (->) (->) (t `T_TT_I` tt) (t `JT` tt) =>
 Covariant Monoidal Functor (->) LM LM t =>
 Covariant Monoidal Functor (->) LM LM tt =>
 t (tt e) `LM` t (tt ee) -> (t `JT` tt) (e `LM` ee)
yp'yp'jt = jt `compose` day @Straight @(->) @t @LM @LM identity
 (day @Straight @(->) @tt @LM @LM identity identity)

-- TODO: generalize
yp'yp'jt'yokl :: forall from into e ee t tt ttt o .
 Covariant Yoneda from into t =>
 Covariant Yoneda from into (t `JT` tt) =>
 Component Natural (->) (->) (t `T_TT_I` tt) (t `JT` tt) =>
 Component Natural (->) into (T_TT_I (t `JT` tt) ttt) (t `JT` tt) =>
 Covariant Monoidal Functor (->) LM LM t =>
 Covariant Monoidal Functor (->) LM LM tt =>
 Castable Opposite into (Straight from (e `LM` ee) (ttt o)) =>
 Castable Opposite into (T_TT_I (JT t tt) ttt o) =>
 t (tt e) `LM` t (tt ee) -> into (from (e `LM` ee) (ttt o)) ((t `JT` tt) o)
yp'yp'jt'yokl = yokl @from @into `compose` yp'yp'jt

-- TODO: generalize
rwr'foi :: forall into w o u e ee .
 Covariant Endo Semi Functor into (U_II_I u o) =>
 Castable Straight into (U_II_I u o ee) =>
 Castable Opposite into (U_II_I u o e) =>
 Castable Opposite into (w u ee o) =>
 Castable Straight into (w u e o) =>
 (Supertype (w u e o) ~ u e o) =>
 (Supertype (w u ee o) ~ u ee o) =>
 into e ee -> into (w u e o) (w u ee o)
rwr'foi = rwr `compose` i_ `compose` fo

-- TODO: generalize
rwr'fio :: forall into w o u e ee .
 Covariant Endo Semi Functor into (U_I_II u o) =>
 Castable Straight into (U_I_II u o ee) =>
 Castable Opposite into (U_I_II u o e) =>
 Castable Opposite into (w u o ee) =>
 Castable Straight into (w u o e) =>
 (Supertype (w u o e) ~ u o e) =>
 (Supertype (w u o ee) ~ u o ee) =>
 into e ee -> into (w u o e) (w u o ee)
rwr'fio = rwr `compose` _i `compose` fo

-- TODO: try to simplify
rwr'yoi :: forall from into w o u e ee .
 Precategory into =>
 Covariant Yoneda from into (U_II_I u o) =>
 Castable Opposite into (w u ee o) =>
 Castable Straight (->) (w u e o) =>
 Castable Straight into (U_II_I u o ee) =>
 Castable Opposite into (U_I_II from e ee) =>
 (Supertype (w u e o) ~ u e o) =>
 (Supertype (w u ee o) ~ u ee o) =>
 w u e o -> into (from e ee) (w u ee o)
rwr'yoi x = wr @into `compose` yoi (unwrap x)

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
yokl'_yi'yokl :: forall t tt ttt a aa o .
 Covariant Yoneda (->) (->) t =>
 Covariant Endo Semi Functor (->) t =>
 Covariant Endo Semi Functor (->) tt =>
 Covariant Endo Semi Functor (->) ttt =>
 Component Natural (->) (->) (T_TT_I t tt) t =>
 Component Natural (->) (->) (T_TT_I t ttt) t =>
 Castable Straight (->) a =>
 (Supertype a ~ tt aa) =>
 t a -> (aa -> ttt o) -> t o
yokl'_yi'yokl x = yokl @(->) @(->) @ttt @t
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
