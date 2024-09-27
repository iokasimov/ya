{-# LANGUAGE AllowAmbiguousTypes #-}
module Ya.Algebra.Operators where

import Ya.Algebra.Abstract
import Ya.Algebra.Definition
import Ya.Algebra.Instances ()

infixl 9 `ho`, `ho'ho`, `ho'ho'hu`, `ho'hu`, `ho'ha`, `ho'ha'he`, `ho'yo`, `ho'yioi`, `ho'yu`, `ho'yok`, `ho'yuk`, `ho'yokl`
 , `ho'he`
 , `ho'he'he`
 , `ho'he'he'he`
infixl 8 `hoo`, `hoo'ha`, `hoo'ha'he`, `hoo'yo`, `hoo'yu`, `hoo'yok`, `hoo'yuk`, `hoo'yokl`
 , `hoo'he`
 , `hoo'he'he`
 , `hoo'he'he'he`
infixl 7 `hooo`, `hooo'ha`, `hooo'ha'he`, `hooo'yo`, `hooo'yu`, `hooo'yok`, `hooo'yuk`, `hooo'yokl`
 , `hooo'he`
 , `hooo'he'he`
 , `hooo'he'he'he`
infixl 6 `hoooo`, `hoooo'ha`, `hoooo'ha'he`, `hoooo'yo`, `hoooo'yu`, `hoooo'yok`, `hoooo'yuk`, `hoooo'yokl`
 , `hoooo'he`
 , `hoooo'he'he`
 , `hoooo'he'he'he`
infixl 5 `hooooo`, `hooooo'ha`, `hooooo'ha'he`, `hooooo'yo`, `hooooo'yu`, `hooooo'yok`, `hooooo'yuk`, `hooooo'yokl`
 , `hooooo'he`
 , `hooooo'he'he`
 , `hooooo'he'he'he`
infixl 4 `hoooooo`, `hoooooo'ha`, `hoooooo'ha'he`, `hoooooo'yo`, `hoooooo'yu`, `hoooooo'yok`, `hoooooo'yuk`, `hoooooo'yokl`
 , `hoooooo'he`
 , `hoooooo'he'he`
 , `hoooooo'he'he'he`
infixl 3 `hooooooo`, `hooooooo'he`, `hooooooo'he'he`, `hooooooo'he'he'he`, `hooooooo'ha`, `hooooooo'ha'he`, `hooooooo'yok`, `hooooooo'yuk`, `hooooooo'yokl`
infixl 2 `hoooooooo`, `hoooooooo'ha`, `hoooooooo'ha'he`, `hoooooooo'yok`, `hoooooooo'yuk`, `hoooooooo'yokl`
 , `hoooooooo'he`
 , `hoooooooo'he'he`
 , `hoooooooo'he'he'he`
infixl 1 `hooooooooo`, `hooooooooo'ha`, `hooooooooo'ha'he`, `hooooooooo'yok`-- , `hooooooooo'yuk`
 , `hooooooooo'he`
 , `hooooooooo'he'he`
 , `hooooooooo'he'he'he`

infixl 9 `ha`, `ha'ha`, `ha'ho`--, `ha'ho'hu`, `ha'hu` --, `ha'hu'he`, `ha'yo`, `ha'yioi`, `ha'yok`, `ha'yuk`
 , `ha'he`, `ha_ha`
infixl 8 `haa`
 , `haa'he`
infixl 7 `haaa`
 , `haaa'he`
infixl 6 `haaaa`
 , `haaaa'he`
infixl 5 `haaaaa`
 , `haaaaa'he`
infixl 4 `haaaaaa`
 , `haaaaaa'he`
infixl 3 `haaaaaaa`
 , `haaaaaaa'he`
infixl 2 `haaaaaaaa`
 , `haaaaaaaa'he`
infixl 1 `haaaaaaaaa`
 , `haaaaaaaaa'he`

infixl 9 `hu` --, `hu'he`, `hu'he'he`
infixl 8 `huu`
infixl 7 `huuu`
infixl 6 `huuuu`
infixl 5 `huuuuu`
infixl 4 `huuuuuu`
infixl 3 `huuuuuuu`
infixl 2 `huuuuuuuu`
infixl 1 `huuuuuuuuu`

infixl 9 `hd`

infixl 9 `hj`, `hj'hj`
infixl 8 `hjj`
infixl 7 `hjjj`
infixl 6 `hjjjj`
infixl 5 `hjjjjj`
infixl 4 `hjjjjjj`
infixl 3 `hjjjjjjj`
infixl 2 `hjjjjjjjj`
infixl 1 `hjjjjjjjjj`

infixl 9 `he`, `he'he`, `he'he'he` --, `he'ho`, `he'he'ho`, `he'he'he'ho`
infixl 8 `hee`, `hee'he`, `hee'he'he`
infixl 7 `heee`, `heee'he`, `heee'he'he`
infixl 6 `heeee`, `heeee'he`, `heeee'he'he`
infixl 5 `heeeee`, `heeeee'he`, `heeeee'he'he`
infixl 4 `heeeeee`, `heeeeee'he`, `heeeeee'he'he`
infixl 3 `heeeeeee`, `heeeeeee'he`, `heeeeeee'he'he`
infixl 2 `heeeeeeee`, `heeeeeeee'he`, `heeeeeeee'he'he`
infixl 1 `heeeeeeeee`, `heeeeeeeee'he`, `heeeeeeeee'he'he`

-- infixl 8 `lo`, `lo'yp`
-- infixl 7 `loo`, `loo'yp`
-- infixl 6 `looo`, `looo'yp`
-- infixl 5 `loooo`, `loooo'yp`
-- infixl 4 `looooo`, `looooo'yp`
-- infixl 3 `loooooo`, `loooooo'yp`
-- infixl 2 `looooooo`, `looooooo'yp`
-- infixl 1 `loooooooo`, `loooooooo'yp`

infixl 8 `la`
infixl 7 `laa`
infixl 6 `laaa`
infixl 5 `laaaa`
infixl 4 `laaaaa`
infixl 3 `laaaaaa`
infixl 2 `laaaaaaa`
infixl 1 `laaaaaaaa`

infixl 8 `lu`, `lu'yp`, `lu'ys`, `lu'yp'yp`
infixl 7 `luu`, `luu'yp`, `luu'ys`
infixl 6 `luuu`, `luuu'yp`, `luuu'ys`
infixl 5 `luuuu`, `luuuu'yp`, `luuuu'ys`
infixl 4 `luuuuu`, `luuuuu'yp`, `luuuuu'ys`
infixl 3 `luuuuuu`, `luuuuuu'yp`, `luuuuuu'ys`
infixl 2 `luuuuuuu`, `luuuuuuu'yp`, `luuuuuuu'ys`
infixl 1 `luuuuuuuu`, `luuuuuuuu'yp`, `luuuuuuuu'ys`

-- infixl 8 `li`, `li'yu`, `li'yok`, `li'yok'ha`, `li'yok'yokl`, `li'yokl`
infixl 7 `lii`, `lii'yok`
infixl 6 `liii`, `liii'yok`
infixl 5 `liiii`, `liiii'yok`
infixl 4 `liiiii`, `liiiii'yok`
infixl 3 `liiiiii`, `liiiiii'yok`
infixl 2 `liiiiiii`, `liiiiiii'yok`
infixl 1 `liiiiiiii`, `liiiiiiii'yok`

infixl 8 `yo`, `yo'yo`
infixl 7 `yoo`

infixl 7 `yok`, `yok'ha`, `yok'he`, `yok'he'he`, `yok'yokl` --, `yko`
infixl 6 `yokk`, `yokk'he`,  `yokk'he'he`, `yokk'yokl`
infixl 5 `yokkk`, `yokkk'he`,  `yokkk'he'he`, `yokkk'yokl`
infixl 4 `yokkkk`, `yokkkk'he`,  `yokkkk'he'he`, `yokkkk'yokl`
infixl 3 `yokkkkk`, `yokkkkk'he`,  `yokkkkk'he'he`, `yokkkkk'yokl`
infixl 2 `yokkkkkk`, `yokkkkkk'he`,  `yokkkkkk'he'he`, `yokkkkkk'yokl`
infixl 1 `yokkkkkkk`, `yokkkkkkk'he`,  `yokkkkkkk'he'he`, `yokkkkkkk'yokl`

infixl 6 `yiok`

infixl 7 `yuk`
infixl 6 `yukk`
infixl 5 `yukkk`
infixl 4 `yukkkk`
infixl 3 `yukkkkk`
infixl 2 `yukkkkkk`
infixl 1 `yukkkkkkk`

infixl 6 `yokl`, `yokl'yok`, `yokl'yokl`
infixl 5 `yokll`
infixl 4 `yoklll`
infixl 3 `yokllll`
infixl 2 `yoklllll`
infixl 1 `yokllllll`

infixl 8 `ya`

infixl 8 `yu`

infixl 8 `yp`, `yp'yo`, `yp'yp`, `yp'yp'yo`, `yp'yok`, `yp'yokl` --, `yp'yp'jt`, `yp'yp'jt'yok`

infixl 8 `ys`

infixl 7 `yoi`

infixl 7 `yai`, `yai'yai`

infixl 7 `yui`

infixl 7 `yio`, `yio'yo`

infixl 7 `yiu`

-- infixl 6 `yioi`

-- infixl 9 `v`
-- infixl 8 `vv`
-- infixl 7 `vvv`
-- infixl 6 `vvvv`
-- infixl 5 `vvvvv`
-- infixl 4 `vvvvvv`
-- infixl 3 `vvvvvvv`
-- infixl 2 `vvvvvvvv`
-- infixl 1 `vvvvvvvvv`

li, lii, liii, liiii, liiiii, liiiiii, liiiiiii, liiiiiiii
 :: Category into => into e e
li = identity

lii = li
liii = li
liiii = li
liiiii = li
liiiiii = li
liiiiiii = li
liiiiiiii = li

fo :: forall from into t a o .
 Covariant Semi Functor from into t =>
 from a o -> into (t a) (t o)
fo = map @Straight @Straight

fa :: forall from into t a o .
 Contravariant Semi Functor from into t =>
 from a o -> into (t o) (t a)
fa = map @Opposite @Straight

fu :: forall from into t a o .
 Covariant Functor from into t =>
 Mapping Straight Straight from (->) Identity (U_I_II from a) =>
 Wrapper into (Identity o) =>
 o -> into (t a) (t o)
fu = fo @from @into @t `compose` constant @from @(->)

fok :: forall from into t tt a o .
 Component Natural from into (T_TT_I t tt) t =>
 Castable Opposite into (T_TT_I t tt o) =>
 from a (tt o) -> into (t a) (t o)
fok from = component @Straight @from @into @(t `T_TT_I` tt) @t
 `compose` wrap `compose` fo from

fuk :: forall into t tt a o .
 Component Natural into into (T_TT_I t tt) t =>
 Component Natural into (->) Identity (U_I_II into a) =>
 Constant Semi Functor into into t =>
 Wrapper into (T_TT_I t tt o) =>
 Wrapper into (T_TT_I t t o) =>
 Wrapper into (Identity (tt o)) =>
 tt o -> into (t a) (t o)
fuk from = map @Straight @Straight @into @into @(t `T_TT_I` tt) @t identity
 `compose` wrap `compose` fu @into from

fokl :: forall from into t tt a o .
 Covariant Semi Functor from into t =>
 Component Natural from into (T_TT_I t tt) (TT_T_I t tt) =>
 Castable Opposite into (T_TT_I t tt o) =>
 Castable Straight into (TT_T_I t tt o) =>
 from a (tt o) -> into (t a) (tt (t o))
fokl from = wrapped
 (component @Straight @from @into @(t `T_TT_I` tt) @(t `TT_T_I` tt))
 `compose` fo from

yo, yoo, yi'yo :: forall from into t a o .
 Precategory into =>
 Covariant Yoneda from into t =>
 Castable Opposite into (U_I_II from a o) =>
 t a -> into (from a o) (t o)
yo x = yoneda @Straight x `compose` wrap

yoo = yo
yi'yo = yo

yoi :: forall from into t e a o .
 Precategory into =>
 Covariant Yoneda from into (This t e) =>
 Castable Opposite into (Straight from a o) =>
 Castable Straight into (This t e o) =>
 t a e -> into (from a o) (t o e)
yoi = fio @into unwrap `compose` yo @from @into @(This t e) `compose` wrap

yio :: forall from into t e a o .
 Precategory into =>
 Covariant Yoneda from into (That t e) =>
 Castable Opposite into (Straight from a o) =>
 Castable Straight into (That t e o) =>
 t e a -> into (from a o) (t e o)
yio = fio @into unwrap `compose` yo @from @into @(That t e) `compose` wrap

-- yioi :: forall from into w e eee a o .
--  Precategory into =>
--  Covariant Yoneda from into (W_III_I_II w eee e) =>
--  Castable Opposite into (U_I_II from a o) =>
--  Castable Straight into (W_III_I_II w eee e o) =>
--  w e a eee -> into (from a o) (w e o eee)
-- yioi x = compose unwrap (yoneda @Straight @from @into @(W_III_I_II _ _ _) (wrap x))

yu, li'yu :: forall into t a o .
 Covariant Yoneda into into t =>
 Mapping Straight Straight into into Identity (U_I_II into a) =>
 Wrapper into (U_I_II into a o) =>
 Wrapper into (Identity o) =>
 t a -> into o (t o)
yu x = yoneda @U_I_II @into @into x `compose` wrap `compose` constant

li'yu = yu

yui :: forall into t e a o .
 Terminal into =>
 Covariant Yoneda into into (U_II_I t e) =>
 Mapping Straight Straight into into Identity (U_I_II into a) =>
 Wrapper into (U_II_I t e o) =>
 Wrapper into (U_I_II into a o) =>
 Wrapper into (Identity o) =>
 t a e -> into o (t o e)
yui x = unwrap @into @(U_II_I t e _)
 `compose` yu @into (wrap @_ @(U_II_I t e _) x)

yiu :: forall into t i a o .
 Covariant Yoneda into into (U_I_II t i) =>
 Mapping Straight Straight into into Identity (U_I_II into a) =>
 Wrapper into (U_I_II into a o) =>
 Wrapper into (U_I_II t i o) =>
 Wrapper into (Identity o) =>
 t i a -> into o (t i o)
yiu x = unwrap @_ @(U_I_II t i o)
 `compose` yu @into (wrap @_ @(U_I_II t i a) x)

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
ya x = yoneda @Opposite x `compose` wrap

yai :: forall from into t e a o .
 Precategory into =>
 Contravariant Yoneda from into (This t e) =>
 Castable Opposite into (Opposite from a o) =>
 Castable Straight into (This t e o) =>
 t a e -> into (from o a) (t o e)
yai x = compose unwrap (yoneda @Opposite @from @into @(This t e) (wrap x) `compose` wrap)

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

yok, yokk, yokkk, yokkkk, yokkkkk, yokkkkkk, yokkkkkkk
 , li'yok, lii'yok, liii'yok, liiii'yok, liiiii'yok, liiiiii'yok, liiiiiii'yok, liiiiiiii'yok
 :: forall from into tt t a o .
 Component Natural into into (T_TT_I t tt) t =>
 Covariant Yoneda from into t =>
 Castable Opposite into (Straight from a (tt o)) =>
 Castable Opposite into (T_TT_I t tt o) =>
 t a -> into (from a (tt o)) (t o)
yok x = component @Straight @into @into @(T_TT_I t tt)
 `compose` wrap @into @(T_TT_I t tt _)
 `compose` yoneda @Straight @from x
 `compose` wrap

yokk = yok
yokkk = yok
yokkkk = yok
yokkkkk = yok
yokkkkkk = yok
yokkkkkkk = yok
li'yok = yok
lii'yok = yok
liii'yok = yok
liiii'yok = yok
liiiii'yok = yok
liiiiii'yok = yok
liiiiiii'yok = yok
liiiiiiii'yok = yok

yok'he, yokk'he, yokkk'he, yokkkk'he, yokkkkk'he, yokkkkkk'he, yokkkkkkk'he
 :: forall from into tt t a o .
 Component Natural into into (T_TT_I t tt) t =>
 Covariant Semi Functor into into tt =>
 Covariant Yoneda from into t =>
 Contravariant Semi Functor from into (U_II_I from (tt o)) =>
 Wrapper into (U_I_II from a (tt o)) =>
 Wrapper into (U_II_I from (tt o) a) =>
 Wrapper into (U_II_I from (tt o) (Supertype a)) =>
 -- (forall e . Wrapper into (Identity e) =>
 (forall e . Wrapper into (T_TT_I t tt e)) =>
 Wrapper into (T_TT_I t tt o) =>
 Castable Straight from a =>
 t a -> into (from (Supertype a) (tt o)) (t o)
yok'he x = yok @from @into x `compose` fai @from he

yokk'he = yok'he
yokkk'he = yok'he
yokkkk'he = yok'he
yokkkkk'he = yok'he
yokkkkkk'he = yok'he
yokkkkkkk'he = yok'he

yok'he'he, yokk'he'he, yokkk'he'he, yokkkk'he'he, yokkkkk'he'he, yokkkkkk'he'he, yokkkkkkk'he'he
 :: forall from into tt t a o .
 Component Natural into into (T_TT_I t tt) t =>
 Covariant Yoneda from into t =>
 Covariant Semi Functor into into tt =>
 Contravariant Semi Functor from into (U_II_I from (tt o)) =>
 Wrapper into (U_I_II from a (tt o)) =>
 Wrapper into (U_II_I from (tt o) a) =>
 Wrapper into (U_II_I from (tt o) (Supertype (Supertype a))) =>
 (forall e . Wrapper into (T_TT_I t tt e)) =>
 Castable Straight from a =>
 Castable Straight from (Supertype a) =>
 t a -> into (from (Supertype (Supertype a)) (tt o)) (t o)
yok'he'he x = yok @from @into x `compose` fai @from he'he

yokk'he'he = yok'he'he
yokkk'he'he = yok'he'he
yokkkk'he'he = yok'he'he
yokkkkk'he'he = yok'he'he
yokkkkkk'he'he = yok'he'he
yokkkkkkk'he'he = yok'he'he

yuk, yukk, yukkk, yukkkk, yukkkkk, yukkkkkk, yukkkkkkk, yi'yuk
 :: forall into tt t a o .
 Covariant Yoneda into into t =>
 Component Natural into into (T_TT_I t tt) t =>
 Mapping Straight Straight into into Identity (U_I_II into a) =>
 Wrapper into (T_TT_I t tt o) =>
 Wrapper into (Identity (tt o)) =>
 Wrapper into (U_I_II into a (tt o)) =>
 t a -> into (tt o) (t o)
yuk x = yok @into @into x `compose` constant

-- yok x = component @Straight @(->) @into @(T_TT_I t tt)
 -- `compose` wrap @into @(T_TT_I t tt _)
 -- `compose` yoneda @Straight @from x
 -- `compose` wrap

yukk = yuk @into @tt
yukkk = yuk @into @tt
yukkkk = yuk @into @tt
yukkkkk = yuk @into @tt
yukkkkkk = yuk @into @tt
yukkkkkkk = yuk @into @tt
yi'yuk = yuk @into @tt

-- TODO: try to generalize
-- yko :: forall from into tt t a o .
--  Precategory into =>
--  Component Natural (->) (->) t (T_TT_I t tt) =>
--  Covariant Yoneda from into t =>
--  Castable Opposite into (Straight from (tt a) o) =>
--  t a -> into (from (tt a) o) (t o)
-- yko = yoneda @Straight @from @into identity `compose` unwrap
--  `compose` component @Straight @(->) @(->) @t @(T_TT_I t tt)

yokl, yokll, yoklll, yokllll, yoklllll, yokllllll, li'yokl :: forall from into tt t a o .
 Unlabelable into tt =>
 Component Natural from into (T_TT_I t tt) (TT_T_I t tt) =>
 Covariant Yoneda from into t =>
 Castable Opposite into (Straight from a (tt o)) =>
 Castable Straight into (TT_T_I t tt o) =>
 Castable Opposite into (T_TT_I t tt o) =>
 t a -> into (from a (tt o)) (Unlabeled tt (t o))
yokl x = unlabel
 `compose` unwrap @into @(TT_T_I t tt _)
 `compose` component @Straight @from @into @(T_TT_I t tt) @(TT_T_I t tt)
 `compose` wrap @into @(T_TT_I t tt _)
 `compose` yoneda @Straight @from x
 `compose` wrap

yokll = yokl
yoklll = yokl
yokllll = yokl
yoklllll = yokl
yokllllll = yokl

li'yokl = yokl

yiok :: forall from into tt t i a o .
 Component Natural from into (T_TT_I (U_I_II t i) tt) (U_I_II t i) =>
 Covariant Yoneda from into (U_I_II t i) =>
 Castable Opposite into (U_I_II from a (tt o)) =>
 Castable Straight into (U_I_II t i o) =>
 Castable Opposite into (T_TT_I (U_I_II t i) tt o) =>
 t i a -> into (from a (tt o)) (t i o)
yiok x = unwrap @into @(U_I_II t i o)
 `compose` component @Straight @from @into @(T_TT_I (U_I_II t i) tt)
 `compose` wrap @into @(T_TT_I (U_I_II t i) tt _)
 `compose` yoneda @Straight @from (U_I_II x)
 `compose` wrap

-- TODO: label inner effect
yok'yokl, yokk'yokl, yokkk'yokl, yokkkk'yokl, yokkkkk'yokl, yokkkkkk'yokl, yokkkkkkk'yokl, li'yok'yokl
 :: forall from into t tt ttt a o .
 Covariant Yoneda from into t =>
 Covariant Endo Semi Functor into t =>
 Covariant Endo Semi Functor into tt =>
 Covariant Endo Semi Functor from ttt =>
 Contravariant Endo Semi Functor (->) (U_II_I into (t (ttt o))) =>
 Component Natural into into (T_TT_I t tt) t =>
 Component Natural from from (T_TT_I ttt tt) (TT_T_I ttt tt) =>
 Castable Opposite into (U_I_II from (ttt a) (tt (ttt o))) =>
 (forall e . Wrapper into (T_TT_I t tt e)) =>
 (forall e . Wrapper from (T_TT_I ttt tt e)) =>
 (forall e . Wrapper from (TT_T_I ttt tt e)) =>
 t (ttt a) -> into (from a (tt o)) (t (ttt o))
yok'yokl x = fai fokl (yok @from @into x)

yokk'yokl = yok'yokl
yokkk'yokl = yok'yokl
yokkkk'yokl = yok'yokl
yokkkkk'yokl = yok'yokl
yokkkkkk'yokl = yok'yokl
yokkkkkkk'yokl = yok'yokl

li'yok'yokl = yok'yokl

yokl'yok :: forall from into t tt ttt a o .
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
yokl'yok x = fai fok (yokl @from @into x)

yokl'yokl :: forall from into t tt ttt a o .
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
yokl'yokl x = fai fokl (yokl @from @into x)

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
fio from = unwrap `compose` fo @_ @_ @(U_I_II _ _) from `compose` wrap

fioi :: forall from into t a o i ii .
 Covariant Semi Functor from into (W_III_I_II t ii i) =>
 Wrapper into (W_III_I_II t ii i a) =>
 Wrapper into (W_III_I_II t ii i o) =>
 from a o -> into (t i a ii) (t i o ii)
fioi from = unwrap `compose` fo @_ @_ @(W_III_I_II _ _ _) from `compose` wrap

foi :: forall from into t a o i .
 Covariant Semi Functor from into (U_II_I t i) =>
 Wrapper into (U_II_I t i a) =>
 Wrapper into (U_II_I t i o) =>
 from a o -> into (t a i) (t o i)
foi from = unwrap `compose` fo @_ @_ @(U_II_I _ _) from `compose` wrap

fai :: forall from into t a o i .
 Contravariant Semi Functor from into (U_II_I t i) =>
 Wrapper into (U_II_I t i a) =>
 Wrapper into (U_II_I t i o) =>
 from a o -> into (t o i) (t a i)
fai from = unwrap `compose` fa @_ @_ @(U_II_I _ _) from `compose` wrap

fai_ :: forall from into t a o i .
 Contravariant Semi Functor from into (U_II_I t i) =>
 Wrapper into (U_II_I t i a) =>
 Wrapper into (U_II_I t i (Supertype a)) =>
 Wrapper into (U_II_I t i o) =>
 Wrapper from a =>
 from (Supertype a) o -> into (t o i) (t a i)
fai_ from = fai (from `compose` unwrap)

fio'fo :: forall from into t tt e a o .
 Covariant Semi Functor into into (U_I_II t e) =>
 Covariant Semi Functor from into tt =>
 Wrapper into (U_I_II t e (tt a)) =>
 Wrapper into (U_I_II t e (tt o)) =>
 from a o -> into (t e (tt a)) (t e (tt o))
fio'fo from = fio @into @into (fo @from @into from)

fiu :: forall from into t a o e .
 Covariant Functor from into (U_I_II t e) =>
 Mapping Straight Straight from (->) Identity (U_I_II from a) =>
 Wrapper into (U_I_II t e a) =>
 Wrapper into (U_I_II t e o) =>
 Wrapper into (Identity o) =>
 o -> into (t e a) (t e o)
fiu from = unwrap `compose` fu @from @into @(U_I_II _ _) from `compose` wrap

-- TODO: remove
-- fiu'_ :: forall from into t a o e .
--  Covariant Semi Functor into into (U_I_II t e) =>
--  Constant Semi Functor into into (U_I_II t e) =>
--  Castable Opposite (->) (into () o) =>
--  Castable Opposite (->) (Supertype (into () o)) =>
--  Castable Straight into (U_I_II t e o) =>
--  Castable Opposite into (U_I_II t e a) =>
--  Supertype (Supertype (into () o)) -> into (t e a) (t e o)
-- fiu'_ from = unwrap `compose` fu @_ @(U_I_II _ _) (wrap from) `compose` wrap

ho, hoo, hooo, hoooo, hooooo, hoooooo, hooooooo, hoooooooo, hooooooooo, yi'ho :: forall from into u i a o .
 Precategory into =>
 Covariant Yoneda from into (U_I_II u i) =>
 Castable Straight into (U_I_II u i o) =>
 Castable Opposite into (U_I_II from a o) =>
 u i a -> into (from a o) (u i o)
ho = yio @from @into @u

hoo = ho
hooo = ho
hoooo = ho
hooooo = ho
hoooooo = ho
hooooooo = ho
hoooooooo = ho
hooooooooo = ho
yi'ho = ho

ho'he, hoo'he, hooo'he, hoooo'he, hooooo'he, hoooooo'he, hooooooo'he, hoooooooo'he, hooooooooo'he
 :: forall from into u i a o .
 Covariant Yoneda from into (U_I_II u i) =>
 Contravariant Semi Functor from into (U_II_I from o) =>
 Covariant Semi Functor from into (U_I_II from o) =>
 Wrapper from a =>
 Wrapper into (U_I_II u i o) =>
 Wrapper into (U_I_II from a o) =>
 Wrapper into (U_II_I from o a) =>
 Wrapper into (U_II_I from o (Supertype a)) =>
 u i a -> into (from (Supertype a) o) (u i o)
ho'he = fai @into (fai @from he) `compose` yio @from @into @u

hoo'he = ho'he
hooo'he = ho'he
hoooo'he = ho'he
hooooo'he = ho'he
hoooooo'he = ho'he
hooooooo'he = ho'he
hoooooooo'he = ho'he
hooooooooo'he = ho'he

ho'he'he, hoo'he'he, hooo'he'he, hoooo'he'he, hooooo'he'he, hoooooo'he'he, hooooooo'he'he, hoooooooo'he'he, hooooooooo'he'he
 :: forall from into u i a o .
 Covariant Yoneda from into (U_I_II u i) =>
 Contravariant Semi Functor from into (U_II_I from o) =>
 Covariant Semi Functor from into (U_I_II from o) =>
 Wrapper from a =>
 Wrapper from (Supertype a) =>
 Wrapper into (U_I_II u i o) =>
 Wrapper into (U_I_II from a o) =>
 Wrapper into (U_II_I from o a) =>
 Wrapper into (U_II_I from o (Supertype a)) =>
 Wrapper into (U_II_I from o (Supertype (Supertype a))) =>
 u i a -> into (from (Supertype (Supertype a)) o) (u i o)
ho'he'he = fai @into (fai @from (he `compose` he)) `compose` yio @from @into @u

hoo'he'he = ho'he'he
hooo'he'he = ho'he'he
hoooo'he'he = ho'he'he
hooooo'he'he = ho'he'he
hoooooo'he'he = ho'he'he
hooooooo'he'he = ho'he'he
hoooooooo'he'he = ho'he'he
hooooooooo'he'he = ho'he'he

ho'he'he'he, hoo'he'he'he, hooo'he'he'he, hoooo'he'he'he, hooooo'he'he'he, hoooooo'he'he'he, hooooooo'he'he'he, hoooooooo'he'he'he, hooooooooo'he'he'he
 :: forall from into u i a o .
 Precategory from =>
 Precategory into =>
 Covariant Yoneda from into (U_I_II u i) =>
 Contravariant Semi Functor from into (U_II_I from o) =>
 Covariant Semi Functor from into (U_I_II from o) =>
 Wrapper from a =>
 Wrapper from (Supertype a) =>
 Wrapper from (Supertype (Supertype a)) =>
 Wrapper into (U_I_II u i o) =>
 Wrapper into (U_I_II from a o) =>
 Wrapper into (U_II_I from o a) =>
 Wrapper into (U_II_I from o (Supertype a)) =>
 Wrapper into (U_II_I from o (Supertype (Supertype a))) =>
 Wrapper into (U_II_I from o (Supertype (Supertype (Supertype a)))) =>
 u i a -> into (from (Supertype (Supertype (Supertype a))) o) (u i o)
ho'he'he'he x = yio @from @into @u x `compose` fai @from he `compose` fai @from he `compose` fai @from he

hoo'he'he'he = ho'he'he'he
hooo'he'he'he = ho'he'he'he
hoooo'he'he'he = ho'he'he'he
hooooo'he'he'he = ho'he'he'he
hoooooo'he'he'he = ho'he'he'he
hooooooo'he'he'he = ho'he'he'he
hoooooooo'he'he'he = ho'he'he'he
hooooooooo'he'he'he = ho'he'he'he

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

ho'ho'hu :: forall from u uu uuu o e ee eee a .
 Category from =>
 Covariant Yoneda uuu (->) (U_I_II u e) =>
 Covariant Semi Functor from uuu (U_I_II uu ee) =>
 Covariant Endo Semi Functor from (U_I_II uuu eee) =>
 Constant Endo Semi Functor from (U_I_II uuu eee) =>
 Mapping Straight Straight from (->) Identity (U_I_II from a) =>
 Wrapper uuu (U_I_II uu ee (uuu eee a)) =>
 Wrapper uuu (U_I_II uu ee (uuu eee o)) =>
 Wrapper from (U_I_II uuu eee o) =>
 Wrapper from (U_I_II uuu eee a) =>
 Wrapper from (Identity o) =>
 Wrapper (->) (U_1_I from a o) =>
 u e (uu ee (uuu eee a)) -> o -> u e (uu ee (uuu eee o))
ho'ho'hu = fai (fio @from `compose` fiu @from) `compose` ho @uuu

ho'hu :: forall from u uu o e ee a .
 Category from =>
 Covariant Yoneda u from (U_I_II u e) =>
 Contravariant Yoneda (->) (->) (Opposite u e) =>
 Covariant Semi Functor from u (U_I_II uu ee) =>
 Covariant Endo Semi Functor (->) (Straight (->) (u e (uu a ee))) =>
 Contravariant Semi Functor (->) (->) (Opposite from (u e (uu ee o))) =>
 Mapping Straight Straight from (->) Identity (U_I_II from a) =>
 Wrapper u (Straight uu ee a) =>
 Wrapper u (Straight uu ee o) =>
 Wrapper from (Straight uu ee o) =>
 Wrapper from (Straight u e (uu ee o)) =>
 Wrapper from (Straight u (uu ee a) (uu ee o)) =>
 Wrapper u (Identity o) =>
 u e (uu ee a) -> from o (u e (uu ee o))
ho'hu = fai (fiu @from) `compose` ho @u

ho'ha, hoo'ha, hooo'ha, hoooo'ha, hooooo'ha, hoooooo'ha, hooooooo'ha, hoooooooo'ha, hooooooooo'ha
 :: forall from u uu o e ee a .
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
hooo'ha = ho'ha
hoooo'ha = ho'ha
hooooo'ha = ho'ha
hoooooo'ha = ho'ha
hooooooo'ha = ho'ha
hoooooooo'ha = ho'ha
hooooooooo'ha = ho'ha

ho'ha'he, hoo'ha'he, hooo'ha'he, hoooo'ha'he, hooooo'ha'he, hoooooo'ha'he, hooooooo'ha'he, hoooooooo'ha'he, hooooooooo'ha'he
 :: forall from u uu o e ee a .
 Covariant Yoneda u (->) (Straight u e) =>
 Contravariant Semi Functor from u (Opposite uu ee) =>
 Wrapper u (U_II_I uu ee a) =>
 Wrapper u (U_II_I uu ee (Supertype a)) =>
 Wrapper u (U_II_I uu ee o) =>
 Wrapper from a =>
 u e (uu o ee) -> from (Supertype a) o -> u e (uu a ee)
ho'ha'he x = fai fai_ (ho @u x)

hoo'ha'he = ho'ha'he
hooo'ha'he = ho'ha'he
hoooo'ha'he = ho'ha'he
hooooo'ha'he = ho'ha'he
hoooooo'ha'he = ho'ha'he
hooooooo'ha'he = ho'ha'he
hoooooooo'ha'he = ho'ha'he
hooooooooo'ha'he = ho'ha'he

ho'yo, hoo'yo, hooo'yo, hoooo'yo, hooooo'yo, hoooooo'yo :: forall from u t o e a .
 Covariant Yoneda from (->) (Straight u e) =>
 Contravariant Yoneda from (->) (Opposite u e) =>
 Covariant Endo Semi Functor from t =>
 Constant Semi Functor from (->) t =>
 u e (t a) -> from a o -> u e (t o)
ho'yo x = fai (fo @from) (ho @from x)

hoo'yo = ho'yo
hooo'yo = ho'yo
hoooo'yo = ho'yo
hooooo'yo = ho'yo
hoooooo'yo = ho'yo

ho'yu, hoo'yu, hooo'yu, hoooo'yu, hooooo'yu, hoooooo'yu, hooooooo'yu, hoooooooo'yu, hooooooooo'yu  :: forall u t o e a .
 Covariant Yoneda (->) (->) (Straight u e) =>
 Contravariant Yoneda (->) (->) (Opposite u e) =>
 Mapping Straight Straight (->) (->) Identity (U_I_II (->) a) =>
 Covariant Endo Semi Functor (->) t =>
 Constant Semi Functor (->) (->) t =>
 u e (t a) -> o -> u e (t o)
ho'yu x = fai @(->) @(->) (fu @(->)) (ho @(->) x)

hoo'yu = ho'yu
hooo'yu = ho'yu
hoooo'yu = ho'yu
hooooo'yu = ho'yu
hoooooo'yu = ho'yu
hooooooo'yu = ho'yu
hoooooooo'yu = ho'yu
hooooooooo'yu = ho'yu

ho'yioi :: forall from u t o e ee eee a .
 Covariant Yoneda from (->) (Straight u e) =>
 Contravariant Yoneda from (->) (Opposite u e) =>
 Covariant Endo Semi Functor from (W_III_I_II t eee ee) =>
 Wrapper from (W_III_I_II t eee ee a) =>
 Wrapper from (W_III_I_II t eee ee o) =>
 u e (t ee a eee) -> from a o -> u e (t ee o eee)
ho'yioi x = fai (fioi @from) (ho @from x)

-- he'ho
 -- :: forall from into u i a o .
 -- Precategory from =>
 -- Precategory into =>
 -- Covariant Yoneda from into (U_I_II u i) =>
 -- Contravariant Semi Functor from (->) (U_II_I u a) =>
 -- Covariant Semi Functor from into (U_I_II from o) =>
 -- Wrapper from i =>
 -- Wrapper into (U_I_II u i o) =>
 -- Wrapper into (U_I_II from a o) =>
 -- Wrapper into (U_II_I from o a) =>
 -- u (Supertype i) a -> into (from a o) (u i o)
-- he'ho = yio @from @into @u `compose` he @from

-- he'hu
 -- :: forall from into u i a o .
 -- Precategory from =>
 -- Category into =>
 -- Covariant Yoneda into into (U_I_II u i) =>
 -- Constant Semi Functor (->) (->) (U_I_II u i) =>
 -- Mapping Straight Straight (->) (->) (U_I_II u i) (U_I_II u i) =>
 -- Contravariant Semi Functor from (->) (U_II_I u a) =>
 -- Covariant Semi Functor from into (U_I_II from o) =>
 -- Wrapper from i =>
 -- Wrapper into (into () o) =>
 -- Wrapper into (U_I_II into () o) =>
 -- Wrapper into (U_I_II u i o) =>
 -- Wrapper into (U_I_II from a o) =>
 -- u (Supertype i) a -> into (Supertype (into () o)) (u i o)
-- he'hu = yiu @into @u `compose` he @from

-- he'he'ho
 -- :: forall from into u i a o .
 -- Precategory from =>
 -- Precategory into =>
 -- Covariant Yoneda from into (U_I_II u i) =>
 -- Contravariant Semi Functor from (->) (U_II_I u a) =>
 -- Covariant Semi Functor from into (U_I_II from o) =>
 -- Castable Straight from i =>
 -- Castable Straight from (Supertype i) =>
 -- Castable Straight into (U_I_II u i o) =>
 -- Castable Opposite into (U_I_II from a o) =>
 -- Wrapper into (U_II_I from o a) =>
 -- Wrapper into (U_II_I from o (Supertype a)) =>
 -- u (Supertype (Supertype i)) a -> into (from a o) (u i o)
-- -- he'he'ho = yio @from @into @u `compose` fai @from he'he

-- he'he'he'ho
 -- :: forall from into u i a o .
 -- Precategory from =>
 -- Precategory into =>
 -- Covariant Yoneda from into (U_I_II u i) =>
 -- Contravariant Semi Functor from (->) (U_II_I u a) =>
 -- Covariant Semi Functor from into (U_I_II from o) =>
 -- Wrapper from i =>
 -- Wrapper from (Supertype i) =>
 -- Wrapper from (Supertype (Supertype i)) =>
 -- Wrapper into (U_I_II u i o) =>
 -- Wrapper into (U_I_II from a o) =>
 -- Wrapper into (U_II_I from o a) =>
 -- -- Wrapper into (U_II_I from o (Supertype a)) =>
 -- u (Supertype (Supertype (Supertype i))) a -> into (from a o) (u i o)
-- he'he'he'ho = yio @from @into @u `compose` fai @from he'he'he

ha, haa, haaa, haaaa, haaaaa, haaaaaa, haaaaaaa, haaaaaaaa, haaaaaaaaa :: forall from u e a o .
 Contravariant Yoneda from (->) (U_II_I u e) =>
 u a e -> from o a -> u o e
ha x = yai @from @(->) @u x

haa = ha
haaa = ha
haaaa = ha
haaaaa = ha
haaaaaa = ha
haaaaaaa = ha
haaaaaaaa = ha
haaaaaaaaa = ha

ha'he, haa'he, haaa'he, haaaa'he, haaaaa'he, haaaaaa'he, haaaaaaa'he, haaaaaaaa'he, haaaaaaaaa'he :: forall from u e a o .
 Contravariant Yoneda from (->) (U_II_I u e) =>
 Wrapper from o =>
 u a e -> from (Supertype o) a -> u o e
ha'he x = yai @from @(->) @u x `compose` fai (he @from)

haa'he = ha'he
haaa'he = ha'he
haaaa'he = ha'he
haaaaa'he = ha'he
haaaaaa'he = ha'he
haaaaaaa'he = ha'he
haaaaaaaa'he = ha'he
haaaaaaaaa'he = ha'he

ha'he'he, haa'he'he, haaa'he'he, haaaa'he'he, haaaaa'he'he, haaaaaa'he'he, haaaaaaa'he'he, haaaaaaaa'he'he, haaaaaaaaa'he'he
 :: forall from into u e a o .
 Contravariant Yoneda from into (U_II_I u e) =>
 Contravariant Semi Functor from into (U_II_I from a) =>
 Wrapper from o =>
 Wrapper into (U_II_I from a o) =>
 Wrapper into (U_II_I u e o) =>
 Wrapper into (U_II_I from a (Supertype (Supertype o))) =>
 Wrapper from (Supertype o) =>
 u a e -> into (from (Supertype (Supertype o)) a) (u o e)
ha'he'he = fai @into (fai @from (he `compose` he)) `compose` yai @from @into @u

haa'he'he = ha'he'he
haaa'he'he = ha'he'he
haaaa'he'he = ha'he'he
haaaaa'he'he = ha'he'he
haaaaaa'he'he = ha'he'he
haaaaaaa'he'he = ha'he'he
haaaaaaaa'he'he = ha'he'he
haaaaaaaaa'he'he = ha'he'he

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
hv x from = he (x `ha` from)

ha_ha :: forall from u uu a o e ee .
 Contravariant Yoneda u (->) (Opposite u e) =>
 Contravariant Semi Functor from u (Opposite uu ee) =>
 Contravariant Semi Functor u u (Opposite uu ee) =>
 Wrapper u (Opposite uu ee (Supertype a)) =>
 Wrapper u (Opposite uu ee o) =>
 Wrapper u (Opposite uu ee a) =>
 Wrapper u a =>
 Wrapper from a =>
 u (uu a ee) e -> from (Supertype a) o -> u (uu o ee) e
ha_ha x = fai @(->) @(->) fai_ (ha @u x)

ha'ho :: forall from u uu o e ee a .
 Covariant Yoneda u (->) (Straight u e) =>
 Contravariant Yoneda u (->) (Opposite u e) =>
 Covariant Semi Functor from u (U_I_II uu ee) =>
 Wrapper u (U_I_II uu ee a) =>
 Wrapper u (U_I_II uu ee o) =>
 u (uu ee o) e -> from a o -> u (uu ee a) e
ha'ho x = fai @(->) @(->) fio (ha @u x)

-- ha'ho'hu :: forall from into u uu uuu o e ee eee a .
 -- Precategory from =>
 -- Contravariant Yoneda uuu (->) (U_II_I u e) =>
 -- Covariant Semi Functor from uuu (U_I_II uu ee) =>
 -- Covariant Endo Semi Functor from (U_I_II uuu eee) =>
 -- Mapping Straight Straight into into Identity (U_I_II into a) =>
 -- Wrapper uuu (U_I_II uu ee (uuu eee a)) =>
 -- Wrapper uuu (U_I_II uu ee (uuu eee o)) =>
 -- Wrapper from (U_I_II uuu eee o) =>
 -- Wrapper from (U_I_II uuu eee a) =>
 -- Wrapper (->) (U_1_I from a o) =>
 -- u (uu ee (uuu eee o)) e -> Supertype (U_1_I from a o) -> u (uu ee (uuu eee a)) e
-- ha'ho'hu = fai (fio @from `compose` fiu) `compose` ha @uuu

-- ha'hu :: forall from u uu o e ee a .
 -- Covariant Semi Functor u u (U_I_II uu ee) =>
 -- Constant Semi Functor u u (U_I_II uu ee) =>
 -- Contravariant Yoneda u (->) (Opposite u e) =>
 -- Wrapper u (U_I_II uu ee a) =>
 -- Wrapper u (U_I_II uu ee o) =>
 -- Castable Opposite u (U_1_I u a o) =>
 -- Castable Opposite (->) (U_1_I u a o) =>
 -- u (uu ee o) e -> Supertype (U_1_I u a o) -> u (uu ee a) e
-- ha'hu x = fai @(->) @(->) fiu (ha @u x)

-- ha'he'hu :: forall from u uu o e ee a .
 -- Covariant Semi Functor u u (U_I_II uu ee) =>
 -- Constant Semi Functor u u (U_I_II uu ee) (U_I_II uu ee) =>
 -- Contravariant Yoneda u (->) (Opposite u e) =>
 -- Wrapper u (U_I_II uu ee a) =>
 -- Wrapper u (U_I_II uu ee o) =>
 -- Castable Opposite (->) (u () o) =>
 -- u (uu ee o) e -> Supertype (u () o) -> u (uu ee a) e
-- ha'he'hu x = fai @(->) @(->) fiu (ha'he @u x)

-- ha'hu'he :: forall from u uu o e ee a .
--  Covariant Semi Functor u u (U_I_II uu ee) =>
--  Constant Semi Functor u u (U_I_II uu ee) =>
--  Contravariant Yoneda u (->) (Opposite u e) =>
--  Wrapper u (U_I_II uu ee a) =>
--  Wrapper u (U_I_II uu ee o) =>
--  Castable Opposite (->) (Supertype (u () o)) =>
--  Castable Opposite (->) (u () o) =>
--  u (uu ee o) e -> Supertype (Supertype (u () o)) -> u (uu ee a) e
-- ha'hu'he x = fai @(->) @(->) fiu'_ (ha @u x)

ha'yo :: forall from u t o e a .
 Covariant Yoneda from (->) (Straight u e) =>
 Contravariant Yoneda from (->) (Opposite u e) =>
 Covariant Endo Semi Functor from t =>
 Constant Semi Functor from (->) t =>
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

-- -- TODO: replace with `ho_`
-- ho_yi :: forall from u e a o .
--  Covariant Endo Semi Functor from (That from a) =>
--  Covariant Yoneda from (->) (U_I_II u e) =>
--  Contravariant Semi Functor from (->) (U_II_I (->) (u e (Supertype o))) =>
--  Contravariant Yoneda from (->) (U_II_I (->) (u e (Supertype o))) =>
--  Castable Straight (->) (U_I_II u e o) =>
--  Castable Straight from o =>
--  Wrapper from (U_I_II from a o) =>
--  Wrapper from (U_I_II from a (Supertype o)) =>
--  u e a -> from a o -> u e (Supertype o)
-- ho_yi x = fai @from (fio @from he) (ho x)

-- -- TODO: replace with `ho_ho`
-- ho_yi'ho :: forall from u e a o .
--  Covariant Yoneda from (->) (That u e) =>
--  Castable Straight from a =>
--  u e a -> from (Supertype a) o -> u e o
-- ho_yi'ho x xx = x `ho` he @from `ho` xx

hu, huu, huuu, huuuu, huuuuu, huuuuuu, huuuuuuu, huuuuuuuu, huuuuuuuuu ::
 forall into t i a o .
 Covariant Yoneda into into (U_I_II t i) =>
 Mapping Straight Straight into into Identity (U_I_II into a) =>
 Wrapper into (U_I_II into a o) =>
 Wrapper into (U_I_II t i o) =>
 Wrapper into (Identity o) =>
 t i a -> into o (t i o)
hu = yiu

huu = hu
huuu = hu
huuuu = hu
huuuuu = hu
huuuuuu = hu
huuuuuuu = hu
huuuuuuuu = hu
huuuuuuuuu = hu

-- hu'he, huu'he, huuu'he, huuuu'he, huuuuu'he, huuuuuu'he, huuuuuuu'he, huuuuuuuu'he, huuuuuuuuu'he
--  :: forall from into a o .
--  Precategory into =>
--  Precategory from =>
--  Covariant Yoneda from into (U_1_I from ()) =>
--  Contravariant Endo Semi Functor from (U_II_I from o) =>
--  Castable Opposite into (U_I_II from a o) =>
--  Castable Opposite into (U_1_I from a o) =>
--  Castable Straight into (U_1_I from a o) =>
--  Castable Straight from a =>
--  Wrapper from (U_II_I from o a) =>
--  Wrapper from (U_II_I from o (Supertype a)) =>
--  Castable Straight into (U_I_II from a o) =>
--  Castable Straight into (U_1_I from a o) =>
--  Contravariant Yoneda from (->) (U_II_I into (Supertype (U_1_I from a o))) =>
--  Supertype (U_1_I from a o) -> into (from (Supertype a) o) (Supertype (U_1_I from a o))
-- hu'he x = hu @from @into @a x `yai'yai` he @from @a
-- huu'he x = hu @from @into @a x `yai'yai` he @from @a
-- huuu'he x = hu @from @into @a x `yai'yai` he @from @a
-- huuuu'he x = hu @from @into @a x `yai'yai` he @from @a
-- huuuuu'he x = hu @from @into @a x `yai'yai` he @from @a
-- huuuuuu'he x = hu @from @into @a x `yai'yai` he @from @a
-- huuuuuuu'he x = hu @from @into @a x `yai'yai` he @from @a
-- huuuuuuuu'he x = hu @from @into @a x `yai'yai` he @from @a
-- huuuuuuuuu'he x = hu @from @into @a x `yai'yai` he @from @a

-- huu'he = hu'he
-- huuu'he = hu'he
-- huuuu'he = hu'he
-- huuuuu'he = hu'he
-- huuuuuu'he = hu'he
-- huuuuuuu'he = hu'he
-- huuuuuuuu'he = hu'he
-- huuuuuuuuu'he = hu'he

-- hu'he'he, huu'he'he, huuu'he'he, huuuu'he'he, huuuuu'he'he, huuuuuu'he'he, huuuuuuu'he'he, huuuuuuuu'he'he, huuuuuuuuu'he'he
 -- :: forall from into a o .
 -- Precategory into =>
 -- Precategory from =>
 -- Covariant Yoneda from into (U_1_I from a) =>
 -- Constant Yoneda from into (U_1_I from a) =>
 -- Contravariant Endo Semi Functor from (U_II_I from o) =>
 -- Castable Opposite into (U_I_II from a o) =>
 -- Castable Opposite into (U_1_I from a a) =>
 -- Castable Straight into (U_1_I from a o) =>
 -- Castable Straight from a =>
 -- Castable Straight from (Supertype a) =>
 -- Wrapper from (U_II_I from o a) =>
 -- Wrapper from (U_II_I from o (Supertype (Supertype a))) =>
 -- Castable Straight into (U_I_II from a o) =>
 -- Wrapper into (U_1_I from a o) =>
 -- Contravariant Yoneda from (->) (U_II_I into (Supertype (U_1_I from a o))) =>
 -- a -> into (from (Supertype (Supertype a)) o) o
-- hu'he'he x = hu @from @into @a x `yai'yai` he'he @from @a
-- huu'he'he x = hu @from @into @a x `yai'yai` he'he @from @a
-- huuu'he'he x = hu @from @into @a x `yai'yai` he'he @from @a
-- huuuu'he'he x = hu @from @into @a x `yai'yai` he'he @from @a
-- huuuuu'he'he x = hu @from @into @a x `yai'yai` he'he @from @a
-- huuuuuu'he'he x = hu @from @into @a x `yai'yai` he'he @from @a
-- huuuuuuu'he'he x = hu @from @into @a x `yai'yai` he'he @from @a
-- huuuuuuuu'he'he x = hu @from @into @a x `yai'yai` he'he @from @a
-- huuuuuuuuu'he'he x = hu @from @into @a x `yai'yai` he'he @from @a

-- v :: (a -> o) -> a -> e -> o
-- v from x y = from (constant x y)

-- vv = v
-- vvv = v
-- vvvv = v
-- vvvvv = v
-- vvvvvv = v
-- vvvvvvv = v
-- vvvvvvvv = v
-- vvvvvvvvv = v

ro :: forall into hom t i .
 Category into =>
 Covariant (Representable hom) into into t =>
 Castable Straight into (Straight hom (Representation t) i) =>
 into (t i) (hom (Representation t) i)
ro = he `compose` map @Straight @Straight @into @into @t @(Straight hom (Representation t)) identity

ra :: forall into hom t i .
 Category into =>
 Contravariant (Representable hom) into into t =>
 Castable Straight into (Opposite hom (Representation t) i) =>
 into (t i) (hom i (Representation t))
ra = he `compose` map @Opposite @Straight @into @into @t @(Opposite hom (Representation t)) identity

lj :: forall from into t tt a o .
 Adjoint Functor from into t tt =>
 Castable Straight into ((T_TT_I tt t) a) =>
 Castable Opposite into (Identity a) =>
 from (t a) o -> into a (tt o)
lj from = fo from
 `compose` he @into
 `compose` component @Straight @from @into @Identity @(tt `T_TT_I` t)
 `compose` wrap @into

ilj :: forall from into t tt e ee a o .
 Adjoint Functor from into (U_I_II t e) (U_I_II tt ee) =>
 Castable Straight into ((T_TT_I (U_I_II tt ee) (U_I_II t e)) a) =>
 Castable Straight into (U_I_II tt ee o) =>
 Castable Opposite into (Identity a) =>
 Castable Straight from (U_I_II t e a) =>
 from (t e a) o -> into a (tt ee o)
ilj from = he @into @(U_I_II tt _ _)
 `compose` fo (from `compose` he @from @(U_I_II t _ _))
 `compose` he @into @(T_TT_I _ _ _)
 `compose` component @Straight @from @into @Identity @(U_I_II tt ee `T_TT_I` U_I_II t e)
 `compose` wrap @into

hd :: forall from into t tt e a o .
 Adjoint Functor from into (U_II_I t e) (U_I_II tt e) =>
 Castable Straight into ((U_I_II tt e `T_TT_I` U_II_I t e) a) =>
 Castable Straight into (U_I_II tt e o) =>
 Castable Opposite into (Identity a) =>
 Castable Straight from (U_II_I t e a) =>
 from (t a e) o -> into a (tt e o)
hd from = he @into @(U_I_II tt _ _)
 `compose` fo (from `compose` he @from @(U_II_I t _ _))
 `compose` he @into @(T_TT_I _ _ _)
 `compose` component @Straight @from @into @Identity @(U_I_II tt e `T_TT_I` U_II_I t e)
 `compose` wrap @into

hj, hjj, hjjj, hjjjj, hjjjjj, hjjjjjj, hjjjjjjj, hjjjjjjjj, hjjjjjjjjj :: forall from into t tt e a o .
 Adjoint Functor from into (U_II_I t e) (U_I_II tt e) =>
 Castable Opposite from ((T_TT_I (U_II_I t e) (U_I_II tt e)) o) =>
 Castable Straight from (Identity o) =>
 Castable Opposite from (U_II_I t e a) =>
 Castable Opposite into (U_I_II tt e o) =>
 into a (tt e o) -> from (t a e) o
hj from = he @from
 `compose` component @Straight @into @from @(U_II_I t e `T_TT_I` U_I_II tt e) @Identity
 `compose` wrap @from @((U_II_I t e `T_TT_I` U_I_II tt e) _)
 `compose` fo (wrap @into @(U_I_II tt e _) `compose` from)
 `compose` wrap @from @(U_II_I t e _)

hjj = hj
hjjj = hj
hjjjj = hj
hjjjjj = hj
hjjjjjj = hj
hjjjjjjj = hj
hjjjjjjjj = hj
hjjjjjjjjj = hj

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

he, hee, heee, heeee, heeeee, heeeeee, heeeeeee, heeeeeeee, heeeeeeeee :: forall into e .
 Castable Straight into e =>
 into e (Supertype e)
he = unwrap

hee = he
heee = he
heeee = he
heeeee = he
heeeeee = he
heeeeeee = he
heeeeeeee = he
heeeeeeeee = he

he'he, hee'he, heee'he, heeee'he, heeeee'he, heeeeee'he, heeeeeee'he, heeeeeeee'he, heeeeeeeee'he
 :: forall into e .
 Precategory into =>
 Castable Straight into e =>
 Castable Straight into (Supertype e) =>
 into e (Supertype (Supertype e))
he'he = unwrap `compose` unwrap

hee'he = he'he
heee'he = he'he
heeee'he = he'he
heeeee'he = he'he
heeeeee'he = he'he
heeeeeee'he = he'he
heeeeeeee'he = he'he
heeeeeeeee'he = he'he

he'he'he, hee'he'he, heee'he'he, heeee'he'he, heeeee'he'he, heeeeee'he'he, heeeeeee'he'he, heeeeeeee'he'he, heeeeeeeee'he'he :: forall into e .
 Precategory into =>
 Castable Straight into e =>
 Castable Straight into (Supertype e) =>
 Castable Straight into (Supertype (Supertype e)) =>
 into e (Supertype (Supertype (Supertype e)))
he'he'he = unwrap `compose` unwrap `compose` unwrap

hee'he'he = he'he'he
heee'he'he = he'he'he
heeee'he'he = he'he'he
heeeee'he'he = he'he'he
heeeeee'he'he = he'he'he
heeeeeee'he'he = he'he'he
heeeeeeee'he'he = he'he'he
heeeeeeeee'he'he = he'he'he


he'ya :: forall from into t a o e .
 Precategory into =>
 (Supertype e ~ t a) =>
 Contravariant Yoneda from into t =>
 Wrapper into (U_II_I from a o) =>
 Wrapper (->) e =>
 e -> into (from o a) (t o)
he'ya = ya @from @into `compose` unwrap

he'yo :: forall from into t a o e .
 Precategory into =>
 (Supertype e ~ t a) =>
 Covariant Yoneda from into t =>
 Wrapper into (U_I_II from a o) =>
 Wrapper (->) e =>
 e -> into (from a o) (t o)
he'yo = yo @from @into `compose` unwrap

he'yu :: forall into t a o e .
 Precategory into =>
 Covariant Yoneda into into t =>
 Mapping Straight Straight (->) (->) t t =>
 Mapping Straight Straight into into Identity (U_I_II into a) =>
 Wrapper into (U_I_II into a o) =>
 Wrapper (->) (into () o) =>
 Wrapper into (into () o) =>
 Castable Opposite into (U_I_II into () o) =>
 Wrapper into (Identity o) =>
 Wrapper (->) e =>
 t a -> into o (t o)
he'yu = yu @into

-- TODO: define `j'_j'_j'`, `j'_j'_j'_j'`, `j'_j'_j'_j'_j',

rj :: forall from into t tt a o .
 Adjoint Functor from into t tt =>
 Castable Opposite from ((T_TT_I t tt) o) =>
 Castable Straight from (Identity o) =>
 into a (tt o) -> from (t a) o
rj from = he @from @(Identity _)
 `compose` component @Straight @into @from @(t `T_TT_I` tt) @Identity
 `compose` wrap @from @((t `T_TT_I` tt) _)
 `compose` fo @into @from from

-- rij :: forall from into t tt e ee a o .
 -- Adjoint Functor from into (U_I_II t ee) (U_I_II tt e) =>
 -- Castable Opposite from ((T_TT_I (U_I_II t ee) (U_I_II tt e)) o) =>
 -- Castable Straight from (Identity o) =>
 -- Castable Opposite from (U_I_II t ee a) =>
 -- Castable Opposite into (U_I_II tt e o) =>
 -- into a (tt e o) -> from (t ee a) o
-- rij from = _' @from
 -- `compose` component @Straight @into @from @(U_I_II t ee `T_TT_I` U_I_II tt e) @Identity
 -- `compose` wrap @from @((U_I_II t ee `T_TT_I` U_I_II tt e) _)
 -- `compose` fo (wrap @into @(U_I_II tt e _) `compose` from)
 -- `compose` wrap @from @(U_I_II t ee _)

-- lo, loo, looo, loooo, looooo, loooooo, looooooo, loooooooo :: forall into a o oo .
--  Limit Straight into into =>
--  Covariant Functor into into (U_I_II (Product into) o) =>
--  Covariant Functor into into (U_II_I (Product into) (Product into a a)) =>
--  (forall e ee . Wrapper into (U_I_II (Product into) e ee)) =>
--  (forall e ee . Wrapper into (U_II_I (Product into) e ee)) =>
--  (forall e . Wrapper into (Both (Product into) e)) =>
--  (forall e . Wrapper into (Identity e)) =>
--  into a o -> into a oo -> into a (Product into o oo)
-- lo from_left from_right =
--  _i (map @Straight @Straight (wrapped (right @Straight from_right))) `compose`
--  i_ (map @Straight @Straight (wrapped (left @Straight from_left))) `compose`
--  wrapped (map @Straight @Straight @into @into @Identity @(Both (Product into)) identity) `compose`
--  wrapped (map @Straight @Straight @into @into @Identity @(Both (Product into)) identity)

-- loo = lo
-- looo = lo
-- loooo = lo
-- looooo = lo
-- loooooo = lo
-- looooooo = lo
-- loooooooo = lo

-- lo'yp, loo'yp, looo'yp, loooo'yp, looooo'yp, loooooo'yp, looooooo'yp, loooooooo'yp
 -- :: forall t a aa o oo .
 -- Mapping Straight Straight (->) (->) (Day Straight (->) (Product (->)) (Product (->)) t t o oo) t =>
 -- Arrow a (t o) -> Arrow a (t oo) -> Arrow a (t (Product Arrow o oo))
-- lo'yp from_left from_right = yp `compose` lo from_left from_right

-- loo'yp = lo'yp
-- looo'yp = lo'yp
-- loooo'yp = lo'yp
-- looooo'yp = lo'yp
-- loooooo'yp = lo'yp
-- looooooo'yp = lo'yp
-- loooooooo'yp = lo'yp

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

-- into a o -> into a oo -> into a (Product into o oo)

-- cnz :: forall into e a aa o oo .
 -- Cone Straight into into (Object Straight into) =>
 -- Functor Straight into into (That (Product into) o) =>
 -- Functor Straight into into (That (Product into) aa) =>
 -- Functor Straight into into (This (Product into) aa) =>
 -- Wrapper into (That (Product into) o aa) =>
 -- Wrapper into (That (Product into) o oo) =>
 -- Wrapper into (This (Product into) aa o) =>
 -- Wrapper into (This (Product into) aa a) =>
 -- Castable Straight into e =>
 -- (Supertype e ~ (Product into a aa)) =>
 -- into a o -> into aa oo -> into e (Product into o oo)
-- cnz from_left from_right = fio from_right `compose` foi from_left `compose` _' @into

-- TODO: try to generalize
cn'yp, yi'cn'yp :: forall t a aa o oo .
 Mapping Straight Straight (->) (->) (Day Straight (->) (Product (->)) (Product (->)) t t o oo) t =>
 Arrow a (t o) -> Arrow aa (t oo) -> Arrow (Product (->) a aa) (t (Product Arrow o oo))
cn'yp from_left from_right = yp `compose` cn from_left from_right

yi'cn'yp = cn'yp

-- TODO: try to generalize
-- cnz'yp, yi'cnz'yp :: forall e t a aa o oo .
--  Mapping Straight Straight (->) (->) (Day Straight (->) (Product (->)) (Product (->)) t t o oo) t =>
--  Castable Straight (->) e =>
--  (Supertype e ~ Product (->) a aa) =>
--  Arrow a (t o) -> Arrow aa (t oo) -> Arrow e (t (Product Arrow o oo))
-- cnz'yp from_left from_right = yp `compose` cn from_left from_right `compose` he

-- yi'cnz'yp = cnz'yp

-- TODO: try to generalize
-- lu, luu, luuu, luuuu, luuuuu, luuuuuu, luuuuuuu, luuuuuuuu :: forall o oo .
--  Limit Straight (->) (->) =>
--  Covariant Functor (->) (->) (That (Product (->)) o) =>
--  Covariant Functor (->) (->) (This (Product (->)) (Product (->) () ())) =>
--  Castable Straight (->) (Both (Product (->)) (Product (->) () ())) =>
--  Castable Straight (->) (That (Product (->)) o oo) =>
--  Castable Opposite (->) (This (Product (->)) () ()) =>
--  Castable Opposite (->) (That (Product (->)) () ()) =>
--  Castable Straight (->) (Both (Product (->)) ()) =>
--  Castable Straight (->) (This (Product (->)) (Product (->) () ()) o) =>
--  Castable Opposite (->) (This (Product (->)) (Product (->) () ()) (Product (->) () ())) =>
--  Wrapper (->) (That (Product (->)) o (Product (->) () ())) =>
--  (forall e . Wrapper (->) (Identity e)) =>
--  Castable Opposite (->) (U_1_I (->) () o) =>
--  Castable Opposite (->) (U_1_I (->) () oo) =>
--  Castable Straight (->) (U_1_I (->) () (Product (->) o oo)) =>
--  Supertype (U_1_I (->) () o) ->
--  Supertype (U_1_I (->) () oo) ->
--  Supertype (U_1_I (->) () (Product (->) o oo))
-- lu from_left from_right = -- he /
--  -- _i (map @Straight @Straight (wrapped (right @Straight (wrap @_ @(U_1_I (->) () oo) from_right)))) `compose`
--  -- i_ (map @Straight @Straight (wrapped (left @Straight (wrap @_ @(U_1_I (->) () o) from_left)))) `compose`
--  -- wrapped (map @Straight @Straight @(->) @(->) @Identity @(Both (Product (->))) identity) `compose`
--  -- wrapped (map @Straight @Straight @(->) @(->) @Identity @(Both (Product (->))) identity)

--  _i (map @U_1_I @Straight (wrapped (right @Straight from_right))) `compose`
--  i_ (map @U_1_I @Straight (wrapped (left @Straight from_left))) `compose`
 -- wrapped (map @U_1_I @Straight @(->) @(->) @Identity @(Both (Product (->))) identity) `compose`
 -- wrapped (map @U_1_I @Straight @(->) @(->) @Identity @(Both (Product (->))) identity)

lu, luu, luuu, luuuu, luuuuu, luuuuuu, luuuuuuu, luuuuuuuu :: forall o oo .
 Limit Straight (->) (->) =>
 Mapping Straight Straight (->) (->) Identity (U_I_I (Product (->))) =>
 Covariant Yoneda (->) (->) (U_I_II (Product (->)) o) =>
 Covariant Yoneda (->) (->) (U_II_I (Product (->)) ()) =>
 Wrapper (->) (U_I_I (Product (->)) ()) =>
 Wrapper (->) (Identity ()) =>
 o -> oo -> Product (->) o oo
lu l r = wrapped (map @Straight @Straight @(->) @(->) @Identity @(U_I_I (Product (->))) identity) () `yui` l `yiu` r

luu = lu
luuu = lu
luuuu = lu
luuuuu = lu
luuuuuu = lu
luuuuuuu = lu
luuuuuuuu = lu

la, laa, laaa, laaaa, laaaaa, laaaaaa, laaaaaaa, laaaaaaaa :: forall from i o oo .
 Category from =>
 Limit Opposite from from =>
 Covariant Functor from from (That (Sum from) o) =>
 Covariant Functor from from (This (Sum from) (Sum from i i)) =>
 (forall ee eee . Wrapper from (That (Sum from) ee eee)) =>
 (forall ee eee . Wrapper from (This (Sum from) ee eee)) =>
 (forall ee . Wrapper from (Both (Sum from) ee)) =>
 (forall ee . Wrapper from (Identity ee)) =>
 from o i -> from oo i -> from (Sum from o oo) i
la from_left from_right =
 wrapped (map @Opposite @Opposite @from @from @Identity @(Both (Sum from)) identity) `compose`
 wrapped (map @Opposite @Opposite @from @from @Identity @(Both (Sum from)) identity) `compose`
 i_ (map @Straight @Straight (wrapped (left @Opposite from_left))) `compose`
 _i (map @Straight @Straight (wrapped (right @Opposite from_right)))

laa = la
laaa = la
laaaa = la
laaaaa = la
laaaaaa = la
laaaaaaa = la
laaaaaaaa = la

-- `yp`: u (t e) (t ee) -> t (uu e ee)
-- `hs`: from o i -> from oo i -> from (o `ML` oo) i
-- `lo`: into a o -> into a oo -> into a (o `LM` oo)
--     : u (from o i) (from oo i) -> from (uu o oo) i

-- TODO: to test
rwr'hs :: forall from into r o a aa .
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
rwr'hs from_left from_right = rwr /
 wrapped (map @Opposite @Opposite @from @into @Identity @(Both (Sum into)) identity) `compose`
 wrapped (map @Opposite @Opposite @from @into @Identity @(Both (Sum into)) identity) `compose`
 i_ (map @Straight @Straight (wrapped (left @Opposite from_left))) `compose`
 _i (map @Straight @Straight (wrapped (right @Opposite from_right)))

yp :: forall u e ee t .
 Mapping Straight Straight (->) (->) (Day Straight (->) u LM t t e ee) t =>
 u (t e) (t ee) -> t (e `LM` ee)
yp = day @Straight @(->) @t @u @LM identity identity

ys :: forall u e ee t .
 Mapping Straight Straight (->) (->) (Day Straight (->) u ML t t e ee) t =>
 u (t e) (t ee) -> t (e `ML` ee)
ys = day @Straight @(->) @t @u @ML identity identity

dw :: forall u e ee t .
 Mapping Straight Straight (->) (->)
 (Day Straight (->) u MLM t t e ee) t =>
 u (t e) (t ee) -> t (ML e ee `ML` LM e ee)
dw = day @Straight @(->) @t @u @MLM identity he

yp'yp :: forall u e ee t tt .
 Mapping Straight Straight (->) (->)
 (Day Straight (->) u LM t t (tt e) (tt ee)) t =>
 Mapping Straight Straight (->) (->)
 (Day Straight (->) LM LM tt tt e ee) tt =>
 u (t (tt e)) (t (tt ee)) -> t (tt (e `LM` ee))
yp'yp = day @Straight @(->) @t @u @LM identity
 (day @Straight @(->) @tt @LM @LM identity identity)

-- w'rw :: forall into a o .
 -- Precategory into =>
 -- Castable Opposite into o =>
 -- Castable Straight into a =>
 -- into (Supertype a) (Supertype o) -> into a o
-- w'rw into = wrap @into `compose` into `compose` he @into

-- rw'w :: forall into a o .
 -- Precategory into =>
 -- Castable Opposite into a =>
 -- Castable Straight into o =>
 -- into a o -> into (Supertype a) (Supertype o)
-- rw'w into = _' @into `compose` into `compose` wrap @into

-- yi__, yii__, yiii__, yiiii__, yiiiii__ :: forall into a .
 -- Precategory into =>
 -- Castable Straight into a =>
 -- Castable Straight into (Supertype a) =>
 -- into a (Supertype (Supertype a))
-- yi__ = _' @into `compose` _' @into

-- yii__ = yi__
-- yiii__ = yi__
-- yiiii__ = yi__
-- yiiiii__ = yi__

-- yi___, yii___, yiii___, yiiii___, yiiiii___ :: forall into a .
 -- Precategory into =>
 -- Castable Straight into a =>
 -- Castable Straight into (Supertype a) =>
 -- Castable Straight into (Supertype (Supertype a)) =>
 -- into a (Supertype (Supertype (Supertype a)))
-- yi___ = _' @into `compose` _' @into `compose` _' @into

-- yii___ = yi___
-- yiii___ = yi___
-- yiiii___ = yi___
-- yiiiii___ = yi___

-- TODO: it's wrong, we need to rewrite it
-- he'he'he'ho :: forall a e o oo .
--  Castable Straight (->) a =>
--  Castable Straight (->) (Supertype a) =>
--  Castable Straight (->) (Supertype (Supertype a)) =>
--  ((e `ARR` o) ~ Supertype (Supertype (Supertype a))) =>
--  a `ARR` e `ARR` (o `ARR` oo) `ARR` oo
-- he'he'he'ho x e f = f (_' (_' (_' x)) e)

-- TODO: define `rw'o`
-- TODO: define `rw'rw'o`
-- TODO: define `rw'ha`
-- TODO: define `rw'rw'ha`
-- TODO: define `rw'rw'rw'ha`

ho'yok, hoo'yok, hooo'yok, hoooo'yok, hooooo'yok, hoooooo'yok, hooooooo'yok, hoooooooo'yok, hooooooooo'yok :: forall from u t tt a o e .
 Covariant Endo Semi Functor from tt =>
 Covariant Endo Semi Functor from t =>
 Mapping Straight Straight from from (T_TT_I t tt) t =>
 Covariant Yoneda from (->) (Straight u e) =>
 (forall ee . Wrapper from (T_TT_I t tt ee)) =>
 u e (t a) -> from a (tt o) -> u e (t o)
ho'yok x = fai fok (ho @from x)

hoo'yok = ho'yok
hooo'yok = ho'yok
hoooo'yok = ho'yok
hooooo'yok = ho'yok
hoooooo'yok = ho'yok
hooooooo'yok = ho'yok
hoooooooo'yok = ho'yok
hooooooooo'yok = ho'yok

ho'yuk, hoo'yuk, hooo'yuk, hoooo'yuk, hooooo'yuk, hoooooo'yuk, hooooooo'yuk, hoooooooo'yuk, hooooooooo'yuk :: forall from t tt a o e .
 Covariant Endo Semi Functor from tt =>
 Covariant Endo Semi Functor from t =>
 Constant Semi Functor from from t =>
 Component Natural from from (T_TT_I t tt) t =>
 Component Natural from (->) Identity (U_I_II from a) =>
 Covariant Yoneda from (->) (Straight from e) =>
 Wrapper from (T_TT_I t t o) =>
 Wrapper from (Identity (tt o)) =>
 Wrapper (->) (U_1_I from a (tt o)) =>
 (forall ee . Wrapper from (T_TT_I t tt ee)) =>
 from e (t a) -> tt o -> from e (t o)
ho'yuk x = fai (fuk @from @t @tt) (ho @from x)
hoo'yuk x = fai (fuk @from @t @tt) (ho @from x)
hooo'yuk x = fai (fuk @from @t @tt) (ho @from x)
hoooo'yuk x = fai (fuk @from @t @tt) (ho @from x)
hooooo'yuk x = fai (fuk @from @t @tt) (ho @from x)
hoooooo'yuk x = fai (fuk @from @t @tt) (ho @from x)
hooooooo'yuk x = fai (fuk @from @t @tt) (ho @from x)
hoooooooo'yuk x = fai (fuk @from @t @tt) (ho @from x)
hooooooooo'yuk x = fai (fuk @from @t @tt) (ho @from x)

ha'yok :: forall from u t tt a o e .
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
ha'yok x = fai fok (ha @from x)

-- TODO: try to gereralize
yok'ha, li'yok'ha :: forall from t tt a o e .
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
 Mapping Straight Straight from from (T_TT_I t tt) t =>
 (forall ee . Wrapper from ((t `T_TT_I` tt) ee)) =>
 Wrapper from (U_II_I from o a) =>
 Wrapper from (U_II_I from e (tt o)) =>
 Wrapper from (U_I_II from e (tt o)) =>
 Wrapper from (U_II_I from o e) =>
 Wrapper from (U_I_II from e a) =>
 t e -> from a (tt o) -> from (from e a) (t o)
yok'ha x f = yok x `compose` fio f

li'yok'ha = yok'ha

-- yok'hu :: forall from t tt a o e .
  -- Precategory from =>
  -- Covariant Yoneda from from t =>
  -- Mapping Straight Straight from from (U_I_II from e) (U_I_II from e) =>
  -- Constant Semi Functor from from (U_I_II from e) =>
  -- Covariant Semi Functor from from t =>
  -- Covariant Semi Functor (->) from t =>
  -- Covariant Semi Functor from (->) tt =>
  -- Covariant Semi Functor (->) from tt =>
  -- Mapping Straight Straight (->) from (T_TT_I t tt) t =>
  -- (forall ee . Wrapper from ((t `T_TT_I` tt) ee)) =>
  -- Castable Opposite from (T_TT_I t tt o) =>
  -- Wrapper from (U_I_II from e (tt o)) =>
  -- Castable Opposite from (U_I_II from e a) =>
  -- Castable Opposite from (U_1_I from a (tt o)) =>
  -- Castable Opposite (->) (U_1_I from a (tt o)) =>
  -- t e -> Supertype (U_1_I from a (tt o)) -> from (from e a) (t o)
-- yok'hu x f = yok @_ @_ @tt x `compose` fiu @from f

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

ho'yokl, hoo'yokl, hooo'yokl, hoooo'yokl, hooooo'yokl, hoooooo'yokl, hooooooo'yokl, hoooooooo'yokl, hooooooooo'yokl :: forall from u t tt a o e .
 Unlabelable from tt =>
 Covariant Semi Functor from (->) (Straight u e) =>
 Covariant Endo Semi Functor from tt =>
 Covariant Endo Semi Functor from t =>
 Mapping Straight Straight from from (T_TT_I t tt) (TT_T_I t tt) =>
 Covariant Yoneda from (->) (Straight u e) =>
 (forall ee . Wrapper from (T_TT_I t tt ee)) =>
 (forall ee . Wrapper from (TT_T_I t tt ee)) =>
 -- Wrapper from (Identity e) =>
 u e (t a) -> from a (tt o) -> u e (Unlabeled tt (t o))
ho'yokl x = fio @from unlabel `compose` fai fokl (ho @from x)

hoo'yokl = ho'yokl
hooo'yokl = ho'yokl
hoooo'yokl = ho'yokl
hooooo'yokl = ho'yokl
hoooooo'yokl = ho'yokl
hooooooo'yokl = ho'yokl
hoooooooo'yokl = ho'yokl
hooooooooo'yokl = ho'yokl

-- ha'yuk :: forall from t tt a o e .
--  Covariant Functor (->) (->) tt =>
--  Covariant Functor from from t =>
--  Covariant Functor from from tt =>
--  Contravariant Yoneda from (->) (U_II_I from (tt o)) =>
--  Mapping Straight Straight from from (T_TT_I tt t) tt =>
--  Constant Semi Functor from from tt =>
--  Castable Opposite from (T_TT_I tt t o) =>
--  (forall ee . Wrapper from (T_TT_I tt t ee)) =>
--  Castable Opposite from (T_TT_I tt tt o) =>
--  Castable Opposite (->) (U_1_I from a (t o)) =>
--  Supertype (U_1_I from a (t o)) -> from e (tt a) -> from e (tt o)
-- ha'yuk = ha `compose` fuk @from @tt @t

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

-- TODO: generalize
lu'yp, luu'yp, luuu'yp, luuuu'yp, luuuuu'yp, luuuuuu'yp, luuuuuuu'yp, luuuuuuuu'yp :: forall o oo t .
 Covariant Monoidal Functor (->) LM LM t =>
 Covariant Yoneda (->) (->) (U_I_II (Product (->)) (t o)) =>
 Covariant Yoneda (->) (->) (U_II_I (Product (->)) ()) =>
 t o -> t oo -> t (o `LM` oo)
lu'yp from_left from_right = yp (lu from_left from_right)

luu'yp = lu'yp
luuu'yp = lu'yp
luuuu'yp = lu'yp
luuuuu'yp = lu'yp
luuuuuu'yp = lu'yp
luuuuuuu'yp = lu'yp
luuuuuuuu'yp = lu'yp

lu'ys, luu'ys, luuu'ys, luuuu'ys, luuuuu'ys, luuuuuu'ys, luuuuuuu'ys, luuuuuuuu'ys
 :: forall o oo t .
 Covariant Monoidal Functor (->) LM ML t =>
 Covariant Yoneda (->) (->) (U_I_II (Product (->)) (t o)) =>
 Covariant Yoneda (->) (->) (U_II_I (Product (->)) ()) =>
 t o -> t oo -> t (o `ML` oo)
lu'ys from_left from_right = ys (lu from_left from_right)

luu'ys = lu'ys
luuu'ys = lu'ys
luuuu'ys = lu'ys
luuuuu'ys = lu'ys
luuuuuu'ys = lu'ys
luuuuuuu'ys = lu'ys
luuuuuuuu'ys = lu'ys

lu'yp'yp :: forall o oo t tt .
 Covariant Monoidal Functor (->) LM LM t =>
 Covariant Monoidal Functor (->) LM LM tt =>
 -- Mapping Straight Straight into (->) Identity (U_I_I (Product into)) =>
 Covariant Yoneda (->) (->) (U_I_II (Product (->)) (t (tt o))) =>
 Covariant Yoneda (->) (->) (U_II_I (Product (->)) ()) =>
 t (tt o) -> t (tt oo) -> t (tt (o `LM` oo))
lu'yp'yp from_left from_right = yp'yp @LM (lu from_left from_right)

-- TODO: generalize
yp'yo :: forall from e ee r t .
 Covariant Monoidal Functor from LM LM t =>
 t e `LM` t ee -> from (e `LM` ee) r -> t r
yp'yo x f = day @Straight @from @t @LM @LM identity f x

-- TODO: generalize
yp'yok :: forall e ee from into t tt o .
 Covariant Monoidal Functor (->) LM LM t =>
 Covariant Endo Semi Functor into tt =>
 Covariant Endo Semi Functor into t =>
 Covariant Yoneda from into t =>
 Component Natural into into (T_TT_I t tt) t =>
 Castable Opposite into (Straight from (e `LM` ee) (tt o)) =>
 (forall eee . Wrapper into (T_TT_I t tt eee)) =>
 t e `LM` t ee -> into (from (e `LM` ee) (tt o)) (t o)
yp'yok = yok @from @into `compose` yp

-- TODO: generalize
yp'yokl :: forall e ee from into t tt o .
 Unlabelable into tt =>
 Component Natural from into (T_TT_I t tt) (TT_T_I t tt) =>
 Covariant Monoidal Functor (->) LM LM t =>
 Covariant Yoneda from into t =>
 Castable Opposite into (Straight from (e `LM` ee) (tt o)) =>
 Castable Opposite into (T_TT_I t tt o) =>
 Castable Straight into (TT_T_I t tt o) =>
 t e `LM` t ee -> into (from (e `LM` ee) (tt o)) (Unlabeled tt (t o))
yp'yokl = yokl @from @into `compose` yp

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
 `compose` wrap @into @((f `T_TT_I` g) e)

-- TODO: generalize
yp'yp'jt :: forall e ee t tt .
 Component Natural (->) (->) (t `T_TT_I` tt) (t `JT` tt) =>
 Covariant Monoidal Functor (->) LM LM t =>
 Covariant Monoidal Functor (->) LM LM tt =>
 t (tt e) `LM` t (tt ee) -> (t `JT` tt) (e `LM` ee)
yp'yp'jt = jt `compose` day @Straight @(->) @t @LM @LM identity
 (day @Straight @(->) @tt @LM @LM identity identity)

-- TODO: generalize
-- yp'yp'jt'yok :: forall from into e ee t tt ttt o .
 -- Covariant Yoneda from into t =>
 -- Covariant Semi Functor into into ttt =>
 -- Covariant Yoneda from into (t `JT` tt) =>
 -- Component Natural (->) (->) (t `T_TT_I` tt) (t `JT` tt) =>
 -- Component Natural (->) into (T_TT_I (t `JT` tt) ttt) (t `JT` tt) =>
 -- Covariant Monoidal Functor (->) LM LM t =>
 -- Covariant Monoidal Functor (->) LM LM tt =>
 -- Castable Opposite into (Straight from (e `LM` ee) (ttt o)) =>
 -- (forall e . Wrapper into (T_TT_I (JT t tt) ttt e)) =>
 -- t (tt e) `LM` t (tt ee) -> into (from (e `LM` ee) (ttt o)) ((t `JT` tt) o)
-- yp'yp'jt'yok = yok @from @into `compose` yp'yp'jt

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
rwr'yoi x = wrap @into `compose` yoi (unwrap x)

-- -- TODO: generalize
-- o_rwr_''yoi :: forall from into w a o u e ee .
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
--  Constant Semi Functor into into (U_II_I u o) (U_II_I u o) =>
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
--  Constant Semi Functor (->) (->) (U_II_I u o) (U_II_I u o) =>
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
 (rj @(->) @(->) (wrap @_ @(That _ _ _)) `compose` wrap @_ @(That _ _ _))
 `compose` lj @(->) @(->) @(That LM (t a)) @(That into _)
 (monoidal_ @Straight @into @(->) @t @LM @LM identity (wrap identity)
 `compose` unwrap @(->) @(That LM (t a) (t (into a o))))

-- cc :: forall t e ee .
--  Adjoint Functor (->) (->) (That LM (t e `LM` t ee)) (That (->) (t e `LM` t ee)) =>
--  Monoidal Straight Functor (->) LM LM t =>
--  t e -> t ee -> t (e `LM` ee)
-- cc e ee = monoidal_
--  @Straight @(->) @(->) @t @LM @LM identity
--  (wrap identity)
--  (e `lu` ee)
