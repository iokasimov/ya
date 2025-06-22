{-# LANGUAGE AllowAmbiguousTypes #-}
module Ya.Operators.Handcraft where

import Ya.Algebra.Abstract
import Ya.Algebra.Definition
import Ya.Algebra.Effectful
import Ya.Algebra.Instances ()

import Ya.Operators.Mappings

infixl 9 `ho`, `ho'yioi`, `ho'yu`, `ho'yui`, `ho'yok`, `ho'yuk`, `ho'yokl`, `ho'yokl'yokl`, `ho'yokl'yukl`, `ho'yukl`
 , `ho'he`
 , `ho'he'he`
 , `ho'he'he'he`
 , `ho'he'he'hv`
 , `ho'he'he'he'he`
 , `ho'hd`
 , `ho'hd'hd`
infixl 8 `ho_`, `ho_'yu`, `ho_'yok`, `ho_'yuk`, `ho_'yokl`, `ho_'yokl'yokl`, `ho_'yokl'yukl`, `ho_'yukl`
 , `ho_'he`
 , `ho_'he'he`
 , `ho_'he'he'he`
 , `ho_'he'he'hv`
 , `ho_'he'he'he'he`
infixl 7 `ho__`, `ho__'yu`, `ho__'yok`, `ho__'yuk`, `ho__'yokl`, `ho__'yokl'yokl`, `ho__'yokl'yukl`, `ho__'yukl`
 , `ho__'he`
 , `ho__'he'he`
 , `ho__'he'he'he`
 , `ho__'he'he'hv`
 , `ho__'he'he'he'he`
infixl 6 `ho___`, `ho___'yu`, `ho___'yok`, `ho___'yuk`, `ho___'yokl`, `ho___'yokl'yokl`, `ho___'yokl'yukl`, `ho___'yukl`
 , `ho___'he`
 , `ho___'he'he`
 , `ho___'he'he'he`
 , `ho___'he'he'hv`
 , `ho___'he'he'he'he`
infixl 5 `ho____`, `ho____'yu`, `ho____'yok`, `ho____'yuk`, `ho____'yokl`, `ho____'yokl'yokl`, `ho____'yokl'yukl`, `ho____'yukl`
 , `ho____'he`
 , `ho____'he'he`
 , `ho____'he'he'he`
 , `ho____'he'he'hv`
 , `ho____'he'he'he'he`
infixl 4 `ho_____`, `ho_____'yu`, `ho_____'yok`, `ho_____'yuk`, `ho_____'yokl`, `ho_____'yokl'yokl`, `ho_____'yokl'yukl`, `ho_____'yukl`
 , `ho_____'he`
 , `ho_____'he'he`
 , `ho_____'he'he'he`
 , `ho_____'he'he'hv`
 , `ho_____'he'he'he'he`
infixl 3 `ho______`, `ho______'he`, `ho______'yok`, `ho______'yuk`, `ho______'yokl`, `ho______'yokl'yokl`, `ho______'yokl'yukl`, `ho______'yukl`
infixl 2 `ho_______`, `ho_______'yok`, `ho_______'yuk`, `ho_______'yokl`, `ho_______'yokl'yokl`, `ho_______'yokl'yukl`, `ho_______'yukl`
 , `ho_______'he`
 , `ho_______'he'he`
 , `ho_______'he'he'he`
 , `ho_______'he'he'hv`
 , `ho_______'he'he'he'he`
infixl 1 `ho________`, `ho________'yok`, `ho________'yuk`, `ho________'yokl`, `ho________'yokl'yokl`, `ho________'yokl'yukl`, `ho________'yukl`
 , `ho________'he`
 , `ho________'he'he`
 , `ho________'he'he'he`
 , `ho________'he'he'hv`
 , `ho________'he'he'he'he`
 -- , `ho________'yo`
 -- , `ho________'yoi`

infixl 9 `ha`, `ha'hu`, `ha'yok`, `ha'yuk`, `ha'yokl`, `ha'yukl`
 , `ha'he`
 , `he'ha`
 , `ha'hd`
 , `ha'hd'hd`
infixl 8 `ha_`
 , `ha_'he`
 , `ha_'hu`
 , `ha_'yok`
 , `ha_'yuk`
 , `ha_'yokl`
 , `ha_'yukl`
infixl 7 `ha__`
 , `ha__'he`
 , `ha__'hu`
 , `ha__'yok`
 , `ha__'yuk`
 , `ha__'yokl`
 , `ha__'yukl`
infixl 6 `ha___`
 , `ha___'he`
 , `ha___'hu`
 , `ha___'yok`
 , `ha___'yuk`
 , `ha___'yokl`
 , `ha___'yukl`
infixl 5 `ha____`
 , `ha____'he`
 , `ha____'hu`
 , `ha____'yok`
 , `ha____'yuk`
 , `ha____'yokl`
 , `ha____'yukl`
infixl 4 `ha_____`
 , `ha_____'he`
 , `ha_____'hu`
 , `ha_____'yok`
 , `ha_____'yuk`
 , `ha_____'yokl`
 , `ha_____'yukl`
infixl 3 `ha______`
 , `ha______'he`
 , `ha______'hu`
 , `ha______'yok`
 , `ha______'yuk`
 , `ha______'yokl`
 , `ha______'yukl`
infixl 2 `ha_______`
 , `ha_______'he`
 , `ha_______'hu`
 , `ha_______'yok`
 , `ha_______'yuk`
 , `ha_______'yokl`
 , `ha_______'yukl`
infixl 1 `ha________`
 , `ha________'he`
 , `ha________'hu`
 , `ha________'yok`
 , `ha________'yuk`
 , `ha________'yokl`
 , `ha________'yukl`

infixl 9 `hu`, `hu'he`, `he'hu`
infixl 8 `hu_`, `hu_'he`, `he'hu_`
infixl 7 `hu__`, `hu__'he`, `he'hu__`
infixl 6 `hu___`, `hu___'he`, `he'hu___`
infixl 5 `hu____`, `hu____'he`, `he'hu____`
infixl 4 `hu_____`, `hu_____'he`, `he'hu_____`
infixl 3 `hu______`, `hu______'he`, `he'hu______`
infixl 2 `hu_______`, `hu_______'he`, `he'hu_______`
infixl 1 `hu________`, `hu________'he`, `he'hu________`

infixl 9 `hd`
infixl 8 `hd_`
infixl 7 `hd__`
infixl 6 `hd___`
infixl 5 `hd____`
infixl 4 `hd_____`
infixl 3 `hd______`
infixl 2 `hd_______`
infixl 1 `hd________`

infixl 9 `hj` --, `hj'hj`
infixl 8 `hj_`
infixl 7 `hj__`
infixl 6 `hj___`
infixl 5 `hj____`
infixl 4 `hj_____`
infixl 3 `hj______`
infixl 2 `hj_______`
infixl 1 `hj________`

--, `he'he'ho`, `he'he'he'ho`

infixl 9 `he`, `he'he`, `he'he'he`, `he'he'he'he`, `he'ho`, `he'ho'he`
infixl 8 `he_`, `he_'he`, `he_'he'he`, `he_'he'he'he`, `he_'ho`, `he_'ho'he`
infixl 7 `he__`, `he__'he`, `he__'he'he`, `he__'he'he'he`, `he__'ho`, `he__'ho'he`
infixl 6 `he___`, `he___'he`, `he___'he'he`, `he___'he'he'he`, `he___'ho`, `he___'ho'he`
infixl 5 `he____`, `he____'he`, `he____'he'he`, `he____'he'he'he`, `he____'ho`, `he____'ho'he`
infixl 4 `he_____`, `he_____'he`, `he_____'he'he`, `he_____'he'he'he`, `he_____'ho`, `he_____'ho'he`
infixl 3 `he______`, `he______'he`, `he______'he'he`, `he______'he'he'he`, `he______'ho`, `he______'ho'he`
infixl 2 `he_______`, `he_______'he`, `he_______'he'he`, `he_______'he'he'he`, `he_______'ho`, `he_______'ho'he`
infixl 1 `he________`, `he________'he`, `he________'he'he`, `he________'he'he'he`, `he________'ho`, `he________'ho'he`

infixl 9 `hv`, `hv'he`,`hv'he'he`, `he'hv`, `he'he'hv`
infixl 8 `hv_`, `hv_'he`,`hv_'he'he`, `he'hv_`, `he'he'hv_`
infixl 7 `hv__`, `hv__'he`,`hv__'he'he`, `he'hv__`, `he'he'hv__`
infixl 6 `hv___`, `hv___'he`,`hv___'he'he`, `he'hv___`, `he'he'hv___`
infixl 5 `hv____`, `hv____'he`,`hv____'he'he`, `he'hv____`, `he'he'hv____`
infixl 4 `hv_____`, `hv_____'he`,`hv_____'he'he`, `he'hv_____`, `he'he'hv_____`
infixl 3 `hv______`, `hv______'he`,`hv______'he'he`, `he'hv______`, `he'he'hv______`
infixl 2 `hv_______`, `hv_______'he`,`hv_______'he'he`, `he'hv_______`, `he'he'hv_______`
infixl 1 `hv________`, `hv________'he`,`hv________'he'he`, `he'hv________`, `he'he'hv________`

infixl 8 `lo`, `lo'lu`, `lo'yp`, `lo'ys`, `lo'ys'la`, `lu'ys'la`
infixl 7 `lo_`, `lo_'yp`, `lo_'ys`, `lo_'ys'la`, `lu_'ys'la`
infixl 6 `lo__`, `lo__'yp`, `lo__'ys`, `lo__'ys'la`, `lu__'ys'la`
infixl 5 `lo___`, `lo___'yp`, `lo___'ys`, `lo___'ys'la`, `lu___'ys'la`
infixl 4 `lo____`, `lo____'yp`, `lo____'ys`, `lo____'ys'la`, `lu____'ys'la`
infixl 3 `lo_____`, `lo_____'yp`, `lo_____'ys`, `lo_____'ys'la`, `lu_____'ys'la`
infixl 2 `lo______`, `lo______'yp`, `lo______'ys`, `lo______'ys'la`, `lu______'ys'la`
infixl 1 `lo_______`, `lo_______'yp`, `lo_______'ys`, `lo_______'ys'la`, `lu_______'ys'la`

infixl 8 `la`
infixl 7 `la_`
infixl 6 `la__`
infixl 5 `la___`
infixl 4 `la____`
infixl 3 `la_____`
infixl 2 `la______`
infixl 1 `la_______`

infixl 8 `lu`, `lu'yp`, `lu'yp'yo'q`, `lu'ys`, `lu'yp'yp`, `lu'ysp`, `lu'q`, `lu's`
infixl 7 `lu_`, `lu_'yp`, `lu_'yp'yo'q`, `lu_'ys`, `lu_'ysp`, `lu_'q`, `lu_'s`
infixl 6 `lu__`, `lu__'yp`, `lu__'yp'yo'q`, `lu__'ys`, `lu__'ysp`, `lu__'q`, `lu__'s`
infixl 5 `lu___`, `lu___'yp`, `lu___'yp'yo'q`, `lu___'ys`, `lu___'ysp`, `lu___'q`, `lu___'s`
infixl 4 `lu____`, `lu____'yp`, `lu____'yp'yo'q`, `lu____'ys`, `lu____'ysp`, `lu____'q`, `lu____'s`
infixl 3 `lu_____`, `lu_____'yp`, `lu_____'yp'yo'q`, `lu_____'ys`, `lu_____'ysp`, `lu_____'q`, `lu_____'s`
infixl 2 `lu______`, `lu______'yp`, `lu______'yp'yo'q`, `lu______'ys`, `lu______'ysp`, `lu______'q`, `lu______'s`
infixl 1 `lu_______`, `lu_______'yp`, `lu_______'yp'yo'q`, `lu_______'ys`, `lu_______'ysp`, `lu_______'q`, `lu_______'s`

infixl 8 `lv`
infixl 7 `lv_`
infixl 6 `lv__`
infixl 5 `lv___`
infixl 4 `lv____`
infixl 3 `lv_____`
infixl 2 `lv______`
infixl 1 `lv_______`

infixl 8 `li`, `li'yu`, `li'yok` --, `li'yok'yokl`, `li'yokl`
infixl 7 `li_`, `li_'yok`
infixl 6 `li__`, `li__'yok`
infixl 5 `li___`, `li___'yok`
infixl 4 `li____`, `li____'yok`
infixl 3 `li_____`, `li_____'yok`
infixl 2 `li______`, `li______'yok`
infixl 1 `li_______`, `li_______'yok`

infixl 8 `yi`
infixl 7 `yi_`
infixl 6 `yi__`
infixl 5 `yi___`
infixl 4 `yi____`
infixl 3 `yi_____`
infixl 2 `yi______`
infixl 1 `yi_______`

infixl 8 `yo`, `yo'yp`, `yo'yok` --, `yo'hj`
infixl 7 `yo_`
infixl 6 `yo__`
infixl 5 `yo___`
infixl 4 `yo____`
infixl 3 `yo_____`
infixl 2 `yo______`
infixl 1 `yo_______`

infixl 7 `yok`, `yok'yokl`, `yok'yukl`
infixl 6 `yok_`, `yok_'yokl`, `yok_'yukl`
infixl 5 `yok__`, `yok__'yokl`, `yok__'yukl`
infixl 4 `yok___`, `yok___'yokl`, `yok___'yukl`
infixl 3 `yok____`, `yok____'yokl`, `yok____'yukl`
infixl 2 `yok_____`, `yok_____'yokl`, `yok_____'yukl`
infixl 1 `yok______`, `yok______'yokl`, `yok______'yukl`

infixl 7 `kyo`

infixl 6 `yiok`

infixl 7 `yuk`
infixl 6 `yuk_`
infixl 5 `yuk__`
infixl 4 `yuk___`
infixl 3 `yuk____`
infixl 2 `yuk_____`
infixl 1 `yuk______`

infixl 6 `yokl`, `yokl'yokl`
infixl 5 `yokl_`
infixl 4 `yokl__`
infixl 3 `yokl___`
infixl 2 `yokl____`
infixl 1 `yokl_____`

infixl 6 `yukl`
infixl 5 `yukl_`
infixl 4 `yukl__`
infixl 3 `yukl___`
infixl 2 `yukl____`
infixl 1 `yukl_____`

infixl 8 `ya`

infixl 8 `yu`
infixl 7 `yu_`
infixl 6 `yu__`
infixl 5 `yu___`
infixl 4 `yu____`
infixl 3 `yu_____`
infixl 2 `yu______`
infixl 1 `yu_______`

infixl 8 `yp`, `yp'yo`, `yp'yo'hd`, `yp'yp`, `yp'yp'yo`, `yp'ys`, `yp'yok`, `yp'yokl` --, `yp'yp'jt`, `yp'yp'jt'yok`
infixl 7 `yp_'yo`-- , `yip`, `yip'yo`, `yip'yp`, `yip'yip`, `yip'yis`

infixl 8 `ys`, `ys'yo`
-- infixl 7 `yis`

infixl 7 `ysp`

infixl 7 `yoi`

infixl 7 `yai`, `yai'yukl`, `yai'ydi`, `yai'ydi'ydi`, `yai'yij`

infixl 7 `yui` --, `yui'he`

infixl 7 `yio`, `yio'yokl'yokl`, `yio'yokl'yukl`, `yio'yukl`, `yio'yp`, `yio'yij`, `yio'ydi`, `yio'ydi'ydi`, `yio'yij'yij`

infixl 7 `yiu`, `yiu'he`, `he'yiu`

infixl 7 `yvi`, `yvi'he`, `he'yvi`, `he'he'yvi`

infixl 8 `yd`, `yj`

infixl 7 `ydi`, `yij`, `ydi'ydi`

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

infixl 9 `q`
infixl 8 `q_`
infixl 7 `q__`
infixl 6 `q___`
infixl 5 `q____`
infixl 4 `q_____`
infixl 3 `q______`
infixl 2 `q_______`
infixl 1 `q________`

li, li_, li__, li___, li____, li_____, li______, li_______
 :: Category into => into e e
li = identity

li_ = li
li__ = li
li___ = li
li____ = li
li_____ = li
li______ = li
li_______ = li

-- TODO: redefine `ho`/`ha`/`hu`/`hv` and compositions with those as aliases

yi, yi_, yi__, yi___, yi____, yi_____, yi______, yi_______
 :: forall from into a o .
 Precategory into =>
 Covariant Yoneda Functor from into I =>
 Elicitable T'II'I into (T'I'II from a o) =>
 Elicitable T'I'II into (I o) =>
 a -> into (from a o) o
yi x = unwrap `compose` yoneda @T'I'II @Functor (Identity x) `compose` wrap

yi_ = yi
yi__ = yi
yi___ = yi
yi____ = yi
yi_____ = yi
yi______ = yi
yi_______ = yi

yo, yo_, yo__, yo___, yo____, yo_____, yo______, yo_______, yi'yo
 :: forall from into t a o .
 Precategory into =>
 Covariant Yoneda Functor from into t =>
 (forall e ee . Wrapper into (T'I'II from e ee)) =>
 t a -> into (from a o) (t o)
yo x = yoneda @T'I'II @Functor x `compose` wrap

yo_ = yo
yo__ = yo
yo___ = yo
yo____ = yo
yo_____ = yo
yo______ = yo
yo_______ = yo
yi'yo = yo

yoi :: forall from into t i a o .
 Precategory into =>
 Covariant Yoneda Functor from into (T'II'I t i) =>
 (forall e ee . Wrapper into (T'I'II from e ee)) =>
 (forall e . Wrapper into (T'II'I t i e)) =>
 t a i -> into (from a o) (t o i)
yoi = fio @into unwrap `compose` yo @from @into @(T'II'I t i) `compose` wrap

-- TODO: add Hom functor aliases here
yio :: forall from into t i a o .
 Precategory into =>
 Covariant Yoneda Functor from into (T'I'II t i) =>
 (forall e ee . Wrapper into (T'I'II from e ee)) =>
 (forall e . Wrapper into (T'I'II t i e)) =>
 t i a -> into (from a o) (t i o)
yio = fio @into unwrap `compose` yo @from @into @(T'I'II t i) `compose` wrap

-- yioi :: forall from into w e eee a o .
--  Precategory into =>
--  Covariant Yoneda Functor from into (W_III_I_II w eee e) =>
--  Wrapper into (T'I'II from a o) =>
--  Elicitable T'I'II into (W_III_I_II w eee e o) =>
--  w e a eee -> into (from a o) (w e o eee)
-- yioi x = compose unwrap (yoneda @T'I'II @from @into @(W_III_I_II _ _ _) (wrap x))

yu, yu_, yu__, yu___, yu____, yu_____, yu______, yu_______, li'yu :: forall into t a o .
 Covariant Yoneda Functor into into t =>
 Mapping T'I'II T'I'II into into I (T'I'II into a) =>
 Wrapper into (T'I'II into a o) =>
 Wrapper into (I o) =>
 t a -> into o (t o)
yu x = yoneda @T'I'II @Functor @into @into x `compose` wrap `compose` constant

yu_ = yu
yu__ = yu
yu___ = yu
yu____ = yu
yu_____ = yu
yu______ = yu
yu_______ = yu

li'yu = yu

yui :: forall into t i a o .
 Terminal into =>
 Category into =>
 Covariant Yoneda Functor into into (T'II'I t i) =>
 Covariant Functor into into (T'I'II into a) =>
 Contravariant Functor into into (T'II'I into o) =>
 (forall e ee . Wrapper into (T'II'I into e ee)) =>
 (forall e ee . Wrapper into (T'I'II into e ee)) =>
 (forall e . Wrapper into (T'II'I t i e)) =>
 Wrapper into (into Unit o) =>
 t a i -> into (Supertype (into Unit o)) (t o i)
yui x = yoi @into x `compose` fai @into terminal `compose` wrap

yiu, hu, hu_, hu__, hu___, hu____, hu_____, hu______, hu_______, hu________
 :: forall into t i a o .
 Terminal into =>
 Category into =>
 Covariant Yoneda Functor into into (T'I'II t i) =>
 Covariant Functor into into (T'I'II into a) =>
 Contravariant Functor into into (T'II'I into o) =>
 (forall e . Wrapper into (T'I'II t i e)) =>
 (forall e ee . Wrapper into (T'I'II into e ee)) =>
 (forall e ee . Wrapper into (T'II'I into e ee)) =>
 (forall e . Wrapper into (into () e)) =>
 t i a -> into (Supertype (into Unit o)) (t i o)
yiu x = yio @into x `compose` fai @into terminal `compose` wrap

hu = yiu
hu_ = yiu
hu__ = yiu
hu___ = yiu
hu____ = yiu
hu_____ = yiu
hu______ = yiu
hu_______ = yiu
hu________ = yiu

yiu'he, hu'he, hu_'he, hu__'he, hu___'he, hu____'he, hu_____'he, hu______'he, hu_______'he, hu________'he
 :: forall into t i a o .
 Terminal into =>
 Category into =>
 Covariant Yoneda Functor into into (T'I'II t i) =>
 Covariant Functor into into (T'I'II into a) =>
 Contravariant Functor into into (T'II'I into o) =>
 Wrapper into (into Unit o) =>
 (forall e . Wrapper into (T'I'II t i e)) =>
 (forall e ee . Wrapper into (T'I'II into e ee)) =>
 (forall e ee . Wrapper into (T'II'I into e ee)) =>
 Wrapper into (Supertype (into Unit o)) =>
 Wrapper into (T'II'I into o Unit) =>
 (forall e . Wrapper into (T'I'II t i e)) =>
 t i a -> into (Supertype (Supertype (into Unit o))) (t i o)
yiu'he x = yio @into x `compose` fai @into terminal `compose` wrap `compose` wrap

hu'he = yiu'he
hu_'he = yiu'he
hu__'he = yiu'he
hu___'he = yiu'he
hu____'he = yiu'he
hu_____'he = yiu'he
hu______'he = yiu'he
hu_______'he = yiu'he
hu________'he = yiu'he

he'yiu, he'hu, he'hu_, he'hu__, he'hu___, he'hu____, he'hu_____, he'hu______, he'hu_______, he'hu________
 :: forall into t i a o .
 Terminal into =>
 Category into =>
 Covariant Yoneda Functor into into (T'I'II t i) =>
 Contravariant Functor into (AR) (T'II'I t a) =>
 Covariant Functor into into (T'I'II into a) =>
 Contravariant Functor into into (T'II'I into o) =>
 Wrapper into (into Unit o) =>
 Wrapper into (Supertype (into Unit o)) =>
 (forall e ee . Wrapper into (T'I'II into e ee)) =>
 (forall e ee . Wrapper into (T'II'I into e ee)) =>
 (forall e . Wrapper into (T'II'I into e Unit)) =>
 (forall e . Wrapper into (T'I'II t i e)) =>
 Wrapper into i =>
 t (Supertype i) a -> into (Supertype (into Unit o)) (t i o)
he'yiu x = yio @into (fai @into unwrap x) `compose` fai @into terminal `compose` wrap

he'hu = he'yiu
he'hu_ = he'yiu
he'hu__ = he'yiu
he'hu___ = he'yiu
he'hu____ = he'yiu
he'hu_____ = he'yiu
he'hu______ = he'yiu
he'hu_______ = he'yiu
he'hu________ = he'yiu

yd :: forall from into t tt a o .
 Adjoint Functor into into t tt =>
 Covariant Yoneda Functor from into (t `T'TT'I` tt) =>
 (forall e . Wrapper into ((t `T'TT'I` tt) e)) =>
 Wrapper into (I o) =>
 (forall e ee . Wrapper into (T'I'II from e ee)) =>
 t (tt a) -> into (from a o) o
yd x = unwrap @into
 `compose` component @into @(t `T'TT'I` tt) @I
 `compose` yo (wrap x)

ydi, hd, hd_, hd__, hd___, hd____, hd_____, hd______, hd_______, hd________ :: forall from into t tt i ii a o .
 Adjoint Functor into into (T'II'I t i) (T'I'II tt ii) =>
 Covariant Endo Semi Functor (AR) (T'II'I t i) =>
 Covariant Yoneda Functor from into (T'II'I t i `T'TT'I` T'I'II tt ii) =>
 (forall e . Wrapper into ((T'II'I t i `T'TT'I` T'I'II tt ii) e)) =>
 (forall e . Wrapper into (I e)) =>
 (forall e ee . Wrapper into (T'I'II from e ee)) =>
 (forall e ee . Wrapper from (T'I'II tt e ee)) =>
 (forall e ee . Wrapper from (T'II'I t e ee)) =>
 t (tt ii a) i -> into (from a o) o
ydi x = unwrap @into
 `compose` component @into @(T'II'I t i `T'TT'I` T'I'II tt ii) @I
 `compose` yo (wrap @(AR) (wrap @(AR) (foi @(AR) wrap x)))

hd = ydi
hd_ = ydi
hd__ = ydi
hd___ = ydi
hd____ = ydi
hd_____ = ydi
hd______ = ydi
hd_______ = ydi
hd________ = ydi

yj :: forall from into t tt a o .
 Adjoint Functor (AR) (AR) t tt =>
 Covariant Yoneda Functor from into (tt `T'TT'I` t) =>
 (forall e . Wrapper into ((tt `T'TT'I` t) e)) =>
 Wrapper into (I o) =>
 (forall e ee . Wrapper into (T'I'II from e ee)) =>
 a -> into (from a o) (tt (t o))
yj x = unwrap @into `compose` yo (component @(AR) @I @(tt `T'TT'I` t) (wrap x))

yij, hj, hj_, hj__, hj___, hj____, hj_____, hj______, hj_______, hj________ :: forall from into t tt i ii a o .
 Adjoint Functor (AR) (AR) (t `T'II'I` i) (T'I'II tt ii) =>
 Covariant Yoneda Functor from into (T'I'II tt ii `T'TT'I` T'II'I t i) =>
 Covariant Endo Semi Functor into (T'I'II tt ii) =>
 (forall e . Wrapper into ((T'I'II tt ii `T'TT'I` T'II'I t i) e)) =>
 (forall e . Wrapper into (I e)) =>
 (forall e . Wrapper into (T'II'I t i e)) =>
 (forall e . Wrapper into (T'I'II tt ii e)) =>
 (forall e ee . Wrapper into (T'I'II from e ee)) =>
 a -> into (from a o) (tt ii (t o i))
yij x = unwrap @into `compose` fo (unwrap @into)
 `compose` wrapped (yoneda @T'I'II @Functor @from (component @(AR) @I @(T'I'II tt ii `T'TT'I` T'II'I t i) (wrap x)))

hj = yij
hj_ = yij
hj__ = yij
hj___ = yij
hj____ = yij
hj_____ = yij
hj______ = yij
hj_______ = yij
hj________ = yij

ydi'ydi, hd'hd :: forall from into t tt ttt tttt i ii iii iiii a o .
 Adjoint Functor from from (T'II'I ttt iii) (T'I'II tttt iiii) =>
 Adjoint Functor into into (T'II'I t i) (T'I'II tt ii) =>
 Covariant Endo Semi Functor (AR) (T'II'I t i) =>
 Covariant Endo Semi Functor from (T'II'I ttt iii) =>
 Covariant Endo Semi Functor into (T'I'II tt ii) =>
 Covariant Endo Semi Functor from (T'I'II tttt iiii) =>
 Covariant Endo Semi Functor into (T'II'I t i) =>
 Covariant Yoneda Functor from into (T'II'I t i `T'TT'I` T'I'II tt ii) =>
 Contravariant Endo Semi Functor (AR) (T'II'I into o) =>
 (forall e ee . Wrapper from (T'II'I t e ee)) =>
 (forall e ee . Wrapper from (T'I'II tt e ee)) =>
 (forall e ee . Wrapper from (T'II'I ttt e ee)) =>
 (forall e ee . Wrapper from (T'I'II tttt e ee)) =>
 (forall e ee . Wrapper into (T'I'II from e ee)) =>
 (forall e . Wrapper from (I e)) =>
 (forall e . Wrapper into (I e)) =>
 (forall e . Wrapper into (T'II'I t i `T'TT'I` T'I'II tt ii `T'I_` e)) =>
 (forall e . Wrapper into (T'I'II tt ii `T'TT'I` T'II'I t i `T'I_` e)) =>
 (forall e . Wrapper from (T'II'I ttt iii `T'TT'I` T'I'II tttt iiii `T'I_` e)) =>
 t (tt ii (ttt a iii)) i `AR___` into (from a (tttt iiii o)) o
ydi'ydi x = fai @(AR) fdi (ydi @from @into x)

hd'hd = ydi'ydi

ydi'yij, hd'hj :: forall from into t tt ttt tttt i ii iii iiii a o .
 Contravariant Endo Semi Functor (AR) (T'II'I into (tttt iiii o)) =>
 Covariant Yoneda Functor from into (T'II'I t i `T'TT'I` T'I'II tt ii) =>
 Covariant Endo Semi Functor from (T'II'I ttt iii) =>
 Covariant Endo Semi Functor into (T'II'I t i) =>
 Covariant Endo Semi Functor (AR) (T'II'I t i) =>
 Adjoint Functor into into (T'II'I t i) (T'I'II tt ii) =>
 Adjoint Functor from from (T'II'I ttt iii) (T'I'II tttt iiii) =>
 (forall e . Wrapper into (I e)) =>
 (forall e . Wrapper from (I e)) =>
 (forall e ee . Wrapper from (T'II'I t e ee)) =>
 (forall e ee . Wrapper from (T'II'I ttt e ee)) =>
 (forall e ee . Wrapper from (T'I'II tt e ee)) =>
 (forall e ee . Wrapper from (T'I'II tttt e ee)) =>
 (forall e ee . Wrapper into (T'I'II from e ee)) =>
 (forall e . Wrapper from (T'I'II tttt iiii `T'TT'I` T'II'I ttt iii `T'I_` e)) =>
 (forall e . Wrapper into (T'I'II tt ii `T'TT'I` T'II'I t i `T'I_` e)) =>
 (forall e . Wrapper into (T'II'I t i `T'TT'I` T'I'II tt ii `T'I_` e)) =>
 t (tt ii a) i `AR___` into (from (ttt a iii) o) (tttt iiii o)
ydi'yij x = fai @(AR) fij (ydi @from @into x)

hd'hj = ydi'yij

-- yij'ydi --, hj'hd
 -- :: forall from into t tt ttt tttt i ii iii iiii a o .
 -- Contravariant Endo Semi Functor (AR) (T'II'I into (tt ii (t o i))) =>
 -- Covariant Yoneda Functor from into (T'I'II tt ii `T'TT'I` T'II'I t i) =>
 -- Covariant Endo Semi Functor from (T'I'II ttt iii) =>
 -- Covariant Endo Semi Functor from (T'II'I tttt iiii) =>
 -- Covariant Endo Semi Functor into (T'I'II tt ii) =>
 -- Covariant Endo Semi Functor (AR) (T'II'I t i) =>
 -- Covariant Endo Semi Functor (AR) (T'I'II tt ii) =>
 -- Adjoint Functor from into (T'II'I t i) (T'I'II tt ii) =>
 -- Adjoint Functor from from (T'II'I ttt iii) (T'I'II tttt iiii) =>
 -- (forall e . Wrapper into (I e)) =>
 -- (forall e ee . Wrapper into (T'II'I t e ee)) =>
 -- (forall e ee . Wrapper into (T'I'II tt e ee)) =>
 -- (forall e ee . Wrapper from (T'I'II tttt e ee)) =>
 -- (forall e ee . Wrapper from (T'II'I ttt e ee)) =>
 -- (forall e ee . Wrapper into (T'I'II from e ee)) =>
 -- (forall e . Wrapper from (T'I'II ttt iii `T'TT'I`T'II'I tttt iiii  `T'I_` e)) =>
 -- (forall e . Wrapper into (T'I'II tt ii `T'TT'I` T'II'I t i `T'I_` e)) =>
 -- (forall e . Wrapper into (T'II'I t i `T'TT'I` T'I'II tt ii `T'I_` e)) =>
 -- tttt a iiii `AR___` into (from a (ttt iii o)) (tt ii (t o i))
-- yij'ydi x = fai fdi (yij @from @into x)

-- hj'hd = yij'ydi

-- TODO: should become obsolete as soon as we get used to generate these types of operators
-- yo'hj :: forall from into t tt ttt e a o .
--  Precategory into =>
--  Adjoint Functor from from (T'II'I ttt e) (T'I'II tt e) =>
--  Covariant Functor from from (T'I'II tt e) =>
--  Covariant Yoneda Functor from into t =>
--  (forall ee . Wrapper from ((T'TT'I (T'I'II tt e) (T'II'I ttt e)) ee)) =>
--  (forall ee . Wrapper from ((T'TT'I (T'II'I ttt e) (T'I'II tt e)) ee)) =>
--  (forall ee . Wrapper from (I ee)) =>
--  Wrapper from (T'II'I ttt e a) =>
--  Wrapper from (T'I'II tt e o) =>
--  (forall e ee . Wrapper into (T'I'II from e ee)) =>
--  Contravariant Endo Semi Functor (AR) (T'II'I into (t o)) =>
--  t (ttt a e) -> into (from a (tt e o)) (t o)
-- yo'hj x = fai hj (yo @from @into x)

-- TODO: yo_yo : t (tt a) -> into (from a b) (tt a -> into (from b o) (t (tt o)))

ya :: forall from into t a o .
 Precategory into =>
 Contravariant Yoneda Functor from into t =>
 Elicitable T'II'I into (T'II'I from a o) =>
 t a -> into (from o a) (t o)
ya x = yoneda @T'II'I @Functor x `compose` wrap

yai :: forall from into t e a o .
 Precategory into =>
 Contravariant Yoneda Functor from into (T'II'I t e) =>
 Elicitable T'II'I into (T'II'I from a o) =>
 Elicitable T'I'II into (T'II'I t e o) =>
 t a e -> into (from o a) (t o e)
yai x = compose unwrap (yoneda @T'II'I @Functor @from @into @(T'II'I t e) (wrap x) `compose` wrap)

yai'yij :: forall from into t tt ttt i ii iii a o .
 Precategory into =>
 Contravariant Functor from (AR) (T'II'I into (t o i)) =>
 Adjoint Functor from from (T'II'I tt ii) (T'I'II ttt iii) =>
 Covariant Functor from (AR) (T'I'II into (from (tt ii (t o i)) a)) =>
 Contravariant Yoneda Functor from into (T'II'I t i) =>
 Contravariant Endo Semi Functor (AR) (T'II'I into (t o i)) =>
 (forall e ee . Wrapper into (T'II'I from e ee)) =>
 (forall e . Wrapper from (I e)) =>
 (forall e . Wrapper into (T'II'I t i e)) =>
 (forall e . Wrapper from (T'II'I tt ii e)) =>
 (forall e . Wrapper from (T'I'II ttt iii e)) =>
 (forall e . Wrapper from (T'TT'I (T'I'II ttt iii) (T'II'I tt ii) e)) =>
 t (ttt iii a) i -> into (from (tt o ii) a) (t o i)
yai'yij = fai fij `compose` yai @from @into

-- t (ii `AR` a) i -> into ((o `P` ii) `AR` a) (t o i)

yai'ydi, ha'hd :: forall from into t tt ttt i ii iii a o .
 Precategory into =>
 Contravariant Functor from (AR) (T'II'I into (t o i)) =>
 Adjoint Functor from from (T'II'I tt ii) (T'I'II ttt iii) =>
 Covariant Functor from (AR) (T'I'II into (from (tt ii (t o i)) a)) =>
 Covariant Endo Semi Functor from (T'I'II tt ii) =>
 Contravariant Yoneda Functor from into (T'II'I t i) =>
 Contravariant Endo Semi Functor (AR) (T'II'I into (t (tt o ii) i)) =>
 (forall e ee . Wrapper into (T'II'I from e ee)) =>
 (forall e . Wrapper from (I e)) =>
 (forall e . Wrapper into (T'II'I t i e)) =>
 (forall e . Wrapper from (T'II'I tt ii e)) =>
 (forall e . Wrapper from (T'I'II ttt iii e)) =>
 (forall e . Wrapper from (T'TT'I (T'II'I tt ii) (T'I'II ttt iii) e)) =>
 t a i -> into (from o (ttt iii a)) (t (tt o ii) i)
yai'ydi x = fai (fdi @from) (yai @from @into x)

-- t a i `AR__` into (o `AR_` (ii `AR_` a)) (t (o `P` ii) i)

ha'hd = yai'ydi

yai'ydi'ydi, ha'hd'hd :: forall from into t tt ttt tttt ttttt i ii iii iiii iiiii a o .
 Precategory into =>
 Contravariant Functor from (AR) (T'II'I into (t o i)) =>
 Adjoint Functor from from (T'II'I tt ii) (T'I'II ttt iii) =>
 Adjoint Functor from from (T'II'I tttt iiii) (T'I'II ttttt iiiii) =>
 Covariant Functor from (AR) (T'I'II into (from (tt ii (t o i)) a)) =>
 Covariant Endo Semi Functor from (T'I'II tt ii) =>
 Covariant Endo Semi Functor from (T'II'I ttt iii) =>
 Covariant Endo Semi Functor from (T'II'I tttt iiii) =>
 Covariant Endo Semi Functor from (T'I'II ttttt iiiii) =>
 Contravariant Yoneda Functor from into (T'II'I t i) =>
 Contravariant Endo Semi Functor (AR) (T'II'I into (t (tttt (tt o ii) iiii) i)) =>
 (forall e ee . Wrapper into (T'II'I from e ee)) =>
 (forall e . Wrapper from (I e)) =>
 (forall e . Wrapper into (T'II'I t i e)) =>
 (forall e . Wrapper from (T'II'I tt ii e)) =>
 (forall e . Wrapper from (T'I'II ttt iii e)) =>
 (forall e . Wrapper from (T'II'I tttt iiii e)) =>
 (forall e . Wrapper from (T'I'II ttttt iiiii e)) =>
 (forall e . Wrapper from (T'TT'I (T'II'I tt ii) (T'I'II ttt iii) e)) =>
 (forall e . Wrapper from (T'TT'I (T'II'I tttt iiii) (T'I'II ttttt iiiii) e)) =>
 t a i -> into (from o (ttt iii (ttttt iiiii a))) (t (tttt (tt o ii) iiii) i)
yai'ydi'ydi x = fai (fdi @from `compose` fdi @from) (yai @from @into x)

ha'hd'hd = yai'ydi'ydi

yio'ydi, ho'hd :: forall from into t tt ttt i ii iii a o .
 Precategory into =>
 Contravariant Endo Semi Functor (AR) (T'II'I into (t o i)) =>
 Adjoint Functor from from (T'II'I tt ii) (T'I'II ttt iii) =>
 Covariant Functor from (AR) (T'I'II into (from (ttt iii (t o i)) a)) =>
 Covariant Yoneda Functor from into (T'I'II t i) =>
 Covariant Endo Semi Functor from (T'II'I tt ii) =>
 Covariant Endo Semi Functor from (T'I'II ttt iii) =>
 Contravariant Endo Semi Functor (AR) (T'II'I into (t i o)) =>
 (forall e ee . Wrapper into (T'I'II from e ee)) =>
 (forall e . Wrapper from (I e)) =>
 (forall e . Wrapper into (T'I'II t i e)) =>
 (forall e . Wrapper from (T'I'II ttt iii e)) =>
 (forall e . Wrapper from (T'II'I tt ii e)) =>
 (forall e . Wrapper from (T'TT'I (T'II'I tt ii) (T'I'II ttt iii) e)) =>
 t i (tt a ii) -> into (from a (ttt iii o)) (t i o)
yio'ydi x = fai fdi (yio @from @into x)

ho'hd = yio'ydi

yio'ydi'ydi, ho'hd'hd :: forall from into t tt ttt tttt ttttt i ii iii iiii iiiii a o .
 Precategory into =>
 Contravariant Endo Semi Functor (AR) (T'II'I into (t o i)) =>
 Adjoint Functor from from (T'II'I tt ii) (T'I'II ttt iii) =>
 Adjoint Functor from from (T'II'I tttt iiii) (T'I'II ttttt iiiii) =>
 Covariant Functor from (AR) (T'I'II into (from (ttt iii (t o i)) a)) =>
 Covariant Yoneda Functor from into (T'I'II t i) =>
 Covariant Endo Semi Functor from (T'II'I tt ii) =>
 Covariant Endo Semi Functor from (T'I'II ttt iii) =>
 Covariant Endo Semi Functor from (T'II'I tttt iii) =>
 Contravariant Endo Semi Functor (AR) (T'II'I into (t i o)) =>
 (forall e ee . Wrapper into (T'I'II from e ee)) =>
 (forall e . Wrapper from (I e)) =>
 (forall e . Wrapper into (T'I'II t i e)) =>
 (forall e . Wrapper from (T'I'II ttt iii e)) =>
 (forall e . Wrapper from (T'II'I tt ii e)) =>
 (forall e . Wrapper from (T'II'I tttt iiii e)) =>
 (forall e . Wrapper from (T'I'II ttttt iiiii e)) =>
 (forall e . Wrapper from (T'TT'I (T'II'I tt ii) (T'I'II ttt iii) e)) =>
 (forall e . Wrapper from (T'TT'I (T'II'I tttt iiii) (T'I'II ttttt iiiii) e)) => 
 t i (tt (tttt a iiii) ii) -> into (from a (ttttt iiiii (ttt iii o))) (t i o)
yio'ydi'ydi x = fai (fdi @from `compose` fdi @from) (yio @from @into x)

ho'hd'hd = yio'ydi'ydi

yio'yij, ho'hj :: forall from into t tt ttt i ii iii a o .
 Precategory into =>
 Contravariant Endo Semi Functor (AR) (T'II'I into (t o i)) =>
 Adjoint Functor from from (T'II'I tt ii) (T'I'II ttt iii) =>
 Covariant Functor from (AR) (T'I'II into (from (ttt iii (t o i)) a)) =>
 Covariant Yoneda Functor from into (T'I'II t i) =>
 Covariant Endo Semi Functor from (T'II'I tt ii) =>
 Covariant Endo Semi Functor from (T'I'II ttt iii) =>
 Contravariant Endo Semi Functor (AR) (T'II'I into (t i (ttt iii o))) =>
 (forall e ee . Wrapper into (T'I'II from e ee)) =>
 (forall e . Wrapper from (I e)) =>
 (forall e . Wrapper into (T'I'II t i e)) =>
 (forall e . Wrapper from (T'I'II ttt iii e)) =>
 (forall e . Wrapper from (T'II'I tt ii e)) =>
 (forall e . Wrapper from (T'TT'I (T'I'II ttt iii) (T'II'I tt ii) e)) =>
 t i a -> into (from (tt a ii) o) (t i (ttt iii o))
yio'yij x = fai fij (yio @from @into x)

-- t i a -> into (from (a `P` ii) o) (t i (ii `AR` o))


ho'hj = yio'yij

yio'yij'yij, ho'hj'hj :: forall from into t tt ttt tttt ttttt i ii iii iiii iiiii a o .
 Precategory into =>
 Contravariant Endo Semi Functor (AR) (T'II'I into (t o i)) =>
 Adjoint Functor from from (T'II'I tt ii) (T'I'II ttt iii) =>
 Adjoint Functor from from (T'II'I tttt iiii) (T'I'II ttttt iiiii) =>
 Covariant Functor from (AR) (T'I'II into (from (ttt iii (t o i)) a)) =>
 Covariant Yoneda Functor from into (T'I'II t i) =>
 Covariant Endo Semi Functor from (T'II'I tt ii) =>
 Covariant Endo Semi Functor from (T'I'II ttt iii) =>
 Contravariant Endo Semi Functor (AR) (T'II'I into (t i (ttttt iiiii (ttt iii o)))) =>
 (forall e ee . Wrapper into (T'I'II from e ee)) =>
 (forall e . Wrapper from (I e)) =>
 (forall e . Wrapper into (T'I'II t i e)) =>
 (forall e . Wrapper from (T'II'I tt ii e)) =>
 (forall e . Wrapper from (T'I'II ttt iii e)) =>
 (forall e . Wrapper from (T'II'I tttt iiii e)) =>
 (forall e . Wrapper from (T'I'II ttttt iiiii e)) =>
 (forall e . Wrapper from (T'TT'I (T'I'II ttt iii) (T'II'I tt ii) e)) =>
 (forall e . Wrapper from (T'TT'I (T'I'II ttttt iiiii) (T'II'I tttt iiii) e)) =>
 t i a -> into (from (tt (tttt a iiii) ii) o) (t i (ttttt iiiii (ttt iii o)))
yio'yij'yij = fai (fij @from `compose` fij @from) `compose` yio @from @into

ho'hj'hj = yio'yij'yij

-- t i a -> into (from (a `P` iii `P` ii) o) (t i (iii `AR` (ii `AR` o)))

yia :: forall from into t e a o .
 Precategory into =>
 Contravariant Yoneda Functor from into (T'I'II t e) =>
 Elicitable T'II'I into (T'II'I from a o) =>
 Elicitable T'I'II into (T'I'II t e o) =>
 t e a -> into (from o a) (t e o)
yia x = compose unwrap (yoneda @T'II'I @Functor @from @into @(T'I'II t e) (wrap x) `compose` wrap)

yok, yok_, yok__, yok___, yok____, yok_____, yok______
 , li'yok, li_'yok, li__'yok, li___'yok, li____'yok, li_____'yok, li______'yok, li_______'yok
 :: forall from into t tt l a o .
 Covariant Endo Transformation Functor into (t `T'TT'I` l `L` tt) t =>
 Covariant Yoneda Functor from into t =>
 (forall e ee . Wrapper into (T'I'II from e ee)) =>
 (forall e . Wrapper into (t `T'TT'I` l `L` tt `T'I_` e)) =>
 t a -> into (from a (l `L` tt `T'I` o)) (t o)
yok x = component @into @(T'TT'I t (L l tt))
 `compose` wrap @into @(T'TT'I t (L l tt) _)
 `compose` yo x

yok_ = yok
yok__ = yok
yok___ = yok
yok____ = yok
yok_____ = yok
yok______ = yok
li'yok = yok
li_'yok = yok
li__'yok = yok
li___'yok = yok
li____'yok = yok
li_____'yok = yok
li______'yok = yok
li_______'yok = yok

-- yok'he, yok_'he, yok__'he, yok___'he, yok____'he, yok_____'he, yok______'he
--  :: forall from into tt t l a o .
--  Covariant Endo Transformation Functor into (T'TT'I t (L l tt)) t =>
--  Covariant Semi Functor into into tt =>
--  Covariant Yoneda Functor from into t =>
--  Contravariant Semi Functor from into (T'II'I from (L l tt o)) =>
--  (forall e ee . Wrapper into (T'II'I from (L l tt e) ee)) =>
--  (forall e ee . Wrapper into (T'I'II from (L l tt e) ee)) =>
--  (forall e . Wrapper into (T'TT'I t (L l tt) e)) =>
--  Wrapper into (T'TT'I t (L l tt) o) =>
--  Elicitable T'I'II from a =>
--  t a -> into (from (Supertype a) (L l tt o)) (t o)
-- yok'he x = yok @from @into x `compose` fai @from he

-- yok_'he = yok'he
-- yok__'he = yok'he
-- yok___'he = yok'he
-- yok____'he = yok'he
-- yok_____'he = yok'he
-- yok______'he = yok'he

-- yok'he'he, yok_'he'he, yok__'he'he, yok___'he'he, yok____'he'he, yok_____'he'he, yok______'he'he
--  :: forall from into tt t l a o .
--  Covariant Endo Transformation Functor into (T'TT'I t (L l tt)) t =>
--  Covariant Semi Functor into into tt =>
--  Covariant Yoneda Functor from into t =>
--  Contravariant Semi Functor from into (T'II'I from (L l tt o)) =>
--  Wrapper into (T'I'II from a (L l tt o)) =>
--  Wrapper into (T'II'I from (L l tt o) a) =>
--  Wrapper into (T'II'I from (L l tt o) (Supertype (Supertype a))) =>
--  (forall e . Wrapper into (T'TT'I t (L l tt) e)) =>
--  Elicitable T'I'II from a =>
--  Elicitable T'I'II from (Supertype a) =>
--  t a -> into (from (Supertype (Supertype a)) (L l tt o)) (t o)
-- yok'he'he x = yok @from @into x `compose` fai @from he'he

-- yok_'he'he = yok'he'he
-- yok__'he'he = yok'he'he
-- yok___'he'he = yok'he'he
-- yok____'he'he = yok'he'he
-- yok_____'he'he = yok'he'he
-- yok______'he'he = yok'he'he

yuk, yuk_, yuk__, yuk___, yuk____, yuk_____, yuk______, yi'yuk
 :: forall into tt t l a o .
 Covariant Yoneda Functor into into t =>
 Covariant Endo Transformation Functor into (T'TT'I t (L l tt)) t =>
 Mapping T'I'II T'I'II into into I (T'I'II into a) =>
 (forall e . Wrapper into ((t `T'TT'I` l `L` tt) e)) =>
 (forall e ee . Wrapper into (T'I'II into e ee)) =>
 Wrapper into (I (L l tt o)) =>
 t a -> into (L l tt o) (t o)
yuk x = yok @into @into x `compose` constant

yuk_ = yuk @into @tt
yuk__ = yuk @into @tt
yuk___ = yuk @into @tt
yuk____ = yuk @into @tt
yuk_____ = yuk @into @tt
yuk______ = yuk @into @tt
yi'yuk = yuk @into @tt

-- newtype L l t i = Labeled (t i)

kyo :: forall from into t tt ll a o .
 Precategory into =>
 Component (AR) t (t `T'TT'I` ll `L` tt) =>
 Covariant Yoneda Functor from into t =>
 Covariant Functor from into (T'I'II from (ll `L` tt `T'I` a)) =>
 Contravariant Functor from into (T'II'I from (ll `L` I `T'I` o)) =>
 (forall e ee . Wrapper into (T'I'II from e ee)) =>
 (forall e ee . Wrapper into (T'II'I from e ee)) =>
 (forall e . Wrapper from (I e)) =>
 (forall e . Wrapper from (ll `L`I `T'I` e)) =>
 (forall e . Wrapper from (ll `L`tt `T'I` e)) =>
 t a -> into (from (tt a) ((ll `L` I) o)) (t o)
kyo x = yo (unwrap `identity` component @(AR) @t @(t `T'TT'I` ll `L` tt) x)
 `compose` fio @from (unwrap `compose` unwrap)
 `compose` fai @from unwrap

-- kyok :: forall from into t tt ttt ll lll a o .
 -- Precategory into =>
 -- Component (AR) t (t `T'TT'I` ll `L` tt) =>
 -- Covariant Yoneda Functor from into t =>
 -- Covariant Functor from into (T'I'II from (ll `L` tt `T'I` a)) =>
 -- Contravariant Functor from into (T'II'I from (ll `L` I `T'I` o)) =>
 -- (forall e ee . Wrapper into (T'I'II from e ee)) =>
 -- (forall e ee . Wrapper into (T'II'I from e ee)) =>
 -- (forall e . Wrapper from (I e)) =>
 -- (forall e . Wrapper from (ll `L`I `T'I` e)) =>
 -- (forall e . Wrapper from (ll `L`tt `T'I` e)) =>
--  t a -> into (from (tt a) ((ll `L` I) ((lll `L` ttt) o))) (t o)
-- kyok x = yo (unwrap `identity` component @(AR) @t @(t `T'TT'I` ll `L` tt) x)
--  `compose` fio @from (unwrap `compose` unwrap)
--  `compose` fai @from unwrap

yokl, yokl_, yokl__, yokl___, yokl____, yokl_____, li'yokl ::
 forall from into t tt l ll a o .
 Category into =>
 Covariant Endo Transformation Functor into (t `T'TT'I` l `L` ll `L` tt) (t `TT'T'I` tt) =>
 Covariant Yoneda Functor from into t =>
 (forall i . Wrapper into (t `T'TT'I` l `L` ll `L` tt `T'I_` i)) =>
 (forall i . Wrapper into ((t `TT'T'I` tt) i)) =>
 (forall e ee . Wrapper into (T'I'II from e ee)) =>
 t a -> into (from a (L l (L ll tt) o)) (tt (t o))
yokl x = unwrap @into @(TT'T'I t tt _)
 `compose` component @into @(t `T'TT'I` l `L` ll `L` tt) @(t `TT'T'I` tt)
 `compose` wrap @into @((t `T'TT'I` l `L` ll `L` tt) _)
 `compose` yo x

yokl_ = yokl
yokl__ = yokl
yokl___ = yokl
yokl____ = yokl
yokl_____ = yokl

li'yokl = yokl

yukl, yukl_, yukl__, yukl___, yukl____, yukl_____
 :: forall into t tt l ll a o .
 Category into =>
 Covariant Endo Transformation Functor into (t `T'TT'I` l `L` ll `L` tt) (t `TT'T'I` tt) =>
 Component into I (T'I'II into a) =>
 Covariant Yoneda Functor into into t =>
 (forall i . Wrapper into ((t `T'TT'I` L l (L ll tt)) i)) =>
 (forall i . Wrapper into ((t `TT'T'I` tt) i)) =>
 (forall i ii . Wrapper into (T'I'II into i (L l (L ll tt) ii))) =>
 (forall i ii . Wrapper into (T'I'II into ((L ll tt) i) ii)) =>
 (forall i ii . Wrapper into (T'II'I into (L l (L ll tt) i) ii)) =>
 (forall e . Wrapper into (I (L l (L ll tt) e))) =>
 (forall e ee . Wrapper into (T'I'II into e ee)) =>
 t a -> into (L l (L ll tt) o) (tt (t o))
yukl x = yokl @into @into x `compose` constant

yukl_ = yukl
yukl__ = yukl
yukl___ = yukl
yukl____ = yukl
yukl_____ = yukl

-- TODO: labeling
yiok :: forall from into tt t i a o .
 Category into =>
 Component into (T'I'II t i `T'TT'I` tt) (T'I'II t i) =>
 Covariant Yoneda Functor from into (T'I'II t i) =>
 (forall e ee . Wrapper into (T'I'II from e ee)) =>
 Elicitable T'I'II into (T'I'II t i o) =>
 Elicitable T'II'I into (T'TT'I (T'I'II t i) tt o) =>
 t i a -> into (from a (tt o)) (t i o)
yiok x = unwrap @into @(T'I'II t i o)
 `compose` component @into @(T'TT'I (T'I'II t i) tt)
 `compose` wrap @into @(T'TT'I (T'I'II t i) tt _)
 `compose` yo (T'I'II x)

-- TODO: yok'yo
-- TODO: yok'he'yo

yok'yokl, yok_'yokl, yok__'yokl, yok___'yokl, yok____'yokl, yok_____'yokl, yok______'yokl, li'yok'yokl
 :: forall from into t tt ttt l ll a o .
 Covariant Yoneda Functor from into t =>
 Covariant Endo Semi Functor into t =>
 Covariant Endo Semi Functor from tt =>
 Covariant Endo Semi Functor from ttt =>
 Covariant Semi Functor from into (T'I'II from a) =>
 Contravariant Endo Semi Functor (AR) (T'II'I into (t (ttt o))) =>
 Covariant Endo Transformation Functor into (t `T'TT'I` l `L` tt) t =>
 Covariant Endo Transformation Functor from (ttt `T'TT'I` l `L` ll `L` tt) (ttt `TT'T'I` tt) =>
 (forall e ee . Wrapper into (T'I'II from e ee)) =>
 (forall e . Wrapper from ((ttt `T'TT'I` L l (L ll tt)) e)) =>
 (forall e . Wrapper into (L l tt e)) =>
 (forall e . Wrapper from (L l tt e)) =>
 (forall e . Wrapper into (L l (L ll tt) e)) =>
 (forall e . Wrapper into (L ll tt e)) =>
 (forall e . Wrapper from (L l (L ll tt) e)) =>
 (forall e . Wrapper into (T'TT'I t (L l tt) e)) =>
 (forall e . Wrapper into (T'TT'I t (L l (L ll tt)) e)) =>
 (forall e . Wrapper from (T'TT'I ttt (L ll tt) e)) =>
 (forall e . Wrapper from (TT'T'I ttt tt e)) =>
 (forall e . Wrapper from (TT'T'I ttt (L l (L ll tt)) e)) =>
 t (ttt a) -> into (from a (L l (L ll tt) o)) (t (ttt o))
yok'yokl x = fai (fio (wrap @from @(L l tt _)) `compose` fokl @from @from @ttt @tt @l @ll)
  (yok @from @into @t @tt @l x)

yok_'yokl = yok'yokl
yok__'yokl = yok'yokl
yok___'yokl = yok'yokl
yok____'yokl = yok'yokl
yok_____'yokl = yok'yokl
yok______'yokl = yok'yokl

li'yok'yokl = yok'yokl

yok'yukl, yok_'yukl, yok__'yukl, yok___'yukl, yok____'yukl, yok_____'yukl, yok______'yukl
 :: forall into t tt ttt l ll a o .
 Covariant Yoneda Functor (AR) into t =>
 Covariant Endo Semi Functor into t =>
 Covariant Endo Semi Functor (AR) tt =>
 Covariant Endo Semi Functor (AR) ttt =>
 Covariant Semi Functor (AR) into (T'I'II (AR) a) =>
 Contravariant Endo Semi Functor (AR) (T'II'I into (t (ttt o))) =>
 Covariant Endo Transformation Functor into (t `T'TT'I` l `L` tt) t =>
 Covariant Endo Transformation Functor (AR) (ttt `T'TT'I` l `L` ll `L` tt) (ttt `TT'T'I` tt) =>
 (forall e ee . Wrapper into (T'I'II (AR) e ee)) =>
 (forall e . Wrapper (AR) ((ttt `T'TT'I` L l (L ll tt)) e)) =>
 (forall e . Wrapper into (L l tt e)) =>
 (forall e . Wrapper (AR) (L l tt e)) =>
 (forall e . Wrapper into (L l (L ll tt) e)) =>
 (forall e . Wrapper into (L ll tt e)) =>
 (forall e . Wrapper (AR) (L l (L ll tt) e)) =>
 (forall e . Wrapper into (T'TT'I t (L l tt) e)) =>
 (forall e . Wrapper into (T'TT'I t (L l (L ll tt)) e)) =>
 (forall e . Wrapper (AR) (T'TT'I ttt (L ll tt) e)) =>
 (forall e . Wrapper (AR) (TT'T'I ttt tt e)) =>
 (forall e . Wrapper (AR) (TT'T'I ttt (L l (L ll tt)) e)) =>
 t (ttt a) -> into (L l (L ll tt) o) (t (ttt o))
yok'yukl x = fai (fio (wrap @(AR) @(L l tt _)) `compose` fukl @(AR) @ttt @tt @l @ll) (yok @(AR) @into @t @tt @l x)

yok_'yukl = yok'yukl
yok__'yukl = yok'yukl
yok___'yukl = yok'yukl
yok____'yukl = yok'yukl
yok_____'yukl = yok'yukl
yok______'yukl = yok'yukl

-- TODO: , yokl_'yokl, yokl__'yokl, yokl___'yokl, yokl____'yokl, yokl_____'yokl
yokl'yokl :: forall from into t tt ttt l ll lll a o .
 Covariant Yoneda Functor from into t =>
 Covariant Semi Functor from into t =>
 Covariant Endo Semi Functor from tt =>
 Covariant Endo Semi Functor from ttt =>
 Covariant Semi Functor from into ttt =>
 Covariant Endo Transformation Functor into (t `T'TT'I` l `L` lll `L` ttt) (t `TT'T'I` ttt) =>
 Covariant Endo Transformation Functor from (tt `T'TT'I` ll `L` lll `L` ttt) (tt `TT'T'I` ttt) =>
 Contravariant Endo Semi Functor (AR) (T'II'I into (ttt (t (tt o)))) =>
 (forall e . Wrapper from (L l (L lll ttt) (tt e))) =>
 (forall e . Wrapper from (L l (L ll (L lll ttt)) e)) =>
 (forall e . Wrapper from (TT'T'I tt (L lll ttt) e)) =>
 (forall e . Wrapper from (L lll ttt e)) =>
 (forall e . Wrapper from (L ll (L lll ttt) e)) =>
 (forall e . Wrapper from (T'TT'I tt (L ll (L lll ttt)) e)) =>
 (forall e . Wrapper into (L lll ttt e)) =>
 (forall e . Wrapper into (L l (L lll ttt) (tt e))) =>
 (forall e . Wrapper into (L l (L lll ttt) e)) =>
 (forall e . Wrapper into (T'TT'I t (L l (L lll ttt)) e)) =>
 (forall e . Wrapper into (TT'T'I t (L l (L lll ttt)) e)) =>
 (forall e . Wrapper into (T'TT'I t ttt e)) =>
 (forall e . Wrapper into (TT'T'I t ttt e)) =>
 (forall e . Wrapper from (TT'T'I tt ttt e)) =>
 (forall e ee . Wrapper into (T'I'II from e ee)) =>
 t (tt a) -> into (from a (L l (L ll (L lll ttt)) o)) (ttt (t (tt o)))
yokl'yokl x = fai
 (fio @from (wrap `compose` wrap)
  `compose` fokl @from @from @tt @ttt @ll @lll
  `compose` fio @from unwrap
 )
 (yokl @from @into @t @ttt @l @lll @(tt a) @(tt o) x)

-- yokl x: into (from (tt a) (L l (L lll ttt) o)) (ttt (t (tt o)))

-- fokl: from a (L ll (L lll ttt) o) -> into (tt a) (ttt (tt o))

-- yokl'yok :: forall from into t tt ttt l a o .
 -- Covariant Yoneda Functor from into t =>
 -- Covariant Endo Semi Functor from tt =>
 -- Covariant Endo Semi Functor from ttt =>
 -- Contravariant Endo Semi Functor (AR) (T'II'I into (ttt (t o))) =>
 -- Covariant Transformation Functor from from (T'TT'I ttt tt) ttt =>
 -- Covariant Transformation Functor from into (T'TT'I t ttt) (TT'T'I t ttt) =>
 -- Elicitable T'II'I into (T'I'II from (ttt a) (ttt o)) =>
 -- Elicitable T'I'II into (TT'T'I t ttt o) =>
 -- Elicitable T'II'I into (T'TT'I t ttt o) =>
 -- Elicitable T'II'I from (T'TT'I ttt tt o) =>
 -- t (ttt a) -> into (from a (L l tt o)) (ttt (t o))
-- yokl'yok x = fai fok (yokl @from @into x)

ho, ho_, ho__, ho___, ho____, ho_____, ho______, ho_______, ho________, yi'ho :: forall from into u i a o .
 Precategory into =>
 Covariant Yoneda Functor from into (T'I'II u i) =>
 (forall e . Wrapper into (T'I'II u i e)) =>
 (forall e ee . Wrapper into (T'I'II from e ee)) =>
 u i a -> into (from a o) (u i o)
ho = yio @from @into @u

ho_ = ho
ho__ = ho
ho___ = ho
ho____ = ho
ho_____ = ho
ho______ = ho
ho_______ = ho
ho________ = ho
yi'ho = ho

ho'he, ho_'he, ho__'he, ho___'he, ho____'he, ho_____'he, ho______'he, ho_______'he, ho________'he
 :: forall from into u i a o .
 Covariant Yoneda Functor from into (T'I'II u i) =>
 Contravariant Semi Functor from into (T'II'I from o) =>
 Covariant Semi Functor from into (T'I'II from o) =>
 Wrapper from a =>
 (forall e ee . Wrapper into (T'I'II from e ee)) =>
 (forall e ee . Wrapper into (T'II'I from e ee)) =>
 (forall e ee . Wrapper into (T'I'II u e ee)) =>
 u i a -> into (from (Supertype a) o) (u i o)
ho'he = fai @into (fai @from he) `compose` yio @from @into @u

ho_'he = ho'he
ho__'he = ho'he
ho___'he = ho'he
ho____'he = ho'he
ho_____'he = ho'he
ho______'he = ho'he
ho_______'he = ho'he
ho________'he = ho'he

ho'he'he, ho_'he'he, ho__'he'he, ho___'he'he, ho____'he'he, ho_____'he'he, ho______'he'he, ho_______'he'he, ho________'he'he
 :: forall from into u i a o .
 Covariant Yoneda Functor from into (T'I'II u i) =>
 Contravariant Semi Functor from into (T'II'I from o) =>
 Covariant Semi Functor from into (T'I'II from o) =>
 Wrapper from a =>
 Wrapper from (Supertype a) =>
 (forall e . Wrapper into (T'I'II u i e)) =>
 (forall e ee . Wrapper into (T'I'II from e ee)) =>
 (forall e ee . Wrapper into (T'II'I from e ee)) =>
 Wrapper into (T'II'I from o (Supertype a)) =>
 Wrapper into (T'II'I from o (Supertype (Supertype a))) =>
 u i a -> into (from (Supertype (Supertype a)) o) (u i o)
ho'he'he = fai @into (fai @from (he `compose` he)) `compose` yio @from @into @u

ho_'he'he = ho'he'he
ho__'he'he = ho'he'he
ho___'he'he = ho'he'he
ho____'he'he = ho'he'he
ho_____'he'he = ho'he'he
ho______'he'he = ho'he'he
ho_______'he'he = ho'he'he
ho________'he'he = ho'he'he

ho'he'he'hv, ho_'he'he'hv, ho__'he'he'hv, ho___'he'he'hv, ho____'he'he'hv, ho_____'he'he'hv, ho______'he'he'hv, ho_______'he'he'hv, ho________'he'he'hv
 :: forall u e i a o .
 Covariant Yoneda Functor (AR) (AR) I =>
 Covariant Yoneda Functor (AR) (AR) (T'I'II u i) =>
 Contravariant Semi Functor (AR) (AR) (T'II'I (AR) o) =>
 Covariant Semi Functor (AR) (AR) (T'I'II (AR) o) =>
 Wrapper (AR) a =>
 Wrapper (AR) (Supertype a) =>
 Wrapper (AR) (T'I'II u i o) =>
 Wrapper (AR) (T'I'II (AR) a o) =>
 Wrapper (AR) (T'II'I (AR) o a) =>
 Wrapper (AR) (T'II'I (AR) o (Supertype a)) =>
 Wrapper (AR) (T'II'I (AR) o (Supertype (Supertype a))) =>
 (Supertype (Supertype a) ~ (AR) e o) =>
 u i a -> e -> (u i o)
ho'he'he'hv = fai @(AR) (fai @(AR) (he `compose` he) `compose` yi) `compose` yio @(AR) @(AR) @u

ho_'he'he'hv = ho'he'he'hv
ho__'he'he'hv = ho'he'he'hv
ho___'he'he'hv = ho'he'he'hv
ho____'he'he'hv = ho'he'he'hv
ho_____'he'he'hv = ho'he'he'hv
ho______'he'he'hv = ho'he'he'hv
ho_______'he'he'hv = ho'he'he'hv
ho________'he'he'hv = ho'he'he'hv

ho'he'he'he, ho_'he'he'he, ho__'he'he'he, ho___'he'he'he, ho____'he'he'he, ho_____'he'he'he, ho______'he'he'he, ho_______'he'he'he, ho________'he'he'he
 :: forall from into u i a o .
 Precategory from =>
 Precategory into =>
 Covariant Yoneda Functor from into (T'I'II u i) =>
 Contravariant Semi Functor from into (T'II'I from o) =>
 Covariant Semi Functor from into (T'I'II from o) =>
 Wrapper from a =>
 Wrapper from (Supertype a) =>
 Wrapper from (Supertype (Supertype a)) =>
 (forall e . Wrapper into (T'I'II u i e)) =>
 (forall e ee . Wrapper into (T'I'II from e ee)) =>
 (forall e ee . Wrapper into (T'II'I from e ee)) =>
 Wrapper into (T'II'I from o (Supertype a)) =>
 Wrapper into (T'II'I from o (Supertype (Supertype a))) =>
 Wrapper into (T'II'I from o (Supertype (Supertype (Supertype a)))) =>
 u i a -> into (from (Supertype (Supertype (Supertype a))) o) (u i o)
ho'he'he'he x = yio @from @into @u x `compose` fai @from he `compose` fai @from he `compose` fai @from he

ho_'he'he'he = ho'he'he'he
ho__'he'he'he = ho'he'he'he
ho___'he'he'he = ho'he'he'he
ho____'he'he'he = ho'he'he'he
ho_____'he'he'he = ho'he'he'he
ho______'he'he'he = ho'he'he'he
ho_______'he'he'he = ho'he'he'he
ho________'he'he'he = ho'he'he'he

ho'he'he'he'he, ho_'he'he'he'he, ho__'he'he'he'he, ho___'he'he'he'he, ho____'he'he'he'he, ho_____'he'he'he'he, ho______'he'he'he'he, ho_______'he'he'he'he, ho________'he'he'he'he
 :: forall from into u i a o .
 Precategory from =>
 Precategory into =>
 Covariant Yoneda Functor from into (T'I'II u i) =>
 Contravariant Semi Functor from into (T'II'I from o) =>
 Covariant Semi Functor from into (T'I'II from o) =>
 Wrapper from a =>
 Wrapper from (Supertype a) =>
 Wrapper from (Supertype (Supertype a)) =>
 Wrapper from (Supertype (Supertype (Supertype a))) =>
 (forall e . Wrapper into (T'I'II u i e)) =>
 (forall e ee . Wrapper into (T'I'II from e ee)) =>
 (forall e ee . Wrapper into (T'II'I from e ee)) =>
 Wrapper into (T'II'I from o (Supertype a)) =>
 Wrapper into (T'II'I from o (Supertype (Supertype a))) =>
 Wrapper into (T'II'I from o (Supertype (Supertype (Supertype a)))) =>
 Wrapper into (T'II'I from o (Supertype (Supertype (Supertype (Supertype a))))) =>
 u i a -> into (from (Supertype (Supertype (Supertype (Supertype a)))) o) (u i o)
ho'he'he'he'he x = yio @from @into @u x `compose` fai @from he `compose` fai @from he `compose` fai @from he `compose` fai @from he

ho_'he'he'he'he = ho'he'he'he'he
ho__'he'he'he'he = ho'he'he'he'he
ho___'he'he'he'he = ho'he'he'he'he
ho____'he'he'he'he = ho'he'he'he'he
ho_____'he'he'he'he = ho'he'he'he'he
ho______'he'he'he'he = ho'he'he'he'he
ho_______'he'he'he'he = ho'he'he'he'he
ho________'he'he'he'he = ho'he'he'he'he

-- ho'ho, ho_'ho :: forall from u uu i ii a o .
--  Covariant Yoneda Functor u from (T'I'II u i) =>
--  Covariant Semi Functor from u (T'I'II uu ii) =>
--  Contravariant Yoneda Functor (AR) (AR) (T'II'I u i) =>
--  Covariant Endo Semi Functor (AR) (T'I'II (AR) (u i (uu a ii))) =>
--  Contravariant Semi Functor (AR) (AR) (T'II'I from (u i (uu ii o))) =>
--  (forall e ee . Wrapper from (T'I'II u e ee)) =>
--  (forall e ee . Wrapper from (T'I'II uu e ee)) =>
--  (forall e ee . Wrapper u (T'I'II uu e ee)) =>
--  u i (uu ii a) -> from (from a o) (u i (uu ii o))
-- ho'ho x = fai @(AR) @(AR) (fio @from @u) (ho @u @from x)

-- ho_'ho = ho'ho

-- ho'ho'ho :: forall from u uu uuu o i ii iii a .
--  Covariant Yoneda Functor u from (T'I'II u i) =>
--  Contravariant Yoneda Functor (AR) (AR) (T'II'I u i) =>
--  Covariant Semi Functor from u (T'I'II uu ii) =>
--  Covariant Endo Semi Functor from (T'I'II uuu iii) =>
--  Covariant Endo Semi Functor (AR) (T'I'II (AR) (u i (uu a ii))) =>
--  Contravariant Semi Functor (AR) (AR) (T'II'I from (u i (uu ii (uuu iii o)))) =>
--  (forall e ee . Wrapper from (T'I'II uuu e ee)) =>
--  (forall e ee . Wrapper u (T'I'II uu e ee)) =>
--  (forall e ee . Wrapper from (T'I'II u e ee)) =>
--  -- Wrapper from (T'I'II uu ii (uuu iii o)) =>
--  -- Wrapper from (T'I'II u e (uu ii (uuu iii o))) =>
--  -- Wrapper from (T'I'II u (uu ii a) (uu ii o)) =>
--  -- Wrapper from (T'I'II u (uu ii (uuu iii a)) (uu ii (uuu iii o))) =>
--  u i (uu ii (uuu iii a)) -> from (from a o) (u i (uu ii (uuu iii o)))
-- ho'ho'ho x = fai @(AR) @(AR) (fio @from `compose` fio @from) (ho @u @from x)

yio'yio'yui, yio'ho'yui, ho'yio'yui, ho'ho'yui
 :: forall from u uu uuu o i ii iii a .
 Terminal from =>
 Category from =>
 Covariant Yoneda Functor u from (T'I'II u i) =>
 Contravariant Yoneda Functor (AR) (AR) (T'II'I u i) =>
 Covariant Semi Functor from u (T'I'II uu ii) =>
 Covariant Endo Semi Functor from (T'II'I uuu iii) =>
 Covariant Endo Semi Functor (AR) (T'I'II (AR) (u i (uu a ii))) =>
 Contravariant Semi Functor (AR) (AR) (T'II'I from (u i (uu ii (uuu o iii)))) =>
 (forall e ee . Wrapper from (T'II'I uuu e ee)) =>
 (forall e ee . Wrapper from (T'I'II uu e ee)) =>
 (forall e ee . Wrapper from (T'I'II u e ee)) =>
 (forall e ee . Wrapper u (T'I'II uu e ee)) =>
 Wrapper (AR) (from Unit o) =>
 u i (uu ii (uuu a iii)) -> from (Supertype (from Unit o)) (u i (uu ii (uuu o iii)))
yio'yio'yui x = fai @(AR) @(AR) (fio @from `compose` fui @from) (ho @u @from x)

ho'yio'yui = yio'yio'yui
yio'ho'yui = yio'yio'yui
ho'ho'yui = yio'yio'yui

-- ho'ho'hu :: forall from u uu uuu o i ee eee a .
 -- Category from =>
 -- Terminal from =>
 -- Covariant Yoneda Functor uuu (AR) (T'I'II u i) =>
 -- Covariant Semi Functor from uuu (T'I'II uu ee) =>
 -- Covariant Endo Semi Functor from (T'I'II uuu eee) =>
 -- Constant Endo Semi Functor from (T'I'II uuu eee) =>
 -- (forall i . Wrapper uuu (T'I'II uu ee i)) =>
 -- (forall i . Wrapper from (T'I'II uuu eee i)) =>
 -- Wrapper (AR) (from Unit o) =>
 -- u i (uu ee (uuu eee a)) -> Supertype (from Unit o) -> u i (uu ee (uuu eee o))
-- ho'ho'hu = fai (fio @from `compose` fiu @from) `compose` ho @uuu

-- ho'hu :: forall from u uu o e ee a .
 -- Category from =>
 -- Terminal from =>
 -- Covariant Yoneda Functor u from (T'I'II u e) =>
 -- Contravariant Yoneda Functor (AR) (AR) (T'II'I u e) =>
 -- Covariant Semi Functor from u (T'I'II uu ee) =>
 -- Covariant Endo Semi Functor (AR) (T'I'II (AR) (u e (uu a ee))) =>
 -- Contravariant Semi Functor (AR) (AR) (T'II'I from (u e (uu ee o))) =>
 -- (forall eee . Wrapper u (T'I'II uu ee eee)) =>
 -- Wrapper from (T'I'II uu ee o) =>
 -- Wrapper from (T'I'II u e (uu ee o)) =>
 -- Wrapper from (T'I'II u (uu ee a) (uu ee o)) =>
 -- -- Wrapper (AR) (from Unit o) =>
 -- u e (uu ee a) -> from (Supertype (from Unit o)) (u e (uu ee o))
-- ho'hu = fai (fiu @from) `compose` ho @u

-- ho'ha, ho_'ha, ho__'ha, ho___'ha, ho____'ha, ho_____'ha, ho______'ha, ho_______'ha, ho________'ha
--  :: forall from u uu o i ii a .
--  Covariant Yoneda Functor u (AR) (T'I'II u i) =>
--  Contravariant Yoneda Functor u (AR) (T'II'I u i) =>
--  Contravariant Semi Functor from u (T'II'I uu ii) =>
--  Contravariant Endo Semi Functor (AR) (T'II'I (AR) (u i (uu a ii))) =>
--  (forall e ee . Wrapper u (T'II'I uu e ee)) =>
--  (forall e ee . Wrapper from (T'I'II u e ee)) =>
--  u i (uu o ii) -> from a o -> u i (uu a ii)
-- ho'ha x = fai @(AR) @(AR) fai (ho @u x)

-- ho_'ha = ho'ha
-- ho__'ha = ho'ha
-- ho___'ha = ho'ha
-- ho____'ha = ho'ha
-- ho_____'ha = ho'ha
-- ho______'ha = ho'ha
-- ho_______'ha = ho'ha
-- ho________'ha = ho'ha

-- ho'ha'he, ho_'ha'he, ho__'ha'he, ho___'ha'he, ho____'ha'he, ho_____'ha'he, ho______'ha'he, ho_______'ha'he, ho________'ha'he
--  :: forall from u uu o i ii a .
--  Covariant Yoneda Functor u (AR) (T'I'II u i) =>
--  Contravariant Semi Functor from u (T'II'I uu ii) =>
--  (forall e ee . Wrapper u (T'II'I uu e ee)) =>
--  Wrapper from a =>
--  u i (uu o ii) -> from (Supertype a) o -> u i (uu a ii)
-- ho'ha'he x = fai (fai `compose` fai @from unwrap) (ho @u x)

-- ho_'ha'he = ho'ha'he
-- ho__'ha'he = ho'ha'he
-- ho___'ha'he = ho'ha'he
-- ho____'ha'he = ho'ha'he
-- ho_____'ha'he = ho'ha'he
-- ho______'ha'he = ho'ha'he
-- ho_______'ha'he = ho'ha'he
-- ho________'ha'he = ho'ha'he

-- ho'ha'he'he, ho_'ha'he'he, ho__'ha'he'he, ho___'ha'he'he, ho____'ha'he'he, ho_____'ha'he'he, ho______'ha'he'he, ho_______'ha'he'he, ho________'ha'he'he
--  :: forall from u uu o i ii a .
--  Covariant Yoneda Functor u (AR) (T'I'II u i) =>
--  Contravariant Semi Functor from u (T'II'I uu ii) =>
--  (forall e ee . Wrapper u (T'II'I uu e ee)) =>
--  Wrapper from a =>
--  Wrapper from (Supertype a) =>
--  u i (uu o ii) -> from (Supertype (Supertype a)) o -> u i (uu a ii)
-- ho'ha'he'he x = fai (fai `compose` fai @from he'he) (ho @u x)

-- ho_'ha'he'he = ho'ha'he'he
-- ho__'ha'he'he = ho'ha'he'he
-- ho___'ha'he'he = ho'ha'he'he
-- ho____'ha'he'he = ho'ha'he'he
-- ho_____'ha'he'he = ho'ha'he'he
-- ho______'ha'he'he = ho'ha'he'he
-- ho_______'ha'he'he = ho'ha'he'he
-- ho________'ha'he'he = ho'ha'he'he

-- ho'yo, ho_'yo, ho__'yo, ho___'yo, ho____'yo, ho_____'yo, ho______'yo, ho_______'yo, ho________'yo
--  :: forall from u t o e a .
--  Covariant Yoneda Functor from (AR) (T'I'II u e) =>
--  Contravariant Yoneda Functor from (AR) (T'II'I u e) =>
--  Covariant Endo Semi Functor from t =>
--  Constant Semi Functor from (AR) t =>
--  u e (t a) -> from a o -> u e (t o)
-- ho'yo x = fai (fo @from) (ho @from x)

-- ho_'yo = ho'yo
-- ho__'yo = ho'yo
-- ho___'yo = ho'yo
-- ho____'yo = ho'yo
-- ho_____'yo = ho'yo
-- ho______'yo = ho'yo
-- ho_______'yo = ho'yo
-- ho________'yo = ho'yo

ho'yu, ho_'yu, ho__'yu, ho___'yu, ho____'yu, ho_____'yu, ho______'yu, ho_______'yu, ho________'yu
 :: forall u t o e a .
 Covariant Yoneda Functor (AR) (AR) (T'I'II u e) =>
 Contravariant Yoneda Functor (AR) (AR) (T'II'I u e) =>
 Mapping T'I'II T'I'II (AR) (AR) I (T'I'II (AR) a) =>
 Covariant Endo Semi Functor (AR) t =>
 Constant Semi Functor (AR) (AR) t =>
 u e (t a) -> o -> u e (t o)
ho'yu x = fai @(AR) @(AR) (fu @(AR)) (ho @(AR) x)

ho_'yu = ho'yu
ho__'yu = ho'yu
ho___'yu = ho'yu
ho____'yu = ho'yu
ho_____'yu = ho'yu
ho______'yu = ho'yu
ho_______'yu = ho'yu
ho________'yu = ho'yu

-- ho'yoi, ho_'yoi, ho__'yoi, ho___'yoi, ho____'yoi, ho_____'yoi, ho______'yoi, ho_______'yoi, ho________'yoi
--  :: forall from u t o e a .
--  Covariant Yoneda Functor from (AR) (T'I'II u e) =>
--  Contravariant Yoneda Functor from (AR) (T'II'I u e) =>
--  Covariant Endo Semi Functor from (T'II'I t e) =>
--  (forall ee . Wrapper from (T'II'I t e ee)) =>
--  u e (t a e) -> from a o -> u e (t o e)
-- ho'yoi x = fai (foi @from) (ho @from x)

-- ho_'yoi = ho'yoi
-- ho__'yoi = ho'yoi
-- ho___'yoi = ho'yoi
-- ho____'yoi = ho'yoi
-- ho_____'yoi = ho'yoi
-- ho______'yoi = ho'yoi
-- ho_______'yoi = ho'yoi
-- ho________'yoi = ho'yoi

ho'yui, ho_'yui, ho__'yui, ho___'yui, ho____'yui, ho_____'yui, ho______'yui, ho_______'yui, ho________'yui
 :: forall u t o e a .
 Covariant Yoneda Functor (AR) (AR) (T'I'II u e) =>
 Contravariant Yoneda Functor (AR) (AR) (T'II'I u e) =>
 Mapping T'I'II T'I'II (AR) (AR) I (T'I'II (AR) a) =>
 Covariant Endo Semi Functor (AR) (T'II'I t e) =>
 Constant Semi Functor (AR) (AR) (T'II'I t e) =>
 u e (t a e) -> o -> u e (t o e)
ho'yui x = fai @(AR) @(AR) (fui @(AR)) (ho @(AR) x)

ho_'yui = ho'yui
ho__'yui = ho'yui
ho___'yui = ho'yui
ho____'yui = ho'yui
ho_____'yui = ho'yui
ho______'yui = ho'yui
ho_______'yui = ho'yui
ho________'yui = ho'yui

ho'yioi :: forall from u t o e ee eee a .
 Covariant Yoneda Functor from (AR) (T'I'II u e) =>
 Contravariant Yoneda Functor from (AR) (T'II'I u e) =>
 Covariant Endo Semi Functor from (W_III_I_II t eee ee) =>
 Wrapper from (W_III_I_II t eee ee a) =>
 Wrapper from (W_III_I_II t eee ee o) =>
 u e (t ee a eee) -> from a o -> u e (t ee o eee)
ho'yioi x = fai (fioi @from) (ho @from x)

he'ho, he_'ho, he__'ho, he___'ho, he____'ho, he_____'ho, he______'ho, he_______'ho, he________'ho
 :: forall from into u i a o .
 Covariant Yoneda Functor from into (T'I'II u (Supertype i)) =>
 Contravariant Semi Functor into into (T'II'I u o) =>
 Wrapper into i =>
 (forall e ee . Wrapper into (T'I'II from e ee)) =>
 (forall e ee . Wrapper into (T'I'II u e ee)) =>
 (forall e ee . Wrapper into (T'II'I u e ee)) =>
 u (Supertype i) a -> into (from a o) (u i o)
he'ho x = fai @into he
 `compose` yio @from @into @u x

he_'ho= he'ho
he__'ho= he'ho
he___'ho= he'ho
he____'ho= he'ho
he_____'ho= he'ho
he______'ho= he'ho
he_______'ho= he'ho
he________'ho= he'ho

he'ho'he, he_'ho'he, he__'ho'he, he___'ho'he, he____'ho'he, he_____'ho'he, he______'ho'he, he_______'ho'he, he________'ho'he
 :: forall from into u i a o .
 Covariant Yoneda Functor from into (T'I'II u (Supertype i)) =>
 Contravariant Semi Functor from into (T'II'I u o) =>
 Contravariant Semi Functor from into (T'II'I from o) =>
 Wrapper from a =>
 Wrapper from i =>
 (forall e ee . Wrapper into (T'II'I from e ee)) =>
 (forall e ee . Wrapper into (T'I'II from e ee)) =>
 (forall e ee . Wrapper into (T'II'I u e ee)) =>
 (forall e ee . Wrapper into (T'I'II u e ee)) =>
 Wrapper into (T'II'I u o (Supertype i)) =>
 Wrapper into (T'II'I from o (Supertype a)) =>
 u (Supertype i) a -> into (from (Supertype a) o) (u i o)
he'ho'he x = fai @from @into he
 `compose` yio @from @into @u x
 `compose` fai @from @into he

he_'ho'he = he'ho'he
he__'ho'he = he'ho'he
he___'ho'he = he'ho'he
he____'ho'he = he'ho'he
he_____'ho'he = he'ho'he
he______'ho'he = he'ho'he
he_______'ho'he = he'ho'he
he________'ho'he = he'ho'he

-- he'hu
 -- :: forall from into u i a o .
 -- Precategory from =>
 -- Category into =>
 -- Covariant Yoneda Functor into into (T'I'II u i) =>
 -- Constant Semi Functor (AR) (AR) (T'I'II u i) =>
 -- Mapping T'I'II T'I'II (AR) (AR) (T'I'II u i) (T'I'II u i) =>
 -- Contravariant Semi Functor from (AR) (T'II'I u a) =>
 -- Covariant Semi Functor from into (T'I'II from o) =>
 -- Wrapper from i =>
 -- Wrapper into (into () o) =>
 -- Wrapper into (T'I'II into () o) =>
 -- Wrapper into (T'I'II u i o) =>
 -- Wrapper into (T'I'II from a o) =>
 -- u (Supertype i) a -> into (Supertype (into () o)) (u i o)
-- he'hu = yiu @into @u `compose` he @from

-- he'he'ho
 -- :: forall from into u i a o .
 -- Precategory from =>
 -- Precategory into =>
 -- Covariant Yoneda Functor from into (T'I'II u i) =>
 -- Contravariant Semi Functor from (AR) (T'II'I u a) =>
 -- Covariant Semi Functor from into (T'I'II from o) =>
 -- Elicitable T'I'II from i =>
 -- Elicitable T'I'II from (Supertype i) =>
 -- Elicitable T'I'II into (T'I'II u i o) =>
 -- Elicitable T'II'I into (T'I'II from a o) =>
 -- Wrapper into (T'II'I from o a) =>
 -- Wrapper into (T'II'I from o (Supertype a)) =>
 -- u (Supertype (Supertype i)) a -> into (from a o) (u i o)
-- -- he'he'ho = yio @from @into @u `compose` fai @from he'he

-- he'he'he'ho
 -- :: forall from into u i a o .
 -- Precategory from =>
 -- Precategory into =>
 -- Covariant Yoneda Functor from into (T'I'II u i) =>
 -- Contravariant Semi Functor from (AR) (T'II'I u a) =>
 -- Covariant Semi Functor from into (T'I'II from o) =>
 -- Wrapper from i =>
 -- Wrapper from (Supertype i) =>
 -- Wrapper from (Supertype (Supertype i)) =>
 -- Wrapper into (T'I'II u i o) =>
 -- Wrapper into (T'I'II from a o) =>
 -- Wrapper into (T'II'I from o a) =>
 -- -- Wrapper into (T'II'I from o (Supertype a)) =>
 -- u (Supertype (Supertype (Supertype i))) a -> into (from a o) (u i o)
-- he'he'he'ho = yio @from @into @u `compose` fai @from he'he'he

ha, ha_, ha__, ha___, ha____, ha_____, ha______, ha_______, ha________ :: forall from u e a o .
 Contravariant Yoneda Functor from (AR) (T'II'I u e) =>
 u a e -> from o a -> u o e
ha x = yai @from @(AR) @u x

ha_ = ha
ha__ = ha
ha___ = ha
ha____ = ha
ha_____ = ha
ha______ = ha
ha_______ = ha
ha________ = ha

ha'he, ha_'he, ha__'he, ha___'he, ha____'he, ha_____'he, ha______'he, ha_______'he, ha________'he :: forall from u e a o .
 Contravariant Yoneda Functor from (AR) (T'II'I u e) =>
 Wrapper from o =>
 u a e -> from (Supertype o) a -> u o e
ha'he x = yai @from @(AR) @u x `compose` fai (he @from)

ha_'he = ha'he
ha__'he = ha'he
ha___'he = ha'he
ha____'he = ha'he
ha_____'he = ha'he
ha______'he = ha'he
ha_______'he = ha'he
ha________'he = ha'he

ha'he'he, ha_'he'he, ha__'he'he, ha___'he'he, ha____'he'he, ha_____'he'he, ha______'he'he, ha_______'he'he, ha________'he'he
 :: forall from into u e a o .
 Contravariant Yoneda Functor from into (T'II'I u e) =>
 Contravariant Semi Functor from into (T'II'I from a) =>
 Wrapper from o =>
 (forall e . Wrapper into (T'II'I from a e)) =>
 -- Wrapper into (T'II'I from a o) =>
 Wrapper into (T'II'I u e o) =>
 -- Wrapper into (T'II'I from a (Supertype (Supertype o))) =>
 Wrapper from (Supertype o) =>
 u a e -> into (from (Supertype (Supertype o)) a) (u o e)
ha'he'he = fai @into (fai @from (he `compose` he)) `compose` yai @from @into @u

ha_'he'he = ha'he'he
ha__'he'he = ha'he'he
ha___'he'he = ha'he'he
ha____'he'he = ha'he'he
ha_____'he'he = ha'he'he
ha______'he'he = ha'he'he
ha_______'he'he = ha'he'he
ha________'he'he = ha'he'he

he'ha :: forall from into (u :: * -> * -> *) i a o .
 Contravariant Yoneda Functor from into (T'II'I u i) =>
 Contravariant Semi Functor into into (T'II'I u i) =>
 Wrapper into o =>
 (forall e ee . Wrapper into (T'II'I from e ee)) =>
 (forall e ee . Wrapper into (T'I'II u e ee)) =>
 (forall e ee . Wrapper into (T'II'I u e ee)) =>
 u a i -> into (from (Supertype o) a) (u o i)
he'ha x = fai @into he `compose` yai @from @into @u x

yvi, hv, hv_, hv__, hv___, hv____, hv_____, hv______, hv_______, hv________
 :: forall into i .
 Category into =>
 Terminal into =>
 into i i
yvi = identity

-- hu: t i a -> into (from Unit o) (t i o)
-- hv: t a i -> into (from o Void) (t o i)

hv = yvi
hv_ = yvi
hv__ = yvi
hv___ = yvi
hv____ = yvi
hv_____ = yvi
hv______ = yvi
hv_______ = yvi
hv________ = yvi

yvi'he, hv'he, hv_'he, hv__'he, hv___'he, hv____'he, hv_____'he, hv______'he, hv_______'he, hv________'he
 :: forall into a o .
 Category into =>
 Terminal into =>
 Wrapper into a =>
 into (Supertype a) o -> into a o
yvi'he = fai @into unwrap

hv'he = yvi'he
hv_'he = yvi'he
hv__'he = yvi'he
hv___'he = yvi'he
hv____'he = yvi'he
hv_____'he = yvi'he
hv______'he = yvi'he
hv_______'he = yvi'he
hv________'he = yvi'he

yvi'he'he, hv'he'he, hv_'he'he, hv__'he'he, hv___'he'he, hv____'he'he, hv_____'he'he, hv______'he'he, hv_______'he'he, hv________'he'he
 :: forall into a o .
 Category into =>
 Terminal into =>
 Wrapper into a =>
 Wrapper into (Supertype a) =>
 into (Supertype (Supertype a)) o -> into a o
yvi'he'he = fai @into (unwrap `compose` unwrap)

hv'he'he = yvi'he'he
hv_'he'he = yvi'he'he
hv__'he'he = yvi'he'he
hv___'he'he = yvi'he'he
hv____'he'he = yvi'he'he
hv_____'he'he = yvi'he'he
hv______'he'he = yvi'he'he
hv_______'he'he = yvi'he'he
hv________'he'he = yvi'he'he

he'yvi, he'hv, he'hv_, he'hv__, he'hv___, he'hv____, he'hv_____, he'hv______, he'hv_______, he'hv________
 :: forall into a o e .
 Category into =>
 Terminal into =>
 Wrapper (AR) e =>
 (Supertype e ~ into a o) =>
 e -> into a o
he'yvi = hv `compose` unwrap

he'hv = hv `compose` unwrap
he'hv_ = hv `compose` unwrap
he'hv__ = hv `compose` unwrap
he'hv___ = hv `compose` unwrap
he'hv____ = hv `compose` unwrap
he'hv_____ = hv `compose` unwrap
he'hv______ = hv `compose` unwrap
he'hv_______ = hv `compose` unwrap
he'hv________ = hv `compose` unwrap

he'he'yvi, he'he'hv, he'he'hv_, he'he'hv__, he'he'hv___, he'he'hv____, he'he'hv_____, he'he'hv______, he'he'hv_______, he'he'hv________
 :: forall into a o e .
 Category into =>
 Terminal into =>
 Wrapper (AR) e =>
 Wrapper (AR) (Supertype e) =>
 (Supertype (Supertype e) ~ into a o) =>
 e -> into a o
he'he'yvi = hv `compose` unwrap `compose` unwrap

he'he'hv = hv `compose` unwrap `compose` unwrap
he'he'hv_ = hv `compose` unwrap `compose` unwrap
he'he'hv__ = hv `compose` unwrap `compose` unwrap
he'he'hv___ = hv `compose` unwrap `compose` unwrap
he'he'hv____ = hv `compose` unwrap `compose` unwrap
he'he'hv_____ = hv `compose` unwrap `compose` unwrap
he'he'hv______ = hv `compose` unwrap `compose` unwrap
he'he'hv_______ = hv `compose` unwrap `compose` unwrap
he'he'hv________ = hv `compose` unwrap `compose` unwrap

-- he'ho: u (Supertype i) a -> into (from a o) (u i o)
-- ho'he: u i a -> into (from (Supertype a) o) (u i o)

-- he'ho: u (Supertype i) a -> into (from a o) (u i o)
-- ho'he: u i a -> into (from (Supertype a) o) (u i o)
-- ha'he: u a i -> into (from (Supertype o) a) (u o i)

-- ha_ha :: forall from u uu a o e ee .
--  Contravariant Yoneda Functor u (AR) (T'II'I u e) =>
--  Contravariant Semi Functor from u (T'II'I uu ee) =>
--  Contravariant Semi Functor u u (T'II'I uu ee) =>
--  Wrapper u (T'II'I uu ee (Supertype a)) =>
--  Wrapper u (T'II'I uu ee o) =>
--  Wrapper u (T'II'I uu ee a) =>
--  Wrapper u a =>
--  Wrapper from a =>
--  u (uu a ee) e -> from (Supertype a) o -> u (uu o ee) e
-- ha_ha x = fai @(AR) @(AR) fai_ (ha @u x)

-- ha'ho :: forall from u uu o i ii a .
--  Covariant Yoneda Functor u (AR) (T'I'II u i) =>
--  Contravariant Yoneda Functor u (AR) (T'II'I u i) =>
--  Covariant Semi Functor from u (T'I'II uu ii) =>
--  (forall e ee . Wrapper u (T'I'II uu e ee)) =>
--  u (uu ii o) i -> from a o -> u (uu ii a) i
-- ha'ho x = fai @(AR) @(AR) fio (ha @u x)

-- ha'ho'hu :: forall from into u uu u__ o e ee eee a .
 -- Precategory from =>
 -- Contravariant Yoneda Functor u__ (AR) (T'II'I u e) =>
 -- Covariant Semi Functor from u__ (T'I'II uu ee) =>
 -- Covariant Endo Semi Functor from (T'I'II u__ eee) =>
 -- Mapping T'I'II T'I'II into into I (T'I'II into a) =>
 -- Wrapper u__ (T'I'II uu ee (u__ eee a)) =>
 -- Wrapper u__ (T'I'II uu ee (u__ eee o)) =>
 -- Wrapper from (T'I'II u__ eee o) =>
 -- Wrapper from (T'I'II u__ eee a) =>
 -- Wrapper (AR) (U_1_I from a o) =>
 -- u (uu ee (u__ eee o)) e -> Supertype (U_1_I from a o) -> u (uu ee (u__ eee a)) e
-- ha'ho'hu = fai (fio @from `compose` fiu) `compose` ha @u__

-- ha'hu, ha_'hu, ha__'hu, ha___'hu, ha____'hu, ha_____'hu, ha______'hu, ha_______'hu, ha________'hu :: forall u uu o e ee a .
 -- Terminal u =>
 -- Covariant Semi Functor u u (T'I'II uu ee) =>
 -- Constant Semi Functor u u (T'I'II uu ee) =>
 -- Contravariant Yoneda Functor u (AR) (T'II'I u e) =>
 -- Wrapper u (T'I'II uu ee a) =>
 -- Wrapper u (T'I'II uu ee o) =>
 -- Elicitable T'II'I u (U_1_I u a o) =>
 -- Elicitable T'II'I (AR) (U_1_I u a o) =>
 -- u (uu ee o) e -> u Unit o -> u (uu ee a) e
-- ha'hu x = fai @(AR) @(AR) fiu (ha @u x)

-- ha'he'hu :: forall from u uu o e ee a .
 -- Covariant Semi Functor u u (T'I'II uu ee) =>
 -- Constant Semi Functor u u (T'I'II uu ee) (T'I'II uu ee) =>
 -- Contravariant Yoneda Functor u (AR) (T'II'I u e) =>
 -- Wrapper u (T'I'II uu ee a) =>
 -- Wrapper u (T'I'II uu ee o) =>
 -- Elicitable T'II'I (AR) (u () o) =>
 -- u (uu ee o) e -> Supertype (u () o) -> u (uu ee a) e
-- ha'he'hu x = fai @(AR) @(AR) fiu (ha'he @u x)

ha'hu, ha_'hu, ha__'hu, ha___'hu, ha____'hu, ha_____'hu, ha______'hu, ha_______'hu, ha________'hu
 :: forall u uu o i ii a .
 Terminal u =>
 Covariant Semi Functor u u (T'I'II uu ii) =>
 Constant Semi Functor u u (T'I'II uu ii) =>
 Contravariant Yoneda Functor u (AR) (T'II'I u i) =>
 (forall e ee . Wrapper u (T'I'II uu e ee)) =>
 Wrapper (AR) (u Unit o) =>
 u (uu ii o) i -> Supertype (u Unit o) -> u (uu ii a) i
ha'hu x = fai @(AR) @(AR) (fiu @u) (ha @u x)

ha_'hu = ha'hu
ha__'hu = ha'hu
ha___'hu = ha'hu
ha____'hu = ha'hu
ha_____'hu = ha'hu
ha______'hu = ha'hu
ha_______'hu = ha'hu
ha________'hu = ha'hu

-- ha'yo :: forall from u t o e a .
--  Covariant Yoneda Functor from (AR) (T'I'II u e) =>
--  Contravariant Yoneda Functor from (AR) (T'II'I u e) =>
--  Covariant Endo Semi Functor from t =>
--  Constant Semi Functor from (AR) t =>
--  u (t a) e -> from o a -> u (t o) e
-- ha'yo x = fai (fo @from) (ha @from x)

ha'yioi :: forall from u t o e ee eee a .
 Covariant Yoneda Functor from (AR) (T'I'II u e) =>
 Contravariant Yoneda Functor from (AR) (T'II'I u e) =>
 Covariant Endo Semi Functor from (W_III_I_II t eee ee) =>
 Wrapper from (W_III_I_II t eee ee a) =>
 Wrapper from (W_III_I_II t eee ee o) =>
 u (t ee a eee) e -> from o a -> u (t ee o eee) e
ha'yioi x = fai (fioi @from) (ha @from x)

-- -- TODO: replace with `ho_`
-- ho_yi :: forall from u e a o .
--  Covariant Endo Semi Functor from (T'I'II from a) =>
--  Covariant Yoneda Functor from (AR) (T'I'II u e) =>
--  Contravariant Semi Functor from (AR) (T'II'I (AR) (u e (Supertype o))) =>
--  Contravariant Yoneda Functor from (AR) (T'II'I (AR) (u e (Supertype o))) =>
--  Elicitable T'I'II (AR) (T'I'II u e o) =>
--  Elicitable T'I'II from o =>
--  Wrapper from (T'I'II from a o) =>
--  Wrapper from (T'I'II from a (Supertype o)) =>
--  u e a -> from a o -> u e (Supertype o)
-- ho_yi x = fai @from (fio @from he) (ho x)

-- -- TODO: replace with `ho_ho`
-- ho_yi'ho :: forall from u e a o .
--  Covariant Yoneda Functor from (AR) (T'I'II u e) =>
--  Elicitable T'I'II from a =>
--  u e a -> from (Supertype a) o -> u e o
-- ho_yi'ho x xx = x `ho` he @from `ho` xx

-- hu, hu_, hu__, hu___, hu____, hu_____, hu______, hu_______, hu________ ::
 -- forall into t i a o .
 -- Covariant Yoneda Functor into into (T'I'II t i) =>
 -- Mapping T'I'II T'I'II into into I (T'I'II into a) =>
 -- Wrapper into (T'I'II into a o) =>
 -- Wrapper into (T'I'II t i o) =>
 -- Wrapper into (I o) =>
 -- t i a -> into o (t i o)
-- hu = yiu

-- hu, hu_, hu__, hu___, hu____, hu_____, hu______, hu_______, hu________ ::
 -- forall from into t i a o .
 -- Terminal from =>
 -- Category from =>
 -- Covariant Yoneda Functor from into (T'I'II t i) =>
 -- Covariant Functor from into (T'I'II from a) =>
 -- Contravariant Functor from into (T'II'I from o) =>
 -- Wrapper into (T'I'II from a o) =>
 -- Wrapper into (T'II'I from o a) =>
 -- Wrapper into (T'II'I from o Unit) =>
 -- Wrapper into (T'I'II t i o) =>
 -- t i a -> into (from Unit o) (t i o)
-- hu x = yio @from x `compose` fai @from terminal

-- hu_ = hu
-- hu__ = hu
-- hu___ = hu
-- hu____ = hu
-- hu_____ = hu
-- hu______ = hu
-- hu_______ = hu
-- hu________ = hu

-- hu'he, hu_'he, hu__'he, hu___'he, hu____'he, hu_____'he, hu______'he, hu_______'he, hu________'he
--  :: forall from into a o .
--  Precategory into =>
--  Precategory from =>
--  Covariant Yoneda Functor from into (U_1_I from ()) =>
--  Contravariant Endo Semi Functor from (T'II'I from o) =>
--  Elicitable T'II'I into (T'I'II from a o) =>
--  Elicitable T'II'I into (U_1_I from a o) =>
--  Elicitable T'I'II into (U_1_I from a o) =>
--  Elicitable T'I'II from a =>
--  Wrapper from (T'II'I from o a) =>
--  Wrapper from (T'II'I from o (Supertype a)) =>
--  Elicitable T'I'II into (T'I'II from a o) =>
--  Elicitable T'I'II into (U_1_I from a o) =>
--  Contravariant Yoneda Functor from (AR) (T'II'I into (Supertype (U_1_I from a o))) =>
--  Supertype (U_1_I from a o) -> into (from (Supertype a) o) (Supertype (U_1_I from a o))
-- hu'he x = hu @from @into @a x `yai'yai` he @from @a
-- hu_'he x = hu @from @into @a x `yai'yai` he @from @a
-- hu__'he x = hu @from @into @a x `yai'yai` he @from @a
-- hu___'he x = hu @from @into @a x `yai'yai` he @from @a
-- hu____'he x = hu @from @into @a x `yai'yai` he @from @a
-- hu_____'he x = hu @from @into @a x `yai'yai` he @from @a
-- hu______'he x = hu @from @into @a x `yai'yai` he @from @a
-- hu_______'he x = hu @from @into @a x `yai'yai` he @from @a
-- hu________'he x = hu @from @into @a x `yai'yai` he @from @a

-- hu_'he = hu'he
-- hu__'he = hu'he
-- hu___'he = hu'he
-- hu____'he = hu'he
-- hu_____'he = hu'he
-- hu______'he = hu'he
-- hu_______'he = hu'he
-- hu________'he = hu'he

-- hu'he'he, hu_'he'he, hu__'he'he, hu___'he'he, hu____'he'he, hu_____'he'he, hu______'he'he, hu_______'he'he, hu________'he'he
 -- :: forall from into a o .
 -- Precategory into =>
 -- Precategory from =>
 -- Covariant Yoneda Functor from into (U_1_I from a) =>
 -- Constant Yoneda Functor from into (U_1_I from a) =>
 -- Contravariant Endo Semi Functor from (T'II'I from o) =>
 -- Elicitable T'II'I into (T'I'II from a o) =>
 -- Elicitable T'II'I into (U_1_I from a a) =>
 -- Elicitable T'I'II into (U_1_I from a o) =>
 -- Elicitable T'I'II from a =>
 -- Elicitable T'I'II from (Supertype a) =>
 -- Wrapper from (T'II'I from o a) =>
 -- Wrapper from (T'II'I from o (Supertype (Supertype a))) =>
 -- Elicitable T'I'II into (T'I'II from a o) =>
 -- Wrapper into (U_1_I from a o) =>
 -- Contravariant Yoneda Functor from (AR) (T'II'I into (Supertype (U_1_I from a o))) =>
 -- a -> into (from (Supertype (Supertype a)) o) o
-- hu'he'he x = hu @from @into @a x `yai'yai` he'he @from @a
-- hu_'he'he x = hu @from @into @a x `yai'yai` he'he @from @a
-- hu__'he'he x = hu @from @into @a x `yai'yai` he'he @from @a
-- hu___'he'he x = hu @from @into @a x `yai'yai` he'he @from @a
-- hu____'he'he x = hu @from @into @a x `yai'yai` he'he @from @a
-- hu_____'he'he x = hu @from @into @a x `yai'yai` he'he @from @a
-- hu______'he'he x = hu @from @into @a x `yai'yai` he'he @from @a
-- hu_______'he'he x = hu @from @into @a x `yai'yai` he'he @from @a
-- hu________'he'he x = hu @from @into @a x `yai'yai` he'he @from @a

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
 Elicitable T'I'II into (T'I'II hom (Representation t) i) =>
 into (t i) (hom (Representation t) i)
ro = he `compose` map @T'I'II @T'I'II @into @into @t @(T'I'II hom (Representation t)) identity

ra :: forall into hom t i .
 Category into =>
 Contravariant (Representable hom) into into t =>
 Elicitable T'I'II into (T'II'I hom (Representation t) i) =>
 into (t i) (hom i (Representation t))
ra = he `compose` map @T'II'I @T'I'II @into @into @t @(T'II'I hom (Representation t)) identity

-- TODO: it should be renamed since `hj` is used instead of `hd`
lu'q, lu_'q, lu__'q, lu___'q, lu____'q, lu_____'q, lu______'q, lu_______'q, lu________'q
 :: forall into a .
 Adjoint Functor into into (T'II'I (P) a) (T'I'II into a) =>
 (forall e . Wrapper into ((T'I'II into a `T'TT'I` T'II'I (P) a) e)) =>
 (forall e . Wrapper into (T'II'I (P) a e)) =>
 (forall e . Wrapper into (T'I'II into a e)) =>
 Elicitable T'II'I into (I a) =>
 Setoid into a =>
 into a (into a (a `P` a `S` a))
lu'q = fij @into @into @(P) @into q

lu_'q = lu'q
lu__'q = lu'q
lu___'q = lu'q
lu____'q = lu'q
lu_____'q = lu'q
lu______'q = lu'q
lu_______'q = lu'q
lu________'q = lu'q

lu's, lu_'s, lu__'s, lu___'s, lu____'s, lu_____'s, lu______'s, lu_______'s, lu________'s
 :: forall into a .
 Adjoint Functor into into (T'II'I (P) a) (T'I'II into a) =>
 (forall e . Wrapper into ((T'I'II into a `T'TT'I` T'II'I (P) a) e)) =>
 (forall e . Wrapper into (T'II'I (P) a e)) =>
 (forall e . Wrapper into (T'I'II into a e)) =>
 Elicitable T'II'I into (I a) =>
 Semigroup into a =>
 into a (into a a)
lu's = fij @into @into @(P) @into s

lu_'s = lu's
lu__'s = lu's
lu___'s = lu's
lu____'s = lu's
lu_____'s = lu's
lu______'s = lu's
lu_______'s = lu's
lu________'s = lu's

-- hj'hj :: forall from into t tt ttt tttt i ii a o .
 -- Category into =>
-- hj'hj :: forall from into t tt ttt tttt i ii a o .
 -- Category into =>
 -- Adjoint Functor from from (T'II'I t ii) (T'I'II tttt ii) =>
 -- Adjoint Functor from from (T'II'I ttt i) (T'I'II tt i) =>
 -- Covariant Functor into from (T'II'I ttt i) =>
 -- Covariant Functor from from (T'I'II tt i) =>
 -- Wrapper from (T'II'I t ii a) =>
 -- Wrapper into (T'I'II tt i o) =>
 -- Wrapper into (T'I'II tt i (tttt ii o)) =>
 -- Wrapper from (I o) =>
 -- Wrapper from (I (tttt ii o)) =>
 -- Wrapper from (I (T'I'II tttt ii o)) =>
 -- Wrapper from (T'II'I ttt i a) =>
 -- Wrapper from (T'I'II tttt ii o) =>
 -- Wrapper from (T'II'I t ii (ttt a i)) =>
 -- Wrapper from ((T'TT'I (T'II'I ttt i) (T'I'II tt i)) (tttt ii o)) =>
 -- Wrapper from ((T'TT'I (T'II'I t ii) (T'I'II tttt ii)) o) =>
 -- (forall e . Wrapper from (T'II'I ttt i `T'TT'I` T'I'II tt i `T'I_` e)) =>
 -- (forall e . Wrapper from (T'I'II tt i `T'TT'I` T'II'I ttt i `T'I_` e)) =>
 -- a -> from (from (into (from _ o) (tt ii (t o i))) _) (tt ii (t o i))
-- hj'hj = hj @from @from `compose` hj @from @into

-- TODO: it shouldn't exist by itself
he, he_, he__, he___, he____, he_____, he______, he_______, he________ :: forall into e .
 Elicitable T'I'II into e =>
 into e (Supertype e)
he = unwrap

he_ = he
he__ = he
he___ = he
he____ = he
he_____ = he
he______ = he
he_______ = he
he________ = he

he'he, he_'he, he__'he, he___'he, he____'he, he_____'he, he______'he, he_______'he, he________'he
 :: forall into e .
 Precategory into =>
 Elicitable T'I'II into e =>
 Elicitable T'I'II into (Supertype e) =>
 into e (Supertype (Supertype e))
he'he = unwrap `compose` unwrap

he_'he = he'he
he__'he = he'he
he___'he = he'he
he____'he = he'he
he_____'he = he'he
he______'he = he'he
he_______'he = he'he
he________'he = he'he

-- TODO: remove
he'he'he, he_'he'he, he__'he'he, he___'he'he, he____'he'he, he_____'he'he, he______'he'he, he_______'he'he, he________'he'he :: forall into e .
 Precategory into =>
 Elicitable T'I'II into e =>
 Elicitable T'I'II into (Supertype e) =>
 Elicitable T'I'II into (Supertype (Supertype e)) =>
 into e (Supertype (Supertype (Supertype e)))
he'he'he = unwrap `compose` unwrap `compose` unwrap

he_'he'he = he'he'he
he__'he'he = he'he'he
he___'he'he = he'he'he
he____'he'he = he'he'he
he_____'he'he = he'he'he
he______'he'he = he'he'he
he_______'he'he = he'he'he
he________'he'he = he'he'he

he'he'he'he, he_'he'he'he, he__'he'he'he, he___'he'he'he, he____'he'he'he, he_____'he'he'he, he______'he'he'he, he_______'he'he'he, he________'he'he'he :: forall into e .
 Precategory into =>
 Elicitable T'I'II into e =>
 Elicitable T'I'II into (Supertype e) =>
 Elicitable T'I'II into (Supertype (Supertype e)) =>
 Elicitable T'I'II into (Supertype (Supertype (Supertype e))) =>
 into e (Supertype (Supertype (Supertype (Supertype e))))
he'he'he'he = unwrap `compose` unwrap `compose` unwrap `compose` unwrap

he_'he'he'he = he'he'he'he
he__'he'he'he = he'he'he'he
he___'he'he'he = he'he'he'he
he____'he'he'he = he'he'he'he
he_____'he'he'he = he'he'he'he
he______'he'he'he = he'he'he'he
he_______'he'he'he = he'he'he'he
he________'he'he'he = he'he'he'he

he'ya :: forall from into t a o e .
 Precategory into =>
 (Supertype e ~ t a) =>
 Contravariant Yoneda Functor from into t =>
 Wrapper into (T'II'I from a o) =>
 Wrapper (AR) e =>
 e -> into (from o a) (t o)
he'ya = ya @from @into `compose` unwrap

he'yo :: forall from into t a o e .
 Precategory into =>
 (Supertype e ~ t a) =>
 Covariant Yoneda Functor from into t =>
 (forall e ee . Wrapper into (T'I'II from e ee)) =>
 Wrapper (AR) e =>
 e -> into (from a o) (t o)
he'yo = yo @from @into `compose` unwrap

he'yu :: forall into t a o e .
 Precategory into =>
 Covariant Yoneda Functor into into t =>
 Mapping T'I'II T'I'II (AR) (AR) t t =>
 Mapping T'I'II T'I'II into into I (T'I'II into a) =>
 Wrapper into (T'I'II into a o) =>
 Wrapper (AR) (into () o) =>
 Wrapper into (into () o) =>
 Elicitable T'II'I into (T'I'II into () o) =>
 Wrapper into (I o) =>
 Wrapper (AR) e =>
 t a -> into o (t o)
he'yu = yu @into

lo, lo_, lo__, lo___, lo____, lo_____, lo______, lo_______
 :: forall into r a o oo .
 Category into =>
 Limit T'I'II into into =>
 Objective into r (o `P` oo) =>
 Covariant Endo Semi Functor into (T'I'II Product a) =>
 Covariant Endo Semi Functor into (T'II'I Product oo) =>
 (forall e ee . Wrapper into (T'I'II Product e ee)) =>
 (forall e ee . Wrapper into (T'II'I Product e ee)) =>
 (forall e . Wrapper into (Both Product e)) =>
 (forall e . Wrapper into (I e)) =>
 into a o -> into a oo -> into a r
lo l r = objective @into @_ @(o `P` oo)
 `compose` foi @into @into l `compose` fio @into @into r
 `compose` wrapped (map @T'II'I @T'II'I @into @into @(Both Product) @I identity)

lo_ = lo
lo__ = lo
lo___ = lo
lo____ = lo
lo_____ = lo
lo______ = lo
lo_______ = lo

-- TODO: define longer versions of this operator
lo'lu :: forall into a aa o oo .
 Category into =>
 Limit T'I'II into into =>
 Covariant Endo Semi Functor into (T'I'II (P) (a `P` aa)) =>
 Covariant Endo Semi Functor into (T'II'I (P) oo) =>
 (forall e ee . Wrapper into (T'I'II (P) e ee)) =>
 (forall e ee . Wrapper into (T'II'I (P) e ee)) =>
 (forall e . Wrapper into (Both (P) e)) =>
 (forall e . Wrapper into (I e)) =>
 into a o -> into aa oo -> into (a `P` aa) (o `P` oo)
lo'lu l r = lo
 (l `compose` (wrapped (left @T'I'II @into identity)))
 (r `compose` (wrapped (right @T'I'II @into identity)))

lo'yp, lo_'yp, lo__'yp, lo___'yp, lo____'yp, lo_____'yp, lo______'yp, lo_______'yp
 :: forall t tt l a o oo .
 Mapping T'I'II T'I'II (AR) (AR) (Day T'I'II (AR) (P) P t (l `L` tt) o oo) t =>
 Arrow a (t o) -> Arrow a ((l `L` tt) oo) -> Arrow a (t (Product o oo))
lo'yp l r = yp `compose` lo @(AR) @(t o `P` (l `L` tt) oo) l r

lo_'yp = lo'yp
lo__'yp = lo'yp
lo___'yp = lo'yp
lo____'yp = lo'yp
lo_____'yp = lo'yp
lo______'yp = lo'yp
lo_______'yp = lo'yp

lo'ys, lo_'ys, lo__'ys, lo___'ys, lo____'ys, lo_____'ys, lo______'ys, lo_______'ys
 :: forall t tt l a o oo .
 Mapping T'I'II T'I'II (AR) (AR) (Day T'I'II (AR) (P) (S) t (l `L` tt) o oo) t =>
 Arrow a (t o) -> Arrow a ((l `L` tt) oo) -> Arrow a (t (Sum o oo))
lo'ys l r = ys `compose` lo @(AR) @(t o `P` (l `L` tt) oo) l r

lo_'ys = lo'ys
lo__'ys = lo'ys
lo___'ys = lo'ys
lo____'ys = lo'ys
lo_____'ys = lo'ys
lo______'ys = lo'ys
lo_______'ys = lo'ys

lo'ys'la, lo_'ys'la, lo__'ys'la, lo___'ys'la, lo____'ys'la, lo_____'ys'la, lo______'ys'la, lo_______'ys'la
 :: forall t tt l a o .
 Mapping T'I'II T'I'II (AR) (AR) (Day T'I'II (AR) (P) (S) t (l `L` tt) o o) t =>
 Arrow a (t o) -> Arrow a ((l `L` tt) o) -> Arrow a (t o)
lo'ys'la l r = (\x -> ys'yo x (identity @(AR) `la` identity)) `compose` lo @(AR) @(_ `P` _) l r

lo_'ys'la = lo'ys'la
lo__'ys'la = lo'ys'la
lo___'ys'la = lo'ys'la
lo____'ys'la = lo'ys'la
lo_____'ys'la = lo'ys'la
lo______'ys'la = lo'ys'la
lo_______'ys'la = lo'ys'la

lu'ys'la, lu_'ys'la, lu__'ys'la, lu___'ys'la, lu____'ys'la, lu_____'ys'la, lu______'ys'la, lu_______'ys'la
 :: forall t tt l a o .
 Mapping T'I'II T'I'II (AR) (AR) (Day T'I'II (AR) (P) (S) t (l `L` tt) o o) t =>
 Covariant Yoneda Functor (AR) (AR) (T'I'II Product (t o)) =>
 Covariant Yoneda Functor (AR) (AR) (T'II'I Product ()) =>
 t o -> (l `L` tt) o -> (t o)
lu'ys'la l r = ys'yo (lu l r) (identity @(AR) `la` identity)

lu_'ys'la = lu'ys'la
lu__'ys'la = lu'ys'la
lu___'ys'la = lu'ys'la
lu____'ys'la = lu'ys'la
lu_____'ys'la = lu'ys'la
lu______'ys'la = lu'ys'la
lu_______'ys'la = lu'ys'la

-- x `lo'la` y

-- into a o -> into a oo -> into a (Product o oo)

-- cn :: forall into a aa o oo .
 -- Cone T'I'II into into Product =>
 -- Functor T'I'II into into (T'I'II Product o) =>
 -- Functor T'I'II into into (T'I'II Product aa) =>
 -- Functor T'I'II into into (T'II'I Product aa) =>
 -- Wrapper into (T'I'II Product o aa) =>
 -- Wrapper into (T'I'II Product o oo) =>
 -- Wrapper into (T'II'I Product aa o) =>
 -- Wrapper into (T'II'I Product aa a) =>
 -- (forall e . Wrapper into (T'II'I Product aa e)) =>
 -- into a o -> into aa oo -> into (Product a aa) (Product o oo)
-- cn l r = fio r `compose` foi l

-- into a o -> into a oo -> into a (Product into o oo)

-- cnz :: forall into e a aa o oo .
 -- Cone T'I'II into into (Object T'I'II into) =>
 -- Functor T'I'II into into (T'I'II (Product into) o) =>
 -- Functor T'I'II into into (T'I'II (Product into) aa) =>
 -- Functor T'I'II into into (T'II'I (Product into) aa) =>
 -- Wrapper into (T'I'II (Product into) o aa) =>
 -- Wrapper into (T'I'II (Product into) o oo) =>
 -- Wrapper into (T'II'I (Product into) aa o) =>
 -- Wrapper into (T'II'I (Product into) aa a) =>
 -- Elicitable T'I'II into e =>
 -- (Supertype e ~ (Product into a aa)) =>
 -- into a o -> into aa oo -> into e (Product into o oo)
-- cnz l r = fio r `compose` foi l `compose` _' @into

-- TODO: try to generalize
-- cn'yp, yi'cn'yp :: forall t a aa o oo .
 -- Mapping T'I'II T'I'II (AR) (AR) (Day T'I'II (AR) (Product (AR)) (Product (AR)) t t o oo) t =>
 -- Arrow a (t o) -> Arrow aa (t oo) -> Arrow (Product (AR) a aa) (t (Product Arrow o oo))
-- cn'yp l r = yp `compose` cn l r

-- yi'cn'yp = cn'yp

-- TODO: try to generalize
-- cnz'yp, yi'cnz'yp :: forall e t a aa o oo .
--  Mapping T'I'II T'I'II (AR) (AR) (Day T'I'II (AR) (Product (AR)) (Product (AR)) t t o oo) t =>
--  Elicitable T'I'II (AR) e =>
--  (Supertype e ~ Product (AR) a aa) =>
--  Arrow a (t o) -> Arrow aa (t oo) -> Arrow e (t (Product Arrow o oo))
-- cnz'yp l r = yp `compose` cn l r `compose` he

-- yi'cnz'yp = cnz'yp

-- TODO: try to generalize
-- lu, lu_, lu__, lu___, lu____, lu_____, lu______, lu_______ :: forall o oo .
--  Limit T'I'II (AR) (AR) =>
--  Covariant Functor (AR) (AR) (T'I'II (Product (AR)) o) =>
--  Covariant Functor (AR) (AR) (T'II'I (Product (AR)) (Product (AR) () ())) =>
--  Elicitable T'I'II (AR) (Both (Product (AR)) (Product (AR) () ())) =>
--  Elicitable T'I'II (AR) (T'I'II (Product (AR)) o oo) =>
--  Elicitable T'II'I (AR) (T'II'I (Product (AR)) () ()) =>
--  Elicitable T'II'I (AR) (T'I'II (Product (AR)) () ()) =>
--  Elicitable T'I'II (AR) (Both (Product (AR)) ()) =>
--  Elicitable T'I'II (AR) (T'II'I (Product (AR)) (Product (AR) () ()) o) =>
--  Elicitable T'II'I (AR) (T'II'I (Product (AR)) (Product (AR) () ()) (Product (AR) () ())) =>
--  Wrapper (AR) (T'I'II (Product (AR)) o (Product (AR) () ())) =>
--  (forall e . Wrapper (AR) (I e)) =>
--  Elicitable T'II'I (AR) (U_1_I (AR) () o) =>
--  Elicitable T'II'I (AR) (U_1_I (AR) () oo) =>
--  Elicitable T'I'II (AR) (U_1_I (AR) () (Product (AR) o oo)) =>
--  Supertype (U_1_I (AR) () o) ->
--  Supertype (U_1_I (AR) () oo) ->
--  Supertype (U_1_I (AR) () (Product (AR) o oo))
-- lu l r = -- he /
--  -- __ (map @T'I'II @T'I'II (wrapped (right @T'I'II (wrap @_ @(U_1_I (AR) () oo) r)))) `compose`
--  -- i_ (map @T'I'II @T'I'II (wrapped (left @T'I'II (wrap @_ @(U_1_I (AR) () o) l)))) `compose`
--  -- wrapped (map @T'I'II @T'I'II @(AR) @(AR) @I @(Both (Product (AR))) identity) `compose`
--  -- wrapped (map @T'I'II @T'I'II @(AR) @(AR) @I @(Both (Product (AR))) identity)

--  __ (map @U_1_I @T'I'II (wrapped (right @T'I'II r))) `compose`
--  i_ (map @U_1_I @T'I'II (wrapped (left @T'I'II l))) `compose`
 -- wrapped (map @U_1_I @T'I'II @(AR) @(AR) @I @(Both (Product (AR))) identity) `compose`
 -- wrapped (map @U_1_I @T'I'II @(AR) @(AR) @I @(Both (Product (AR))) identity)

lu, lu_, lu__, lu___, lu____, lu_____, lu______, lu_______ :: forall o oo .
 Limit T'I'II (AR) (AR) =>
 Mapping T'I'II T'I'II (AR) (AR) I (T'I'I Product) =>
 Covariant Yoneda Functor (AR) (AR) (T'I'II Product o) =>
 Covariant Yoneda Functor (AR) (AR) (T'II'I Product ()) =>
 Wrapper (AR) (T'I'I Product ()) =>
 Wrapper (AR) (I ()) =>
 o -> oo -> Product o oo
lu l r = wrapped (map @T'I'II @T'I'II @(AR) @(AR) @I @(T'I'I Product) identity) () `yui` l `yiu` r

lu_ = lu
lu__ = lu
lu___ = lu
lu____ = lu
lu_____ = lu
lu______ = lu
lu_______ = lu

-- ho'lu :: forall o oo .
 -- Limit T'I'II (AR) (AR) =>
 -- Mapping T'I'II T'I'II (AR) (AR) I (T'I'I Product) =>
 -- Covariant Yoneda Functor (AR) (AR) (T'I'II Product o) =>
 -- Covariant Yoneda Functor (AR) (AR) (T'II'I Product ()) =>
 -- Wrapper (AR) (T'I'I Product ()) =>
 -- Wrapper (AR) (I ()) =>
 -- from e o -> from e oo -> Product o oo
-- ho'lu l r = wrapped (map @T'I'II @T'I'II @(AR) @(AR) @I @(T'I'I Product) identity) () `yui` l `yiu` r

la, la_, la__, la___, la____, la_____, la______, la_______ :: forall from i a o oo .
 Category from =>
 Limit T'II'I from from =>
 Objective from (o `S` oo) a =>
 Covariant Endo Semi Functor from (T'I'II Sum o) =>
 Covariant Endo Semi Functor from (T'II'I Sum i) =>
 (forall ee eee . Wrapper from (T'I'II Sum ee eee)) =>
 (forall ee eee . Wrapper from (T'II'I Sum ee eee)) =>
 (forall ee . Wrapper from (T'I'I Sum ee)) =>
 (forall ee . Wrapper from (I ee)) =>
 from o i -> from oo i -> from a i
la l r = wrapped (map @T'II'I @T'II'I @from @from @I @(Both Sum) identity)
 `compose` foi @from @from l
 `compose` fio @from @from r
 `compose` objective @_ @(o `S` oo)

la_ = la
la__ = la
la___ = la
la____ = la
la_____ = la
la______ = la
la_______ = la

lv, lv_, lv__, lv___, lv____, lv_____, lv______, lv_______
 :: forall a aa aaa o .
 Covariant Endo Semi Functor (AR) (T'I'II Sum aa) =>
 Covariant Endo Semi Functor (AR) (T'II'I Sum o) =>
 Objective (AR) (aa `S` aaa) a =>
 (forall ee eee . Wrapper (AR) (T'I'II Sum ee eee)) =>
 (forall ee eee . Wrapper (AR) (T'II'I Sum ee eee)) =>
 (forall ee . Wrapper (AR) (T'I'I Sum ee)) =>
 (forall ee . Wrapper (AR) (I ee)) =>
 Wrapper (AR) ((AR) Unit o) =>
 (Supertype ((AR) Unit o) ~ o) =>
 o -> o -> a -> o
lv l r = wrapped (map @T'II'I @T'II'I @(AR) @(AR) @I @(Both Sum) identity)
 `compose` fui @(AR) @(AR) l
 `compose` fiu @(AR) @(AR) r
 `compose` objective @(AR) @(aa `S` aaa) @a

lv_ l r = wrapped (map @T'II'I @T'II'I @(AR) @(AR) @I @(Both Sum) identity)
 `compose` fui @(AR) @(AR) l
 `compose` fiu @(AR) @(AR) r
 `compose` objective @(AR) @(aa `S` aaa) @a
lv__ l r = wrapped (map @T'II'I @T'II'I @(AR) @(AR) @I @(Both Sum) identity)
 `compose` fui @(AR) @(AR) l
 `compose` fiu @(AR) @(AR) r
 `compose` objective @(AR) @(aa `S` aaa) @a
lv___ l r = wrapped (map @T'II'I @T'II'I @(AR) @(AR) @I @(Both Sum) identity)
 `compose` fui @(AR) @(AR) l
 `compose` fiu @(AR) @(AR) r
 `compose` objective @(AR) @(aa `S` aaa) @a
lv____ l r = wrapped (map @T'II'I @T'II'I @(AR) @(AR) @I @(Both Sum) identity)
 `compose` fui @(AR) @(AR) l
 `compose` fiu @(AR) @(AR) r
 `compose` objective @(AR) @(aa `S` aaa) @a
lv_____ l r = wrapped (map @T'II'I @T'II'I @(AR) @(AR) @I @(Both Sum) identity)
 `compose` fui @(AR) @(AR) l
 `compose` fiu @(AR) @(AR) r
 `compose` objective @(AR) @(aa `S` aaa) @a
lv______ l r = wrapped (map @T'II'I @T'II'I @(AR) @(AR) @I @(Both Sum) identity)
 `compose` fui @(AR) @(AR) l
 `compose` fiu @(AR) @(AR) r
 `compose` objective @(AR) @(aa `S` aaa) @a
lv_______ l r = wrapped (map @T'II'I @T'II'I @(AR) @(AR) @I @(Both Sum) identity)
 `compose` fui @(AR) @(AR) l
 `compose` fiu @(AR) @(AR) r
 `compose` objective @(AR) @(aa `S` aaa) @a

-- `yp`: u (t e) (t ee) -> t (uu e ee)
-- `hs`: from o i -> from oo i -> from (o `S` oo) i
-- `lo`: into a o -> into a oo -> into a (o `P` oo)
--     : u (from o i) (from oo i) -> from (uu o oo) i

-- TODO: to test
-- rwr'hs :: forall from into r o a aa .
 -- Category from =>
 -- Limit T'II'I from into =>
 -- Covariant Functor into into (T'I'II Sum a) =>
 -- Covariant Functor into into (T'II'I Sum (Sum (Supertype r) (Supertype r))) =>
 -- Elicitable T'II'I into (Both Sum (Sum (Supertype r) (Supertype r))) =>
 -- Elicitable T'II'I into (T'I'II Sum a aa) =>
 -- Elicitable T'I'II into (T'I'II Sum (Supertype r) (Supertype r)) =>
 -- Elicitable T'I'II into (T'II'I Sum (Supertype r) (Supertype r)) =>
 -- Elicitable T'II'I into (Both Sum (Supertype r)) =>
 -- Elicitable T'I'II into (That Sum a (Sum (Supertype r) (Supertype r))) =>
 -- Elicitable T'II'I into (T'II'I Sum (Sum (Supertype r) (Supertype r)) a) =>
 -- Elicitable T'I'II into (T'II'I Sum (Sum (Supertype r) (Supertype r)) (Sum (Supertype r) (Supertype r))) =>
 -- (Supertype o ~ Sum a aa) =>
 -- (forall eee_ . Wrapper into (I eee_)) =>
 -- Elicitable T'II'I into r =>
 -- Elicitable T'I'II into o =>
 -- from a (Supertype r) -> from aa (Supertype r) -> into o r
-- rwr'hs l r = rwr /
 -- wrapped (map @T'II'I @T'II'I @from @into @I @(Both Sum) identity) `compose`
 -- wrapped (map @T'II'I @T'II'I @from @into @I @(Both Sum) identity) `compose`
 -- i_ (map @T'I'II @T'I'II (wrapped (left @T'II'I l))) `compose`
 -- __ (map @T'I'II @T'I'II (wrapped (right @T'II'I r)))

-- TODO: try to generalize
yp :: forall u e ee t tt l .
 Mapping T'I'II T'I'II (AR) (AR) (Day T'I'II (AR) u (P) t (l `L` tt) e ee) t =>
 -- Covariant Monoidal Functor (AR) (AR) u (P) l t =>
 u (t e) ((l `L` tt) ee) -> t (e `P` ee)
yp = day @T'I'II @(AR) @l @t @tt @u @(P) identity identity

-- TODO: try to generalize
yp'yo, yp_'yo :: forall e ee r t tt l .
 Mapping T'I'II T'I'II (AR) (AR) (Day T'I'II (AR) (P) P t (l `L` tt) e ee) t =>
 t e `P` (l `L` tt) ee -> (e `P` ee `AR` r) -> t r
yp'yo x f = day @T'I'II @(AR) @l @t @tt @(P) @P identity f x

yp_'yo = yp'yo

yp'yo'hd :: forall e ee r t tt l .
 Mapping T'I'II T'I'II (AR) (AR) (Day T'I'II (AR) (P) P t (l `L` tt) e ee) t =>
 t e `P` (l `L` tt) ee -> (e `AR_` ee `AR` r) -> t r
yp'yo'hd x f = day @T'I'II @(AR) @l @t @tt @(P) @P identity (fdi f) x

-- TODO: try to generalize
-- yip :: forall u e ee eee t .
 -- Covariant Endo Semi Functor (AR) (T'II'I u (t e eee)) =>
 -- Covariant Endo Semi Functor (AR) (T'I'II u (T'I'II t e ee)) =>
 -- Covariant Monoidal Functor (AR) (AR) u (P) (T'I'II t e) =>
 -- u (t e ee) (t e eee) -> t e (ee `P` eee)
-- yip = unwrap @Arrow
 -- `compose` day @T'I'II @(AR) @(T'I'II t e) @u @(P) identity identity
 -- `compose` fio @Arrow wrap `compose` foi @Arrow wrap

-- TODO: try to generalize
-- yip'yo :: forall u e ee eee t r .
 -- Covariant Endo Semi Functor (AR) (T'II'I u (t e eee)) =>
 -- Covariant Endo Semi Functor (AR) (T'I'II u (T'I'II t e ee)) =>
 -- Covariant Monoidal Functor (AR) (AR) u (P) (T'I'II t e) =>
 -- u (t e ee) (t e eee) -> (AR) (ee `P` eee) r -> t e r
-- yip'yo x f = unwrap @Arrow
 -- `compose` day @T'I'II @(AR) @(T'I'II t e) @u @(P) identity f
 -- `compose` fio @Arrow wrap `compose` foi @Arrow wrap
 -- `identity` x

-- TODO: try to generalize
yo'yp :: forall u e ee t tt ll .
 Covariant Endo Semi Functor (AR) t =>
 Mapping T'I'II T'I'II (AR) (AR) (Day T'I'II (AR) u (P) tt (ll `L` tt) e ee) tt =>
 t (u (tt e) ((ll `L` tt) ee)) -> t (tt (e `P` ee))
yo'yp = fo (day @T'I'II @(AR) @ll @tt @tt @u @(P) identity identity)

-- TODO: try to generalize
yio'yp :: forall u e ee eee t tt ll .
 Covariant Endo Semi Functor (AR) (T'I'II t eee) =>
 Mapping T'I'II T'I'II (AR) (AR) (Day T'I'II (AR) u (P) tt (ll `L` tt) e ee) tt =>
 t eee (u (tt e) ((ll `L` tt) ee)) -> t eee (tt (e `P` ee))
yio'yp = fio (day @T'I'II @(AR) @ll @tt @tt @u @(P) identity identity)

-- TODO: try to generalize
ys :: forall u e ee t tt l .
 Mapping T'I'II T'I'II (AR) (AR) (Day T'I'II (AR) u (S) t (l `L` tt) e ee) t =>
 u (t e) ((l `L` tt) ee) -> t (e `S` ee)
ys = day @T'I'II @(AR) @l @t @tt @u @(S) identity identity

-- TODO: try to generalize
ys'yo :: forall from t tt l e ee u r .
 Category from =>
 -- Covariant Monoidal Functor from (AR) u (S) l t =>
 Mapping T'I'II T'I'II from (AR) (Day T'I'II from u (S) t (l `L` tt) e ee) t =>
 u (t e) ((l `L` tt) ee) -> from (e `S` ee) r -> t r
ys'yo x f = day @T'I'II @from @l @t @tt @u @(S) identity f x

-- TODO: try to generalize
-- yis :: forall u e ee eee t .
 -- Covariant Endo Semi Functor (AR) (T'II'I u (t e eee)) =>
 -- Covariant Endo Semi Functor (AR) (T'I'II u (T'I'II t e ee)) =>
 -- Covariant Monoidal Functor (AR) (AR) u (S) (T'I'II t e) =>
 -- u (t e ee) (t e eee) -> t e (ee `S` eee)
-- yis = unwrap @Arrow
 -- `compose` day @T'I'II @(AR) @(T'I'II t e) @u @(S) identity identity
 -- `compose` fio @Arrow wrap `compose` foi @Arrow wrap

-- TODO: try to generalize
ysp :: forall u e ee t tt l .
 -- Covariant Monoidal Functor (AR) (AR) u (SP) l t =>
 Mapping T'I'II T'I'II (AR) (AR) (Day T'I'II (AR) u (SP) t (l `L` tt) e ee) t =>
 u (t e) ((l `L` tt) ee) -> t (e `S` ee `S_` e `P` ee)
ysp = day @T'I'II @(AR) @l @t @tt @u @(SP) identity he

-- TODO: try to generalize
yp'yp :: forall u e ee t tt ttt tttt l ll .
 -- Covariant Monoidal Functor (AR) (AR) u (P) l t =>
 -- Covariant Monoidal Functor (AR) (AR) (P) P ll tt =>
 Covariant Transformation Functor (AR) (AR) (Covariant Day (AR) u (P) t (l `L` ttt) (tt e) (L ll tttt ee)) t =>
 Covariant Transformation Functor (AR) (AR) (Covariant Day (AR) (P) P tt (ll `L` tttt) e ee) tt =>
 u (t (tt e)) ((l `L` ttt) (ll `L` tttt `T'I` ee)) -> t (tt (e `P` ee))
yp'yp = day @T'I'II @(AR) @l @t @ttt @u @(P) identity
 (day @T'I'II @(AR) @ll @tt @tttt @(P) @P identity identity)

-- TODO: generalize
yp'ys :: forall u e ee t tt l ll .
 Covariant Lax Monoidal Functor (AR) (AR) u (P) l t =>
 Covariant Lax Monoidal Functor (AR) (AR) (P) (S) ll tt =>
 u (t (tt e)) ((l `L` t) ((ll `L` tt) ee)) -> t (tt (e `S` ee))
yp'ys = day @T'I'II @(AR) @l @t @t @u @(P) identity
 (day @T'I'II @(AR) @ll @tt @tt @(P) @(S) identity identity)

-- yip'yp :: forall u e ee eee t tt .
 -- Covariant Endo Semi Functor (AR) (T'I'II t e) =>
 -- Covariant Endo Semi Functor (AR) (T'I'II u (T'I'II t e (tt ee))) =>
 -- Covariant Endo Semi Functor (AR) (T'II'I u (t e (tt eee))) =>
 -- Covariant Monoidal Functor (AR) (AR) (P) P tt =>
 -- Covariant Monoidal Functor (AR) (AR) u (P) (T'I'II t e) =>
 -- u (t e (tt ee)) (t e (tt eee)) -> t e (tt (ee `P` eee))
-- yip'yp x = yip'yo x yp

-- yip'yip :: forall u e ee eee eeee t tt .
 -- Covariant Endo Semi Functor (AR) (T'I'II t e) =>
 -- Covariant Endo Semi Functor (AR) (T'I'II u (T'I'II t e (tt ee eee))) =>
 -- Covariant Endo Semi Functor (AR) (T'II'I u (t e (tt ee eeee))) =>
 -- Covariant Monoidal Functor (AR) (AR) (P) P (T'I'II tt ee) =>
 -- Covariant Monoidal Functor (AR) (AR) u (P) (T'I'II t e) =>
 -- u (t e (tt ee eee)) (t e (tt ee eeee)) -> t e (tt ee (eee `P` eeee))
-- yip'yip x = yip'yo x yip

-- yip'yis :: forall u e ee eee eeee t tt .
 -- Covariant Endo Semi Functor (AR) (T'I'II t e) =>
 -- Covariant Endo Semi Functor (AR) (T'I'II u (T'I'II t e (tt ee eee))) =>
 -- Covariant Endo Semi Functor (AR) (T'II'I u (t e (tt ee eeee))) =>
 -- Covariant Monoidal Functor (AR) (AR) u (P) (T'I'II t e) =>
 -- Covariant Monoidal Functor (AR) (AR) (P) (S) (T'I'II tt ee) =>
 -- u (t e (tt ee eee)) (t e (tt ee eeee)) -> t e (tt ee (eee `S` eeee))
-- yip'yis x = yip'yo x yis

-- TODO: try to generalize
yp'yok :: forall i ii from into t tt ttt l ll o .
 Covariant Transformation Functor (AR) (AR) (Covariant Day (AR) (P) P t (l `L` ttt) i ii) t =>
 Covariant Endo Semi Functor into tt =>
 Covariant Endo Semi Functor into t =>
 Covariant Yoneda Functor from into t =>
 Covariant Endo Transformation Functor into (t `T'TT'I` ll `L` tt) t =>
 (forall e ee . Wrapper into (T'I'II from e ee)) =>
 (forall e . Wrapper into ((t `T'TT'I` ll `L` tt) e)) =>
 t i `P` (l `L` ttt) ii -> into (from (i `P` ii) ((ll `L` tt) o)) (t o)
yp'yok = yok @from @into `compose` yp

-- TODO: try to generalize
yp'yokl :: forall e ee from into t tt ttt l ll lll o .
 Covariant Endo Transformation Functor into (t `T'TT'I` ll `L` l `L` tt) (t `TT'T'I` tt) =>
 Covariant Transformation Functor (AR) (AR) (Covariant Day (AR) (P) P t (lll `L` ttt) e ee) t =>
 Covariant Yoneda Functor from into t =>
 Elicitable T'II'I into (T'I'II from (e `P` ee) (tt o)) =>
 (forall i . Wrapper into (T'TT'I t tt i)) =>
 (forall i . Wrapper into (TT'T'I t tt i)) =>
 (forall i . Wrapper into ((t `T'TT'I` L ll (L l tt)) i)) =>
 (forall e ee . Wrapper into (T'I'II from e ee)) =>
 t e `P` (lll `L` ttt) ee -> into (from (e `P` ee) (L ll (L l tt) o)) (tt (t o))
yp'yokl = yokl @from @into `compose` yp

-- TODO: try to generalize
yp'yp'yo :: forall from e ee r t tt ttt tttt l ll .
 Covariant Transformation Functor (AR) (AR) (Covariant Day (AR) (P) P t (l `L` ttt) (tt e) (L ll tttt ee)) t =>
 Covariant Transformation Functor from (AR) (Covariant Day from (P) P tt (ll `L` tttt) e ee) tt =>
 t (tt e) `P` (l `L` ttt) ((ll `L` tttt) ee) -> from (e `P` ee) r -> t (tt r)
yp'yp'yo x f = day @T'I'II @(AR) @l @t @ttt @(P) @P identity
 (day @T'I'II @from @ll @tt @tttt @(P) @P identity f) x

-- w'rw :: forall into a o
 -- Precategory into =>
 -- Elicitable T'II'I into o =>
 -- Elicitable T'I'II into a =>
 -- into (Supertype a) (Supertype o) -> into a o
-- w'rw into = wrap @into `compose` into `compose` he @into

-- rw'w :: forall into a o .
 -- Precategory into =>
 -- Elicitable T'II'I into a =>
 -- Elicitable T'I'II into o =>
 -- into a o -> into (Supertype a) (Supertype o)
-- rw'w into = _' @into `compose` into `compose` wrap @into

-- yi__, yi___, yi____, yi_____, yi______ :: forall into a .
 -- Precategory into =>
 -- Elicitable T'I'II into a =>
 -- Elicitable T'I'II into (Supertype a) =>
 -- into a (Supertype (Supertype a))
-- yi__ = _' @into `compose` _' @into

-- yi___ = yi__
-- yi____ = yi__
-- yi_____ = yi__
-- yi______ = yi__

-- yi___, yi____, yi_____, yi______, yi_______ :: forall into a .
 -- Precategory into =>
 -- Elicitable T'I'II into a =>
 -- Elicitable T'I'II into (Supertype a) =>
 -- Elicitable T'I'II into (Supertype (Supertype a)) =>
 -- into a (Supertype (Supertype (Supertype a)))
-- yi___ = _' @into `compose` _' @into `compose` _' @into

-- yi____ = yi___
-- yi_____ = yi___
-- yi______ = yi___
-- yi_______ = yi___

-- TODO: it's wrong, we ne_d to rewrite it
-- he'he'he'ho :: forall a e o oo .
--  Elicitable T'I'II (AR) a =>
--  Elicitable T'I'II (AR) (Supertype a) =>
--  Elicitable T'I'II (AR) (Supertype (Supertype a)) =>
--  ((e `ARR` o) ~ Supertype (Supertype (Supertype a))) =>
--  a `ARR` e `ARR` (o `ARR` oo) `ARR` oo
-- he'he'he'ho x e f = f (_' (_' (_' x)) e)

-- TODO: define `rw'o`
-- TODO: define `rw'rw'o`
-- TODO: define `rw'ha`
-- TODO: define `rw'rw'ha`
-- TODO: define `rw'rw'rw'ha`

yo'yok
 :: forall from into t tt ttt lll a o .
 Covariant Endo Semi Functor from tt =>
 Component from (tt `T'TT'I` lll `L` ttt) tt =>
 Covariant Yoneda Functor from into t =>
 Contravariant Endo Semi Functor (AR) (T'II'I into (t (tt o))) =>
 (forall e ee . Wrapper into (T'I'II from e ee)) =>
 (forall e . Wrapper from (tt `T'TT'I` lll `L` ttt `T'I_` e)) =>
 (t (tt a)) -> into (from (a) (lll `L` ttt `T'I` o)) (t (tt o))
yo'yok = fai (fok @from @from @tt @ttt) `compose` yo @from @into

ho'yok, ho_'yok, ho__'yok, ho___'yok, ho____'yok, ho_____'yok, ho______'yok, ho_______'yok, ho________'yok :: forall from u t tt l a o e .
 Covariant Endo Semi Functor from tt =>
 Covariant Endo Semi Functor from t =>
 Mapping T'I'II T'I'II from from (t `T'TT'I` L l tt) t =>
 Covariant Yoneda Functor from (AR) (T'I'II u e) =>
 (forall ee . Wrapper from ((t `T'TT'I` L l tt) ee)) =>
 (forall ee . Wrapper from ((t `T'TT'I` tt) ee)) =>
 (forall ee . Wrapper from (L l tt ee)) =>
 u e (t a) -> from a (L l tt o) -> u e (t o)
ho'yok x = fai fok (ho @from x)

ho_'yok = ho'yok
ho__'yok = ho'yok
ho___'yok = ho'yok
ho____'yok = ho'yok
ho_____'yok = ho'yok
ho______'yok = ho'yok
ho_______'yok = ho'yok
ho________'yok = ho'yok

ho'yuk, ho_'yuk, ho__'yuk, ho___'yuk, ho____'yuk, ho_____'yuk, ho______'yuk, ho_______'yuk, ho________'yuk
 :: forall from t tt ll a o e .
 Covariant Endo Semi Functor from tt =>
 Covariant Endo Semi Functor from t =>
 Constant Semi Functor from from t =>
 Covariant Endo Transformation Functor from (t `T'TT'I` ll `L` tt) t =>
 Component (AR) I (T'I'II from a) =>
 Covariant Yoneda Functor from (AR) (T'I'II from e) =>
 Wrapper from (t `T'TT'I` ll `L` tt `T'I_` o) =>
 Wrapper from (I `T'I_` ll `L` tt `T'I` o) =>
 -- Wrapper (AR) (U_1_I from a (tt o)) =>
 -- (forall ee . Wrapper from (t `T'TT'I` ll `L` tt `T'I_` ee)) =>
 from e (t a) -> (ll `L` tt) o -> from e (t o)
ho'yuk x = fai (fuk @from @t @tt) (ho @from x)
ho_'yuk x = fai (fuk @from @t @tt) (ho @from x)
ho__'yuk x = fai (fuk @from @t @tt) (ho @from x)
ho___'yuk x = fai (fuk @from @t @tt) (ho @from x)
ho____'yuk x = fai (fuk @from @t @tt) (ho @from x)
ho_____'yuk x = fai (fuk @from @t @tt) (ho @from x)
ho______'yuk x = fai (fuk @from @t @tt) (ho @from x)
ho_______'yuk x = fai (fuk @from @t @tt) (ho @from x)
ho________'yuk x = fai (fuk @from @t @tt) (ho @from x)

ha'yok, ha_'yok, ha__'yok, ha___'yok, ha____'yok, ha_____'yok, ha______'yok, ha_______'yok, ha________'yok
 :: forall from u t tt l a o e .
 Covariant Endo Semi Functor from t =>
 Covariant Endo Semi Functor from tt =>
 Covariant Endo Transformation Functor from (t `T'TT'I` L l tt) t =>
 Contravariant Yoneda Functor from (AR) (T'II'I (AR) (tt o)) =>
 Contravariant Yoneda Functor from (AR) (T'II'I u e) =>
 (forall ee . Wrapper from ((t `T'TT'I` L l tt) ee)) =>
 (forall ee . Wrapper from ((t `T'TT'I` tt) ee)) =>
 (forall ee . Wrapper from (L l tt ee)) =>
 u (t o) e -> from a (L l tt o) -> u (t a) e
ha'yok = fai fok `compose` ha @from @u

ha_'yok = ha'yok
ha__'yok = ha'yok
ha___'yok = ha'yok
ha____'yok = ha'yok
ha_____'yok = ha'yok
ha______'yok = ha'yok
ha_______'yok = ha'yok
ha________'yok = ha'yok

ha'yuk, ha_'yuk, ha__'yuk, ha___'yuk, ha____'yuk, ha_____'yuk, ha______'yuk, ha_______'yuk, ha________'yuk
 :: forall u t tt l a o e .
 Covariant Endo Semi Functor (AR) t =>
 Covariant Endo Semi Functor (AR) tt =>
 Covariant Endo Transformation Functor (AR) (t `T'TT'I` L l tt) t =>
 Contravariant Yoneda Functor (AR) (AR) (T'II'I u e) =>
 (forall ee . Wrapper (AR) ((t `T'TT'I` L l tt) ee)) =>
 (forall ee . Wrapper (AR) (L l tt ee)) =>
 u (t o) e -> L l tt o -> u (t a) e
ha'yuk = fai fuk `compose` ha @(AR) @u

ha_'yuk = ha'yuk
ha__'yuk = ha'yuk
ha___'yuk = ha'yuk
ha____'yuk = ha'yuk
ha_____'yuk = ha'yuk
ha______'yuk = ha'yuk
ha_______'yuk = ha'yuk
ha________'yuk = ha'yuk

ha'yokl, ha_'yokl, ha__'yokl, ha___'yokl, ha____'yokl, ha_____'yokl, ha______'yokl, ha_______'yokl, ha________'yokl
 :: forall from u t tt l ll a o e .
 Covariant Endo Semi Functor from t =>
 Covariant Endo Semi Functor from tt =>
 Covariant Endo Transformation Functor from (t `T'TT'I` L l (L ll tt)) (t `TT'T'I` tt) =>
 Contravariant Yoneda Functor from (AR) (T'II'I (AR) (tt o)) =>
 Contravariant Yoneda Functor from (AR) (T'II'I u e) =>
 (forall ee . Wrapper from ((t `T'TT'I` L l (L ll tt)) ee)) =>
 (forall ee . Wrapper from ((t `T'TT'I` tt) ee)) =>
 (forall ee . Wrapper from ((t `TT'T'I` tt) ee)) =>
 (forall ee . Wrapper from (L l tt ee)) =>
 u (tt (t o)) e -> from a (L l (L ll tt) o) -> u (t a) e
ha'yokl = fai fokl `compose` ha @from @u

ha_'yokl = ha'yokl
ha__'yokl = ha'yokl
ha___'yokl = ha'yokl
ha____'yokl = ha'yokl
ha_____'yokl = ha'yokl
ha______'yokl = ha'yokl
ha_______'yokl = ha'yokl
ha________'yokl = ha'yokl

-- TODO: generalize
yai'yukl, ha'yukl, ha_'yukl, ha__'yukl, ha___'yukl, ha____'yukl, ha_____'yukl, ha______'yukl, ha_______'yukl, ha________'yukl
 :: forall u t tt l ll a o e .
 Covariant Endo Semi Functor (AR) t =>
 Covariant Endo Semi Functor (AR) tt =>
 Covariant Endo Transformation Functor (AR) (t `T'TT'I` L l (L ll tt)) (t `TT'T'I` tt) =>
 Covariant Endo Transformation Functor (AR) I (T'I'II (AR) a) =>
 Contravariant Yoneda Functor (AR) (AR) (T'II'I (AR) (tt o)) =>
 Contravariant Yoneda Functor (AR) (AR) (T'II'I u e) =>
 (forall ee . Wrapper (AR) ((t `T'TT'I` L l (L ll tt)) ee)) =>
 (forall ee . Wrapper (AR) ((t `T'TT'I` tt) ee)) =>
 (forall ee . Wrapper (AR) ((t `TT'T'I` tt) ee)) =>
 (forall ee . Wrapper (AR) (L l tt ee)) =>
 Wrapper (AR) (I `T'I_` l `L` ll `L` tt `T'I` o) =>
 u (tt (t o)) e -> L l (L ll tt) o -> u (t a) e
yai'yukl = fai fukl `compose` ha @(AR) @u

ha'yukl = yai'yukl
ha_'yukl = yai'yukl
ha__'yukl = yai'yukl
ha___'yukl = yai'yukl
ha____'yukl = yai'yukl
ha_____'yukl = yai'yukl
ha______'yukl = yai'yukl
ha_______'yukl = yai'yukl
ha________'yukl = yai'yukl

-- TODO: try to gereralize
-- yok'ho :: forall from t tt l a o e .
 -- Covariant Functor (AR) (AR) tt =>
 -- Contravariant Functor (AR) (AR) (T'II'I from (t o)) =>
 -- Covariant Functor from from (T'I'II from e) =>
 -- Contravariant Functor from from (T'II'I from o) =>
 -- Covariant Functor (AR) from t =>
 -- Covariant Functor from from t =>
 -- Covariant Functor (AR) (AR) t =>
 -- Covariant Functor (AR) from tt =>
 -- Covariant Functor from from tt =>
 -- Covariant Yoneda Functor from from t =>
 -- Contravariant Yoneda Functor from (AR) (T'II'I from (L l tt o)) =>
 -- Mapping T'I'II T'I'II from from (T'TT'I t (L l tt)) t =>
 -- (forall ee . Wrapper from ((t `T'TT'I` L l tt) ee)) =>
 -- Wrapper from (T'II'I from e (L l tt o)) =>
 -- Wrapper from (T'I'II from e (L l tt o)) =>
 -- (forall ee . Wrapper from (L l tt ee)) =>
 -- (forall ee . Wrapper from (T'I'II from e ee)) =>
 -- Wrapper from (T'II'I from o a) =>
 -- Wrapper from (T'II'I from o e) =>
 -- Wrapper from (T'I'II from e a) =>
 -- t e -> from a (L l tt o) -> from (from e a) (t o)
-- yok'ho x f = yok x `compose` fio f

-- TODO: try to gereralize
-- yok'ha :: forall into t tt l a o i .
 -- Category into =>
 -- Covariant Yoneda Functor into into t =>
 -- Covariant Functor into into t =>
 -- Covariant Functor into into tt =>
 -- Contravariant Functor into into (T'II'I into (L l tt o)) =>
 -- Contravariant Yoneda Functor into (AR) (T'II'I into (L l tt o)) =>
 -- Mapping T'I'II T'I'II into into (T'TT'I t (L l tt)) t =>
 -- (forall e . Wrapper into ((t `T'TT'I` L l tt) e)) =>
 -- (forall e . Wrapper into (L l tt e)) =>
 -- (forall e ee . Wrapper into (T'I'II into e (L l tt ee))) =>
 -- (forall e ee . Wrapper into (T'II'I into (L l tt e) ee)) =>
 -- t i -> into i a -> into (into a (L l tt o)) (t o)
-- yok'ha x f = yok @into @into x `compose` fai @into f

-- yok'hj, yok_'hj, yok__'hj, yok___'hj, yok____'hj, yok_____'hj, yok______'hj
 -- :: forall from t tt ttt tttt l a o e .
 -- Category from =>
 -- Adjoint Functor from from (T'II'I ttt e) (T'I'II tttt e) =>
 -- Contravariant Functor (AR) (AR) (T'II'I from (t o)) =>
 -- Covariant Functor from from t =>
 -- Covariant Functor from from tt =>
 -- Covariant Endo Transformation Functor from (T'TT'I t (L l tt)) t =>
 -- Covariant Yoneda Functor from from t =>
 -- (forall ee . Wrapper from (T'I'II from (ttt a e) (L l tt ee))) =>
 -- (forall ee . Wrapper from (T'II'I ttt e ee)) =>
 -- (forall ee . Wrapper from (T'II'I tttt e (l `L` tt `T'I` ee))) =>
 -- (forall ee . Wrapper from (T'I'II tttt e (l `L` tt `T'I` ee))) =>
 -- (forall ee . Wrapper from (L l tt ee)) =>
 -- (forall ee . Wrapper from (t `T'TT'I` l `L` tt `WR___` ee)) =>
 -- (forall ee . Wrapper from (I (l `L` tt `T'I` ee))) =>
 -- (forall ee . Wrapper from (T'II'I ttt e `T'TT'I` T'I'II tttt e `WR___` l `L` tt `T'I` ee)) =>
 -- t (ttt a e) -> from (from a (tttt e (L l tt o))) (t o)
-- yok'hj x = fai hj (yok @from @from x)

-- yok_'hj = yok'hj
-- yok__'hj = yok'hj
-- yok___'hj = yok'hj
-- yok____'hj = yok'hj
-- yok_____'hj = yok'hj
-- yok______'hj = yok'hj

-- yok'hu :: forall from t tt a o e .
  -- Precategory from =>
  -- Covariant Yoneda Functor from from t =>
  -- Mapping T'I'II T'I'II from from (T'I'II from e) (T'I'II from e) =>
  -- Constant Semi Functor from from (T'I'II from e) =>
  -- Covariant Semi Functor from from t =>
  -- Covariant Semi Functor (AR) from t =>
  -- Covariant Semi Functor from (AR) tt =>
  -- Covariant Semi Functor (AR) from tt =>
  -- Mapping T'I'II T'I'II (AR) from (T'TT'I t tt) t =>
  -- (forall ee . Wrapper from ((t `T'TT'I` tt) ee)) =>
  -- Elicitable T'II'I from (T'TT'I t tt o) =>
  -- Wrapper from (T'I'II from e (tt o)) =>
  -- Elicitable T'II'I from (T'I'II from e a) =>
  -- Elicitable T'II'I from (U_1_I from a (tt o)) =>
  -- Elicitable T'II'I (AR) (U_1_I from a (tt o)) =>
  -- t e -> Supertype (U_1_I from a (tt o)) -> from (from e a) (t o)
-- yok'hu x f = yok @_ @_ @tt x `compose` fiu @from f

-- yokl__ :: forall from u t tt a o e .
 -- Category from =>
 -- -- Covariant Endo Semi Functor from tt =>
 -- Covariant Functor from from (T'I'II u e) =>
 -- Covariant Functor (AR) u t =>
 -- Covariant Functor u u t =>
 -- -- Mapping T'I'II T'I'II from from (T'TT'I t tt) t =>
 -- Covariant Yoneda Functor from u t =>
 -- Covariant Yoneda Functor u from (T'I'II u e) =>
 -- Covariant Yoneda Functor from from (T'II'I u (t o)) =>
 -- -- Covariant Yoneda Functor from from t =>
 -- -- (forall ee . Wrapper from (T'TT'I t tt ee)) =>
 -- -- t (from a o) -> from (u e a) (t o)
 -- t (u e a) -> u (from a o) (t o)
-- yokl__ x = fai fio (yokl @from @u x)

-- TODO: generalize
ho'yokl, ho_'yokl, ho__'yokl, ho___'yokl, ho____'yokl, ho_____'yokl, ho______'yokl, ho_______'yokl, ho________'yokl :: forall from u t tt l ll a o e .
 Covariant Semi Functor from (AR) (T'I'II u e) =>
 Covariant Endo Semi Functor from tt =>
 Covariant Endo Semi Functor from t =>
 Covariant Endo Transformation Functor from (t `T'TT'I` L l (L ll tt)) (t `TT'T'I` tt) =>
 Covariant Yoneda Functor from (AR) (T'I'II u e) =>
 (forall ee . Wrapper from ((t `T'TT'I` L l (L ll tt)) ee)) =>
 (forall ee . Wrapper from ((t `T'TT'I` tt) ee)) =>
 (forall ee . Wrapper from ((t `TT'T'I` tt) ee)) =>
 (forall ee . Wrapper from (L l (L ll tt) ee)) =>
 (forall ee . Wrapper from (L ll tt ee)) =>
 u e (t a) -> from a (L l (L ll tt) o) -> u e (tt (t o))
ho'yokl x = fai fokl (ho @from x)

ho_'yokl = ho'yokl
ho__'yokl = ho'yokl
ho___'yokl = ho'yokl
ho____'yokl = ho'yokl
ho_____'yokl = ho'yokl
ho______'yokl = ho'yokl
ho_______'yokl = ho'yokl
ho________'yokl = ho'yokl

yio'yokl'yokl
 , ho'yokl'yokl
 , ho_'yokl'yokl
 , ho__'yokl'yokl
 , ho___'yokl'yokl
 , ho____'yokl'yokl
 , ho_____'yokl'yokl
 , ho______'yokl'yokl
 , ho_______'yokl'yokl
 , ho________'yokl'yokl
 :: forall from into u t tt ttt l ll lll a o i .
 Category from =>
 Covariant Yoneda Functor from into (T'I'II u i) =>
 Covariant Endo Semi Functor from t =>
 Covariant Endo Semi Functor from tt =>
 Covariant Semi Functor into from t =>
 Covariant Endo Semi Functor from ttt =>
 Covariant Semi Functor into from ttt =>
 Contravariant Semi Functor (AR) (AR) (T'II'I into (u i (ttt (t (tt o))))) =>
 Covariant Transformation Functor from from (t `T'TT'I` l `L` lll `L` ttt) (t `TT'T'I` ttt) =>
 Covariant Transformation Functor from from (tt `T'TT'I` ll `L` lll `L` ttt) (tt `TT'T'I` ttt) =>
 Covariant Transformation Functor into from (t `T'TT'I` l `L` ll `L` ttt) (t `TT'T'I` ttt) =>
 (forall e ee . Wrapper into (T'I'II from e ee)) =>
 (forall e . Wrapper into (T'I'II u i e)) =>
 (forall e . Wrapper from ((tt `TT'T'I` ttt) e)) =>
 (forall e . Wrapper from ((t `TT'T'I` ttt) (tt e))) =>
 (forall e . Wrapper from (L lll ttt e)) =>
 (forall e . Wrapper from (L l (L ll (L lll ttt)) e)) =>
 (forall e . Wrapper from ((tt `T'TT'I` ll `L` lll `L` ttt) e)) =>
 (forall e . Wrapper from ((t `T'TT'I` l `L` lll `L` ttt) (tt e))) =>
 (forall e . Wrapper from (L l (L lll ttt) (tt e))) =>
 u i (t (tt a)) -> into (from a (L l (L ll (L lll ttt)) o)) (u i (ttt (t (tt o))))
yio'yokl'yokl x = fai @(AR)
 (fokl @from @from @t @ttt @l @lll
  `compose` fio @from (wrap @from @(L l _ _) `compose` wrap @from @(L lll _ _))
  `compose` fokl @from @from @tt @ttt @ll @lll
  `compose` fio @from (unwrap @from @(L l _ _)))
 (yio @from x)

ho'yokl'yokl = yio'yokl'yokl
ho_'yokl'yokl = yio'yokl'yokl
ho__'yokl'yokl = yio'yokl'yokl
ho___'yokl'yokl = yio'yokl'yokl
ho____'yokl'yokl = yio'yokl'yokl
ho_____'yokl'yokl = yio'yokl'yokl
ho______'yokl'yokl = yio'yokl'yokl
ho_______'yokl'yokl = yio'yokl'yokl
ho________'yokl'yokl = yio'yokl'yokl

yio'yokl'yukl
 , ho'yokl'yukl
 , ho_'yokl'yukl
 , ho__'yokl'yukl
 , ho___'yokl'yukl
 , ho____'yokl'yukl
 , ho_____'yokl'yukl
 , ho______'yokl'yukl
 , ho_______'yokl'yukl
 , ho________'yokl'yukl
 :: forall into u t tt ttt l ll lll a o i .
 Covariant Yoneda Functor (AR) into (T'I'II u i) =>
 Covariant Endo Semi Functor (AR) t =>
 Covariant Endo Semi Functor (AR) tt =>
 Covariant Semi Functor into (AR) t =>
 Covariant Endo Semi Functor (AR) ttt =>
 Covariant Semi Functor into (AR) ttt =>
 Contravariant Semi Functor (AR) (AR) (T'II'I into (u i (ttt (t (tt o))))) =>
 Covariant Transformation Functor (AR) (AR) (t `T'TT'I` l `L` lll `L` ttt) (t `TT'T'I` ttt) =>
 Covariant Transformation Functor (AR) (AR) (tt `T'TT'I` ll `L` lll `L` ttt) (tt `TT'T'I` ttt) =>
 Covariant Transformation Functor into (AR) (t `T'TT'I` l `L` ll `L` ttt) (t `TT'T'I` ttt) =>
 (forall e ee . Wrapper into (T'I'II (AR) e ee)) =>
 (forall e . Wrapper into (T'I'II u i e)) =>
 (forall e . Wrapper (AR) ((tt `TT'T'I` ttt) e)) =>
 (forall e . Wrapper (AR) ((t `TT'T'I` ttt) (tt e))) =>
 (forall e . Wrapper (AR) (L lll ttt e)) =>
 (forall e . Wrapper (AR) (L l (L ll (L lll ttt)) e)) =>
 (forall e . Wrapper (AR) ((tt `T'TT'I` ll `L` lll `L` ttt) e)) =>
 (forall e . Wrapper (AR) ((t `T'TT'I` l `L` lll `L` ttt) (tt e))) =>
 (forall e . Wrapper (AR) (L l (L lll ttt) (tt e))) =>
 u i (t (tt a)) -> into (L l (L ll (L lll ttt)) o) (u i (ttt (t (tt o))))
yio'yokl'yukl x = fai @(AR)
 (fokl @(AR) @(AR) @t @ttt @l @lll
  `compose` fio @(AR) (wrap @(AR) @(L l _ _) `compose` wrap @(AR) @(L lll _ _))
  `compose` fukl @(AR) @tt @ttt @ll @lll
  `compose` unwrap @(AR) @(L l _ _))
 (yio @(AR) x)

ho'yokl'yukl = yio'yokl'yukl
ho_'yokl'yukl = yio'yokl'yukl
ho__'yokl'yukl = yio'yokl'yukl
ho___'yokl'yukl = yio'yokl'yukl
ho____'yokl'yukl = yio'yokl'yukl
ho_____'yokl'yukl = yio'yokl'yukl
ho______'yokl'yukl = yio'yokl'yukl
ho_______'yokl'yukl = yio'yokl'yukl
ho________'yokl'yukl = yio'yokl'yukl

yio'yukl, ho'yukl, ho_'yukl, ho__'yukl, ho___'yukl, ho____'yukl, ho_____'yukl, ho______'yukl, ho_______'yukl, ho________'yukl
 :: forall u t tt l ll a o e .
 Covariant Semi Functor (AR) (AR) (T'I'II u e) =>
 Covariant Endo Semi Functor (AR) tt =>
 Covariant Endo Semi Functor (AR) t =>
 Mapping T'I'II T'I'II (AR) (AR) (t `T'TT'I` L l (L ll tt)) (t `TT'T'I` tt) =>
 Covariant Endo Transformation Functor (AR) I (T'I'II (AR) a) =>
 Covariant Endo Yoneda Functor (AR) (T'I'II u e) =>
 (forall ee . Wrapper (AR) ((t `T'TT'I` L l (L ll tt)) ee)) =>
 (forall ee . Wrapper (AR) ((t `T'TT'I` tt) ee)) =>
 (forall ee . Wrapper (AR) ((t `TT'T'I` tt) ee)) =>
 (forall ee . Wrapper (AR) (L l (L ll tt) ee)) =>
 (forall ee . Wrapper (AR) (L ll tt ee)) =>
 u e (t a) -> L l (L ll tt) o -> u e (tt (t o))
yio'yukl x = fai fukl (ho @(AR) x)

ho'yukl = yio'yukl
ho_'yukl = yio'yukl
ho__'yukl = yio'yukl
ho___'yukl = yio'yukl
ho____'yukl = yio'yukl
ho_____'yukl = yio'yukl
ho______'yukl = yio'yukl
ho_______'yukl = yio'yukl
ho________'yukl = yio'yukl

-- ha'yuk :: forall from t tt a o e .
--  Covariant Functor (AR) (AR) tt =>
--  Covariant Functor from from t =>
--  Covariant Functor from from tt =>
--  Contravariant Yoneda Functor from (AR) (T'II'I from (tt o)) =>
--  Mapping T'I'II T'I'II from from (T'TT'I tt t) tt =>
--  Constant Semi Functor from from tt =>
--  Elicitable T'II'I from (T'TT'I tt t o) =>
--  (forall ee . Wrapper from (T'TT'I tt t ee)) =>
--  Elicitable T'II'I from (T'TT'I tt tt o) =>
--  Elicitable T'II'I (AR) (U_1_I from a (t o)) =>
--  Supertype (U_1_I from a (t o)) -> from e (tt a) -> from e (tt o)
-- ha'yuk = ha `compose` fuk @from @tt @t

-- TODO: generalize
lu'yp, lu_'yp, lu__'yp, lu___'yp, lu____'yp, lu_____'yp, lu______'yp, lu_______'yp
 :: forall o oo t tt l .
 Mapping T'I'II T'I'II (AR) (AR) (Day T'I'II (AR) (P) P t (l `L` tt) o oo) t =>
 -- Covariant Monoidal Functor (AR) (AR) (P) P l t =>
 Covariant Yoneda Functor (AR) (AR) (T'I'II Product (t o)) =>
 Covariant Yoneda Functor (AR) (AR) (T'II'I Product ()) =>
 t o -> (l `L` tt) oo -> t (o `P` oo)
lu'yp from_left r = yp (lu from_left r)

lu_'yp = lu'yp
lu__'yp = lu'yp
lu___'yp = lu'yp
lu____'yp = lu'yp
lu_____'yp = lu'yp
lu______'yp = lu'yp
lu_______'yp = lu'yp

lu'yp'yo'q, lu_'yp'yo'q, lu__'yp'yo'q, lu___'yp'yo'q, lu____'yp'yo'q, lu_____'yp'yo'q, lu______'yp'yo'q, lu_______'yp'yo'q
 :: forall o t tt l .
 Mapping T'I'II T'I'II (AR) (AR) (Day T'I'II (AR) (P) P t (l `L` tt) o o) t =>
 -- Covariant Monoidal Functor (AR) (AR) (P) P l t =>
 Covariant Yoneda Functor (AR) (AR) (T'I'II Product (t o)) =>
 Covariant Yoneda Functor (AR) (AR) (T'II'I Product ()) =>
 Setoid (AR) o =>
 t o -> (l `L` tt) o -> t (o `P` o `S` o)
lu'yp'yo'q from_left r = yp'yo (lu from_left r) q

lu_'yp'yo'q = lu'yp'yo'q
lu__'yp'yo'q = lu'yp'yo'q
lu___'yp'yo'q = lu'yp'yo'q
lu____'yp'yo'q = lu'yp'yo'q
lu_____'yp'yo'q = lu'yp'yo'q
lu______'yp'yo'q = lu'yp'yo'q
lu_______'yp'yo'q = lu'yp'yo'q

-- lu'yip, lu_'yip, lu__'yip, lu___'yip, lu____'yip, lu_____'yip, lu______'yip, lu_______'yip
 -- :: forall e o oo t .
 -- Covariant Monoidal Functor (AR) (AR) (P) P (T'I'II t e) =>
 -- Covariant Yoneda Functor (AR) (AR) (T'I'II Product (t e o)) =>
 -- Covariant Yoneda Functor (AR) (AR) (T'II'I Product ()) =>
 -- t e o -> t e oo -> t e (o `P` oo)
-- lu'yip l r = yip (lu l r)

-- lu_'yip = lu'yip
-- lu__'yip = lu'yip
-- lu___'yip = lu'yip
-- lu____'yip = lu'yip
-- lu_____'yip = lu'yip
-- lu______'yip = lu'yip
-- lu_______'yip = lu'yip

lu'ys, lu_'ys, lu__'ys, lu___'ys, lu____'ys, lu_____'ys, lu______'ys, lu_______'ys
 :: forall o oo t tt l .
 -- Covariant Lax Monoidal Functor (AR) (AR) (P) (S) l t =>
 Mapping T'I'II T'I'II (AR) (AR) (Day T'I'II (AR) (P) (S) t (l `L` tt) o oo) t =>
 Covariant Yoneda Functor (AR) (AR) (T'I'II (P) (t o)) =>
 Covariant Yoneda Functor (AR) (AR) (T'II'I (P) ()) =>
 t o -> (l `L` tt) oo -> t (o `S` oo)
lu'ys l r = ys (lu l r)

lu_'ys = lu'ys
lu__'ys = lu'ys
lu___'ys = lu'ys
lu____'ys = lu'ys
lu_____'ys = lu'ys
lu______'ys = lu'ys
lu_______'ys = lu'ys

-- lu'yis, lu_'yis, lu__'yis, lu___'yis, lu____'yis, lu_____'yis, lu______'yis, lu_______'yis
 -- :: forall e o oo t .
 -- Covariant Monoidal Functor (AR) (AR) (P) (S) (T'I'II t e) =>
 -- Covariant Yoneda Functor (AR) (AR) (T'I'II (P) (t e o)) =>
 -- Covariant Yoneda Functor (AR) (AR) (T'II'I (P) ()) =>
 -- t e o -> t e oo -> t e (o `S` oo)
-- lu'yis l r = yis (lu l r)

-- lu_'yis = lu'yis
-- lu__'yis = lu'yis
-- lu___'yis = lu'yis
-- lu____'yis = lu'yis
-- lu_____'yis = lu'yis
-- lu______'yis = lu'yis
-- lu_______'yis = lu'yis

lu'yp'yp :: forall o oo t tt l ll .
 Covariant Endo Semi Functor (AR) tt =>
 Covariant Transformation Functor (AR) (AR) (Day T'I'II (AR) (P) P t (l `L` t) (tt o) (L ll tt oo)) t =>
 Covariant Transformation Functor (AR) (AR) (Day T'I'II (AR) (P) P tt (ll `L` tt) o oo) tt =>
 Covariant Yoneda Functor (AR) (AR) (T'I'II Product (t (tt o))) =>
 Covariant Yoneda Functor (AR) (AR) (T'II'I Product Unit) =>
 t (tt o) -> (l `L` t) ((ll `L` tt) oo) -> t (tt (o `P` oo))
lu'yp'yp l r = yp'yp @(P) (lu l r)

lu'yp'ys
 :: forall t tt l ll o oo .
 Covariant Lax Monoidal Functor (AR) (AR) (P) P l t =>
 Covariant Lax Monoidal Functor (AR) (AR) (P) (S) ll tt =>
 Covariant Endo Semi Functor (AR) t =>
 Covariant Yoneda Functor (AR) (AR) (T'II'I Product ()) =>
 Covariant Yoneda Functor (AR) (AR) (T'I'II Product (t (tt o))) =>
 t (tt o) -> (l `L` t) ((ll `L` tt) oo) -> t (tt (o `S` oo))
lu'yp'ys l r = yp'ys (lu l r)

-- lu'yip'yp
 -- :: forall t tt o oo e .
 -- Covariant Lax Monoidal Functor (AR) (AR) (P) P tt =>
 -- Covariant Monoidal Functor (AR) (AR) (P) P (T'I'II t e) =>
 -- Covariant Endo Semi Functor (AR) (T'I'II t e) =>
 -- Covariant Yoneda Functor (AR) (AR) (T'II'I Product ()) =>
 -- Covariant Yoneda Functor (AR) (AR) (T'I'II Product (t e (tt o))) =>
 -- t e (tt o) -> t e (tt oo) -> t e (tt (o `P` oo))
-- lu'yip'yp l r = yip'yp (lu l r)

-- lu'yip'yip
 -- :: forall t tt o oo e ee .
 -- Covariant Monoidal Functor (AR) (AR) (P) P (T'I'II tt ee) =>
 -- Covariant Monoidal Functor (AR) (AR) (P) P (T'I'II t e) =>
 -- Covariant Endo Semi Functor (AR) (T'I'II t e) =>
 -- Covariant Yoneda Functor (AR) (AR) (T'II'I Product ()) =>
 -- Covariant Yoneda Functor (AR) (AR) (T'I'II Product (t e (tt ee o))) =>
 -- t e (tt ee o) -> t e (tt ee oo) -> t e (tt ee (o `P` oo))
-- lu'yip'yip l r = yip'yip (lu l r)

-- lu'yip'yis
 -- :: forall t tt l ll o oo e ee .
 -- Covariant Monoidal Functor (AR) (AR) (P) P l (T'I'II t e) =>
 -- Covariant Monoidal Functor (AR) (AR) (P) (S) ll (T'I'II tt ee) =>
 -- Covariant Endo Semi Functor (AR) (T'I'II t e) =>
 -- Covariant Yoneda Functor (AR) (AR) (T'II'I Product ()) =>
 -- Covariant Yoneda Functor (AR) (AR) (T'I'II Product (t e (tt ee o))) =>
 -- t e (tt ee o) -> (l `L` t) e ((ll `L` tt) ee oo) -> t e (tt ee (o `S` oo))
-- lu'yip'yis l r = yip'yis (lu l r)

lu'ysp, lu_'ysp, lu__'ysp, lu___'ysp, lu____'ysp, lu_____'ysp, lu______'ysp, lu_______'ysp
 :: forall e o oo t tt l .
 Mapping T'I'II T'I'II (AR) (AR) (Day T'I'II (AR) (P) (SP) t (l `L` tt) o oo) t =>
 Covariant Yoneda Functor (AR) (AR) (T'II'I Product ()) =>
 Covariant Yoneda Functor (AR) (AR) (T'I'II Product (t o)) =>
 t o -> (l `L` tt) oo -> t (o `S` oo `S_` o `P` oo)
lu'ysp l r = ysp (lu l r)

lu_'ysp = lu'ysp
lu__'ysp = lu'ysp
lu___'ysp = lu'ysp
lu____'ysp = lu'ysp
lu_____'ysp = lu'ysp
lu______'ysp = lu'ysp
lu_______'ysp = lu'ysp

-- jt :: forall into f g e .
 -- Covariant Transformation Functor (AR) into (f `T'TT'I` g) (f `JNT` g) =>
 -- Elicitable T'II'I into ((f `T'TT'I` g) e) =>
 -- into (f (g e)) ((f `JNT` g) e)
-- jt = component @into @(f `T'TT'I` g) @(f `JNT` g) @e
 -- `compose` wrap @into @((f `T'TT'I` g) e)

-- TODO: generalize
-- yp'yp'jt :: forall e ee t tt .
 -- Covariant Transformation Functor (AR) (AR) (t `T'TT'I` tt) (t `JNT` tt) =>
 -- Covariant Monoidal Functor (AR) (AR) (P) P t =>
 -- Covariant Monoidal Functor (AR) (AR) (P) P tt =>
 -- t (tt e) `P` t (tt ee) -> (t `JNT` tt) (e `P` ee)
-- yp'yp'jt = jt `compose` day @T'I'II @(AR) @t @(P) @P identity
 -- (day @T'I'II @(AR) @tt @(P) @P identity identity)

-- TODO: generalize
-- yp'yp'jt'yok :: forall from into e ee t tt ttt o .
 -- Covariant Yoneda Functor from into t =>
 -- Covariant Semi Functor into into ttt =>
 -- Covariant Yoneda Functor from into (t `JNT` tt) =>
 -- Covariant Transformation Functor (AR) (AR) (t `T'TT'I` tt) (t `JNT` tt) =>
 -- Covariant Transformation Functor (AR) into (T'TT'I (t `JNT` tt) ttt) (t `JNT` tt) =>
 -- Covariant Monoidal Functor (AR) (P) P t =>
 -- Covariant Monoidal Functor (AR) (P) P tt =>
 -- Elicitable T'II'I into (T'I'II from (e `P` ee) (ttt o)) =>
 -- (forall e . Wrapper into (T'TT'I (JNT t tt) ttt e)) =>
 -- t (tt e) `P` t (tt ee) -> into (from (e `P` ee) (ttt o)) ((t `JNT` tt) o)
-- yp'yp'jt'yok = yok @from @into `compose` yp'yp'jt

q, q_, q__, q___, q____, q_____, q______, q_______, q________ ::
 forall into e .
 Setoid into e =>
 into (e `P` e) (e `P` e `S` e)
q = equality

q_ = q
q__ = q
q___ = q
q____ = q
q_____ = q
q______ = q
q_______ = q
q________ = q
