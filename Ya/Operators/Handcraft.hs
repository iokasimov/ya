{-# LANGUAGE AllowAmbiguousTypes #-}
module Ya.Operators.Handcraft where

import Ya.Algebra.Abstract
import Ya.Algebra.Definition
import Ya.Algebra.Effectful
import Ya.Algebra.Instances ()

import Ya.Operators.Mappings

infixl 9 `ho`, `ho'yoo`, `ho'yioi`, `ho'yu`, `ho'yui`, `ho'yok`, `ho'yuk`, `ho'yokl`, `ho'yukl`, `ho'yokl'yokl`, `ho'yokl'yukl`, `ho'yoikl`
 , `ho'he`
 , `ho'he'he`
 , `ho'he'he'he`
 , `ho'he'he'hv`
 , `ho'he'he'he'he`
 , `ho'hd`
 , `ho'hd'hd`
 , `ho'hu`
infixl 8 `ho_`, `ho_'yoo`, `ho_'yu`, `ho_'yok`, `ho_'yuk`, `ho_'yokl`, `ho_'yukl`, `ho_'yokl'yokl`, `ho_'yokl'yukl`, `ho_'yoikl`
 , `ho_'he`
 , `ho_'he'he`
 , `ho_'he'he'he`
 , `ho_'he'he'hv`
 , `ho_'he'he'he'he`
 , `ho_'hd`
infixl 7 `ho__`, `ho__'yoo`, `ho__'yu`, `ho__'yok`, `ho__'yuk`, `ho__'yokl`, `ho__'yukl`, `ho__'yokl'yokl`, `ho__'yokl'yukl`, `ho__'yoikl`
 , `ho__'he`
 , `ho__'he'he`
 , `ho__'he'he'he`
 , `ho__'he'he'hv`
 , `ho__'he'he'he'he`
 , `ho__'hd`
infixl 6 `ho___`, `ho___'yoo`, `ho___'yu`, `ho___'yok`, `ho___'yuk`, `ho___'yokl`, `ho___'yukl`, `ho___'yokl'yokl`, `ho___'yokl'yukl`, `ho___'yoikl`
 , `ho___'he`
 , `ho___'he'he`
 , `ho___'he'he'he`
 , `ho___'he'he'hv`
 , `ho___'he'he'he'he`
 , `ho___'hd`
infixl 5 `ho____`, `ho____'yoo`, `ho____'yu`, `ho____'yok`, `ho____'yuk`, `ho____'yokl`, `ho____'yukl`, `ho____'yokl'yokl`, `ho____'yokl'yukl`, `ho____'yoikl`
 , `ho____'he`
 , `ho____'he'he`
 , `ho____'he'he'he`
 , `ho____'he'he'hv`
 , `ho____'he'he'he'he`
infixl 4 `ho_____`, `ho_____'yoo`, `ho_____'yu`, `ho_____'yok`, `ho_____'yuk`, `ho_____'yokl`, `ho_____'yukl`, `ho_____'yokl'yokl`, `ho_____'yokl'yukl`, `ho_____'yoikl`
 , `ho_____'he`
 , `ho_____'he'he`
 , `ho_____'he'he'he`
 , `ho_____'he'he'hv`
 , `ho_____'he'he'he'he`
 , `ho____'hd`
infixl 3 `ho______`, `ho______'yoo`, `ho______'he`, `ho______'yok`, `ho______'yuk`, `ho______'yokl`, `ho______'yokl'yokl`, `ho______'yokl'yukl`, `ho______'yukl`, `ho______'yoikl`
infixl 2 `ho_______`, `ho_______'yoo`, `ho_______'yok`, `ho_______'yuk`, `ho_______'yokl`, `ho_______'yokl'yokl`, `ho_______'yokl'yukl`, `ho_______'yukl`, `ho_______'yoikl`
 , `ho_______'he`
 , `ho_______'he'he`
 , `ho_______'he'he'he`
 , `ho_______'he'he'hv`
 , `ho_______'he'he'he'he`
 , `ho_____'hd`
infixl 1 `ho________`, `ho________'yoo`, `ho________'yok`, `ho________'yuk`, `ho________'yokl`, `ho________'yukl` , `ho________'yokl'yokl`, `ho________'yokl'yukl`, `ho________'yoikl`
 , `ho________'he`
 , `ho________'he'he`
 , `ho________'he'he'he`
 , `ho________'he'he'hv`
 , `ho________'he'he'he'he`
 , `ho______'hd`
 -- , `ho________'yo`
 -- , `ho________'yoi`

infixl 9 `ha`, `ha'hu`
 , `ha'yok`
 , `ha'yuk`
 , `ha'kyo`
 , `ha'kyok`
 , `ha'yokl`, `ha'yukl`
 , `ha'he`
 , `he'ha`
 , `ha'hd`
 , `ha'hd'hd`
infixl 8 `ha_`
 , `ha_'he`
 , `ha_'hu`
 , `ha_'yok`
 , `ha_'yuk`
 , `ha_'kyo`
 , `ha_'kyok`
 , `ha_'yokl`
 , `ha_'yukl`
infixl 7 `ha__`
 , `ha__'he`
 , `ha__'hu`
 , `ha__'yok`
 , `ha__'yuk`
 , `ha__'kyo`
 , `ha__'kyok`
 , `ha__'yokl`
 , `ha__'yukl`
infixl 6 `ha___`
 , `ha___'he`
 , `ha___'hu`
 , `ha___'yok`
 , `ha___'yuk`
 , `ha___'kyo`
 , `ha___'kyok`
 , `ha___'yokl`
 , `ha___'yukl`
infixl 5 `ha____`
 , `ha____'he`
 , `ha____'hu`
 , `ha____'yok`
 , `ha____'yuk`
 , `ha____'kyo`
 , `ha____'kyok`
 , `ha____'yokl`
 , `ha____'yukl`
infixl 4 `ha_____`
 , `ha_____'he`
 , `ha_____'hu`
 , `ha_____'yok`
 , `ha_____'yuk`
 , `ha_____'kyo`
 , `ha_____'kyok`
 , `ha_____'yokl`
 , `ha_____'yukl`
infixl 3 `ha______`
 , `ha______'he`
 , `ha______'hu`
 , `ha______'yok`
 , `ha______'yuk`
 , `ha______'kyo`
 , `ha______'kyok`
 , `ha______'yokl`
 , `ha______'yukl`
infixl 2 `ha_______`
 , `ha_______'he`
 , `ha_______'hu`
 , `ha_______'yok`
 , `ha_______'yuk`
 , `ha_______'kyo`
 , `ha_______'kyok`
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

infixl 8 `lo`, `lo'lu`, `lo'yp`, `lo'yp'yo'q`, `lo'ys`, `lo'ys'la`, `lo'q`, `lu'ys'la`
infixl 7 `lo_`, `lo_'yp`, `lo_'yp'yo'q`, `lo_'ys`, `lo_'ys'la`, `lo_'q`, `lu_'ys'la`
infixl 6 `lo__`, `lo__'yp`, `lo__'yp'yo'q`, `lo__'ys`, `lo__'ys'la`, `lo__'q`, `lu__'ys'la`
infixl 5 `lo___`, `lo___'yp`, `lo___'yp'yo'q`, `lo___'ys`, `lo___'ys'la`, `lo___'q`, `lu___'ys'la`
infixl 4 `lo____`, `lo____'yp`, `lo____'yp'yo'q`, `lo____'ys`, `lo____'ys'la`, `lo____'q`, `lu____'ys'la`
infixl 3 `lo_____`, `lo_____'yp`, `lo_____'yp'yo'q`, `lo_____'ys`, `lo_____'ys'la`, `lo_____'q`, `lu_____'ys'la`
infixl 2 `lo______`, `lo______'yp`, `lo______'yp'yo'q`, `lo______'ys`, `lo______'ys'la`, `lo______'q`, `lu______'ys'la`
infixl 1 `lo_______`, `lo_______'yp`, `lo_______'yp'yo'q`, `lo_______'ys`, `lo_______'ys'la`, `lo_______'q`,  `lu_______'ys'la`

infixl 8 `la`
infixl 7 `la_`
infixl 6 `la__`
infixl 5 `la___`
infixl 4 `la____`
infixl 3 `la_____`
infixl 2 `la______`
infixl 1 `la_______`

infixl 8 `lu`, `lu'yp`, `lu'yp'yo'q`, `lu'ys`, `lu'yp'yp`, `lu'yr`, `lu'q`, `lu's`
infixl 7 `lu_`, `lu_'yp`, `lu_'yp'yo'q`, `lu_'ys`, `lu_'yr`, `lu_'q`, `lu_'s`
infixl 6 `lu__`, `lu__'yp`, `lu__'yp'yo'q`, `lu__'ys`, `lu__'yr`, `lu__'q`, `lu__'s`
infixl 5 `lu___`, `lu___'yp`, `lu___'yp'yo'q`, `lu___'ys`, `lu___'yr`, `lu___'q`, `lu___'s`
infixl 4 `lu____`, `lu____'yp`, `lu____'yp'yo'q`, `lu____'ys`, `lu____'yr`, `lu____'q`, `lu____'s`
infixl 3 `lu_____`, `lu_____'yp`, `lu_____'yp'yo'q`, `lu_____'ys`, `lu_____'yr`, `lu_____'q`, `lu_____'s`
infixl 2 `lu______`, `lu______'yp`, `lu______'yp'yo'q`, `lu______'ys`, `lu______'yr`, `lu______'q`, `lu______'s`
infixl 1 `lu_______`, `lu_______'yp`, `lu_______'yp'yo'q`, `lu_______'ys`, `lu_______'yr`, `lu_______'q`, `lu_______'s`

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

infixl 8 `yo`, `yo'yp`, `yo'yok`, `yo'yoo`, `yo'yuu`
infixl 7 `yo_`, `yoo`
infixl 6 `yo__`
infixl 5 `yo___`
infixl 4 `yo____`
infixl 3 `yo_____`
infixl 2 `yo______`
infixl 1 `yo_______`

infixl 7 `yok` --, `yok'yokl`, `yok'yukl`
infixl 6 `yok_` --, `yok_'yokl`, `yok_'yukl`
infixl 5 `yok__` --, `yok__'yokl`, `yok__'yukl`
infixl 4 `yok___` --, `yok___'yokl`, `yok___'yukl`
infixl 3 `yok____` --, `yok____'yokl`, `yok____'yukl`
infixl 2 `yok_____` --, `yok_____'yokl`, `yok_____'yukl`
infixl 1 `yok______` --, `yok______'yokl`, `yok______'yukl`

infixl 7 `kyo`

infixl 6 `kyok`

infixl 5 `kyokl`

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

infixl 5 `yiokl`, `yiokl'yokl`
infixl 5 `yoikl`, `yoikl'yokl`

infixl 8 `ya`

infixl 8 `yu`
infixl 7 `yu_`
infixl 6 `yu__`
infixl 5 `yu___`
infixl 4 `yu____`
infixl 3 `yu_____`
infixl 2 `yu______`
infixl 1 `yu_______`

infixl 8 `yp`, `yp'yo`, `yp'yo'hd`, `yp'yu`, `yp'yp`, `yp'yp'yo`, `yp'ys`, `yp'yok`, `yp'yokl` --, `yp'yp'jt`, `yp'yp'jt'yok`
infixl 7 `yp_'yo`-- , `yip`, `yip'yo`, `yip'yp`, `yip'yip`, `yip'yis`

infixl 8 `ys`, `ys'yo`, `ys'yu`
-- infixl 7 `yis`

infixl 8 `yr`, `yr'yo`, `yr'yokl`

infixl 7 `yoi`

infixl 7 `yai` --, `yai'yukl`
 , `yai'ydi`, `yai'ydi'ydi`, `yai'yij`

infixl 7 `yui` --, `yui'he`

infixl 7 `yio`, `yio'yokl`, `yio'yukl`, `yio'yokl'yokl`, `yio'yokl'yukl`, `yio'yoikl`
 , `yio'yp`, `yio'yij`, `yio'ydi`, `yio'ydi'ydi`, `yio'yij'yij`

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
 :: Category target => target e e
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
 :: forall source target a o .
 Precategory target =>
 Covariant Yoneda Functor source target I =>
 Elicitable T'II'I target (T'I'II source a o) =>
 Elicitable T'I'II target (I o) =>
 a -> target (source a o) o
yi x = unwrap `compose` yoneda @T'I'II @Functor (Identity x) `compose` wrap

yi_ = yi
yi__ = yi
yi___ = yi
yi____ = yi
yi_____ = yi
yi______ = yi
yi_______ = yi

yo, yo_, yo__, yo___, yo____, yo_____, yo______, yo_______, yi'yo
 :: forall source target t a o .
 Precategory target =>
 Covariant Yoneda Functor source target t =>
 (forall e ee . Wrapper target (T'I'II source e ee)) =>
 t a -> target (source a o) (t o)
yo x = yoneda @T'I'II @Functor x `compose` wrap

yo_ = yo
yo__ = yo
yo___ = yo
yo____ = yo
yo_____ = yo
yo______ = yo
yo_______ = yo
yi'yo = yo

yo'yoo :: forall source target t tt a o .
 Covariant Yoneda Functor source target (T'I t) =>
 Covariant Semi Functor source source (T'I'I tt) =>
 (forall e . Wrapper source (T'I'I tt e)) =>
 (forall e ee . Wrapper target (T'I'II source e ee)) =>
 Contravariant Functor (AR) (AR) (T'II'I target (t (tt o o))) =>
 t (tt a a) -> target (source a o) (t (tt o o))
yo'yoo x = fai (foo @source @source @tt) (yo @source @target x)

yo'yuu :: forall target t tt a aa o .
 Precategory target =>
 Covariant Yoneda Functor target target (T'I t) =>
 Covariant Functor target target (T'I'II tt a) =>
 Covariant Functor target target (T'II'I tt o) =>
 (forall e ee . Wrapper target (T'I'II tt e ee)) =>
 (forall e ee . Wrapper target (T'II'I tt e ee)) =>
 (forall e ee . Wrapper target (T'I'II target e ee)) =>
 (forall e . Wrapper (AR) (target Unit e)) =>
 Terminal target =>
 Contravariant Functor (AR) (AR) (T'II'I target (t (tt o o))) =>
 t (tt a aa) -> target (Supertype (target Unit o)) (t (tt o o))
yo'yuu x = fai (fuu @target @target @tt) (yo @target @target x)

yoo :: forall source target t a o .
 Precategory target =>
 Covariant Yoneda Functor source target (T'I'I t) =>
 (forall e . Wrapper target (T'I'I t e)) =>
 (forall e ee . Wrapper target (T'I'II source e ee)) =>
 t a a -> target (source a o) (t o o)
yoo = fio @target unwrap `compose` yo @source @target @(T'I'I t) `compose` wrap

yoi :: forall source target t i a o .
 Precategory target =>
 Covariant Yoneda Functor source target (T'II'I t i) =>
 (forall e ee . Wrapper target (T'I'II source e ee)) =>
 (forall e . Wrapper target (T'II'I t i e)) =>
 t a i -> target (source a o) (t o i)
yoi = fio @target unwrap `compose` yo @source @target @(T'II'I t i) `compose` wrap

-- TODO: add Hom functor aliases here
yio :: forall source target t i a o .
 Precategory target =>
 Covariant Yoneda Functor source target (T'I'II t i) =>
 (forall e ee . Wrapper target (T'I'II source e ee)) =>
 (forall e . Wrapper target (T'I'II t i e)) =>
 t i a -> target (source a o) (t i o)
yio = fio @target unwrap `compose` yo @source @target @(T'I'II t i) `compose` wrap

-- yioi :: forall source target w e eee a o .
--  Precategory target =>
--  Covariant Yoneda Functor source target (W_III_I_II w eee e) =>
--  Wrapper target (T'I'II source a o) =>
--  Elicitable T'I'II target (W_III_I_II w eee e o) =>
--  w e a eee -> target (source a o) (w e o eee)
-- yioi x = compose unwrap (yoneda @T'I'II @source @target @(W_III_I_II _ _ _) (wrap x))

yu, yu_, yu__, yu___, yu____, yu_____, yu______, yu_______, li'yu :: forall target t a o .
 Covariant Yoneda Functor target target t =>
 Mapping T'I'II T'I'II target target I (T'I'II target a) =>
 Wrapper target (T'I'II target a o) =>
 Wrapper target (I o) =>
 t a -> target o (t o)
yu x = yoneda @T'I'II @Functor @target @target x `compose` wrap `compose` constant

yu_ = yu
yu__ = yu
yu___ = yu
yu____ = yu
yu_____ = yu
yu______ = yu
yu_______ = yu

li'yu = yu

yui :: forall target t i a o .
 Terminal target =>
 Category target =>
 Covariant Yoneda Functor target target (T'II'I t i) =>
 Covariant Functor target target (T'I'II target a) =>
 Contravariant Functor target target (T'II'I target o) =>
 (forall e ee . Wrapper target (T'II'I target e ee)) =>
 (forall e ee . Wrapper target (T'I'II target e ee)) =>
 (forall e . Wrapper target (T'II'I t i e)) =>
 Wrapper target (target Unit o) =>
 t a i -> target (Supertype (target Unit o)) (t o i)
yui x = yoi @target x `compose` fai @target terminal `compose` wrap

yiu, hu, hu_, hu__, hu___, hu____, hu_____, hu______, hu_______, hu________
 :: forall target t i a o .
 Terminal target =>
 Category target =>
 Covariant Yoneda Functor target target (T'I'II t i) =>
 Covariant Functor target target (T'I'II target a) =>
 Contravariant Functor target target (T'II'I target o) =>
 (forall e . Wrapper target (T'I'II t i e)) =>
 (forall e ee . Wrapper target (T'I'II target e ee)) =>
 (forall e ee . Wrapper target (T'II'I target e ee)) =>
 (forall e . Wrapper target (target () e)) =>
 t i a -> target (Supertype (target Unit o)) (t i o)
yiu x = yio @target x `compose` fai @target terminal `compose` wrap

hu = yiu
hu_ = yiu
hu__ = yiu
hu___ = yiu
hu____ = yiu
hu_____ = yiu
hu______ = yiu
hu_______ = yiu
hu________ = yiu

yiu'he --, hu'he, hu_'he, hu__'he, hu___'he, hu____'he, hu_____'he, hu______'he, hu_______'he, hu________'he
 :: forall target t i a o .
 Terminal target =>
 Category target =>
 Covariant Yoneda Functor target target (T'I'II t i) =>
 Covariant Functor target target (T'I'II target a) =>
 Contravariant Functor target target (T'II'I target o) =>
 Wrapper target (target Unit o) =>
 (forall e . Wrapper target (T'I'II t i e)) =>
 (forall e ee . Wrapper target (T'I'II target e ee)) =>
 (forall e ee . Wrapper target (T'II'I target e ee)) =>
 Wrapper target (Supertype (target Unit o)) =>
 Wrapper target o =>
 Wrapper target (T'II'I target o Unit) =>
 (forall e . Wrapper target (T'I'II t i e)) =>
 t i a -> target (Supertype (target Unit o)) (t i (Supertype o))
yiu'he = fai @target (fio (unwrap @target @o) `compose` fai @target terminal `compose` wrap) `compose` yio @target

hu'he
 :: forall target t i a o .
 Terminal target =>
 Category target =>
 Covariant Yoneda Functor target target (T'I'II t i) =>
 Covariant Functor target target (T'I'II target a) =>
 Contravariant Functor target target (T'II'I target o) =>
 Wrapper target (target Unit o) =>
 (forall e . Wrapper target (T'I'II t i e)) =>
 (forall e ee . Wrapper target (T'I'II target e ee)) =>
 (forall e ee . Wrapper target (T'II'I target e ee)) =>
 Wrapper target (Supertype (target Unit o)) =>
 Wrapper target o =>
 Wrapper target (T'II'I target o Unit) =>
 (forall e . Wrapper target (T'I'II t i e)) =>
 t i a -> target (Supertype (target Unit o)) (t i (Supertype o))
hu'he = fai @target (fio (unwrap @target @o) `compose` fai @target terminal `compose` wrap) `compose` yio @target

hu_'he
 :: forall target t i a o .
 Terminal target =>
 Category target =>
 Covariant Yoneda Functor target target (T'I'II t i) =>
 Covariant Functor target target (T'I'II target a) =>
 Contravariant Functor target target (T'II'I target o) =>
 Wrapper target (target Unit o) =>
 (forall e . Wrapper target (T'I'II t i e)) =>
 (forall e ee . Wrapper target (T'I'II target e ee)) =>
 (forall e ee . Wrapper target (T'II'I target e ee)) =>
 Wrapper target (Supertype (target Unit o)) =>
 Wrapper target o =>
 Wrapper target (T'II'I target o Unit) =>
 (forall e . Wrapper target (T'I'II t i e)) =>
 t i a -> target (Supertype (target Unit o)) (t i (Supertype o))
hu_'he = fai @target (fio (unwrap @target @o) `compose` fai @target terminal `compose` wrap) `compose` yio @target

hu__'he
 :: forall target t i a o .
 Terminal target =>
 Category target =>
 Covariant Yoneda Functor target target (T'I'II t i) =>
 Covariant Functor target target (T'I'II target a) =>
 Contravariant Functor target target (T'II'I target o) =>
 Wrapper target (target Unit o) =>
 (forall e . Wrapper target (T'I'II t i e)) =>
 (forall e ee . Wrapper target (T'I'II target e ee)) =>
 (forall e ee . Wrapper target (T'II'I target e ee)) =>
 Wrapper target (Supertype (target Unit o)) =>
 Wrapper target o =>
 Wrapper target (T'II'I target o Unit) =>
 (forall e . Wrapper target (T'I'II t i e)) =>
 t i a -> target (Supertype (target Unit o)) (t i (Supertype o))
hu__'he = fai @target (fio (unwrap @target @o) `compose` fai @target terminal `compose` wrap) `compose` yio @target

hu___'he
 :: forall target t i a o .
 Terminal target =>
 Category target =>
 Covariant Yoneda Functor target target (T'I'II t i) =>
 Covariant Functor target target (T'I'II target a) =>
 Contravariant Functor target target (T'II'I target o) =>
 Wrapper target (target Unit o) =>
 (forall e . Wrapper target (T'I'II t i e)) =>
 (forall e ee . Wrapper target (T'I'II target e ee)) =>
 (forall e ee . Wrapper target (T'II'I target e ee)) =>
 Wrapper target (Supertype (target Unit o)) =>
 Wrapper target o =>
 Wrapper target (T'II'I target o Unit) =>
 (forall e . Wrapper target (T'I'II t i e)) =>
 t i a -> target (Supertype (target Unit o)) (t i (Supertype o))
hu___'he = fai @target (fio (unwrap @target @o) `compose` fai @target terminal `compose` wrap) `compose` yio @target

hu____'he
 :: forall target t i a o .
 Terminal target =>
 Category target =>
 Covariant Yoneda Functor target target (T'I'II t i) =>
 Covariant Functor target target (T'I'II target a) =>
 Contravariant Functor target target (T'II'I target o) =>
 Wrapper target (target Unit o) =>
 (forall e . Wrapper target (T'I'II t i e)) =>
 (forall e ee . Wrapper target (T'I'II target e ee)) =>
 (forall e ee . Wrapper target (T'II'I target e ee)) =>
 Wrapper target (Supertype (target Unit o)) =>
 Wrapper target o =>
 Wrapper target (T'II'I target o Unit) =>
 (forall e . Wrapper target (T'I'II t i e)) =>
 t i a -> target (Supertype (target Unit o)) (t i (Supertype o))
hu____'he = fai @target (fio (unwrap @target @o) `compose` fai @target terminal `compose` wrap) `compose` yio @target

hu_____'he
 :: forall target t i a o .
 Terminal target =>
 Category target =>
 Covariant Yoneda Functor target target (T'I'II t i) =>
 Covariant Functor target target (T'I'II target a) =>
 Contravariant Functor target target (T'II'I target o) =>
 Wrapper target (target Unit o) =>
 (forall e . Wrapper target (T'I'II t i e)) =>
 (forall e ee . Wrapper target (T'I'II target e ee)) =>
 (forall e ee . Wrapper target (T'II'I target e ee)) =>
 Wrapper target (Supertype (target Unit o)) =>
 Wrapper target o =>
 Wrapper target (T'II'I target o Unit) =>
 (forall e . Wrapper target (T'I'II t i e)) =>
 t i a -> target (Supertype (target Unit o)) (t i (Supertype o))
hu_____'he = fai @target (fio (unwrap @target @o) `compose` fai @target terminal `compose` wrap) `compose` yio @target

hu______'he
 :: forall target t i a o .
 Terminal target =>
 Category target =>
 Covariant Yoneda Functor target target (T'I'II t i) =>
 Covariant Functor target target (T'I'II target a) =>
 Contravariant Functor target target (T'II'I target o) =>
 Wrapper target (target Unit o) =>
 (forall e . Wrapper target (T'I'II t i e)) =>
 (forall e ee . Wrapper target (T'I'II target e ee)) =>
 (forall e ee . Wrapper target (T'II'I target e ee)) =>
 Wrapper target (Supertype (target Unit o)) =>
 Wrapper target o =>
 Wrapper target (T'II'I target o Unit) =>
 (forall e . Wrapper target (T'I'II t i e)) =>
 t i a -> target (Supertype (target Unit o)) (t i (Supertype o))
hu______'he = fai @target (fio (unwrap @target @o) `compose` fai @target terminal `compose` wrap) `compose` yio @target

hu_______'he
 :: forall target t i a o .
 Terminal target =>
 Category target =>
 Covariant Yoneda Functor target target (T'I'II t i) =>
 Covariant Functor target target (T'I'II target a) =>
 Contravariant Functor target target (T'II'I target o) =>
 Wrapper target (target Unit o) =>
 (forall e . Wrapper target (T'I'II t i e)) =>
 (forall e ee . Wrapper target (T'I'II target e ee)) =>
 (forall e ee . Wrapper target (T'II'I target e ee)) =>
 Wrapper target (Supertype (target Unit o)) =>
 Wrapper target o =>
 Wrapper target (T'II'I target o Unit) =>
 (forall e . Wrapper target (T'I'II t i e)) =>
 t i a -> target (Supertype (target Unit o)) (t i (Supertype o))
hu_______'he = fai @target (fio (unwrap @target @o) `compose` fai @target terminal `compose` wrap) `compose` yio @target

hu________'he
 :: forall target t i a o .
 Terminal target =>
 Category target =>
 Covariant Yoneda Functor target target (T'I'II t i) =>
 Covariant Functor target target (T'I'II target a) =>
 Contravariant Functor target target (T'II'I target o) =>
 Wrapper target (target Unit o) =>
 (forall e . Wrapper target (T'I'II t i e)) =>
 (forall e ee . Wrapper target (T'I'II target e ee)) =>
 (forall e ee . Wrapper target (T'II'I target e ee)) =>
 Wrapper target (Supertype (target Unit o)) =>
 Wrapper target o =>
 Wrapper target (T'II'I target o Unit) =>
 (forall e . Wrapper target (T'I'II t i e)) =>
 t i a -> target (Supertype (target Unit o)) (t i (Supertype o))
hu________'he = fai @target (fio (unwrap @target @o) `compose` fai @target terminal `compose` wrap) `compose` yio @target

he'yiu, he'hu, he'hu_, he'hu__, he'hu___, he'hu____, he'hu_____, he'hu______, he'hu_______, he'hu________
 :: forall target t i a o .
 Terminal target =>
 Category target =>
 Covariant Yoneda Functor target target (T'I'II t i) =>
 Contravariant Functor target (AR) (T'II'I t a) =>
 Covariant Functor target target (T'I'II target a) =>
 Contravariant Functor target target (T'II'I target o) =>
 Wrapper target (target Unit o) =>
 Wrapper target (Supertype (target Unit o)) =>
 (forall e ee . Wrapper target (T'I'II target e ee)) =>
 (forall e ee . Wrapper target (T'II'I target e ee)) =>
 (forall e . Wrapper target (T'II'I target e Unit)) =>
 (forall e . Wrapper target (T'I'II t i e)) =>
 Wrapper target i =>
 t (Supertype i) a -> target (Supertype (target Unit o)) (t i o)
he'yiu x = yio @target (fai @target unwrap x) `compose` fai @target terminal `compose` wrap

he'hu = he'yiu
he'hu_ = he'yiu
he'hu__ = he'yiu
he'hu___ = he'yiu
he'hu____ = he'yiu
he'hu_____ = he'yiu
he'hu______ = he'yiu
he'hu_______ = he'yiu
he'hu________ = he'yiu

yd :: forall source target t tt a o .
 Adjoint Functor target target t tt =>
 Covariant Yoneda Functor source target (t `T'TT'I` tt) =>
 (forall e . Wrapper target ((t `T'TT'I` tt) e)) =>
 Wrapper target (I o) =>
 (forall e ee . Wrapper target (T'I'II source e ee)) =>
 t (tt a) -> target (source a o) o
yd x = unwrap @target
 `compose` component @target @(t `T'TT'I` tt) @I
 `compose` yo (wrap x)

ydi, hd, hd_, hd__, hd___, hd____, hd_____, hd______, hd_______, hd________ :: forall source target t tt i ii a o .
 Adjoint Functor target target (T'II'I t i) (T'I'II tt ii) =>
 Covariant Endo Semi Functor (AR) (T'II'I t i) =>
 Covariant Yoneda Functor source target (T'II'I t i `T'TT'I` T'I'II tt ii) =>
 (forall e . Wrapper target ((T'II'I t i `T'TT'I` T'I'II tt ii) e)) =>
 (forall e . Wrapper target (I e)) =>
 (forall e ee . Wrapper target (T'I'II source e ee)) =>
 (forall e ee . Wrapper source (T'I'II tt e ee)) =>
 (forall e ee . Wrapper source (T'II'I t e ee)) =>
 t (tt ii a) i -> target (source a o) o
ydi x = unwrap @target
 `compose` component @target @(T'II'I t i `T'TT'I` T'I'II tt ii) @I
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

yj :: forall source target t tt a o .
 Adjoint Functor (AR) (AR) t tt =>
 Covariant Yoneda Functor source target (tt `T'TT'I` t) =>
 (forall e . Wrapper target ((tt `T'TT'I` t) e)) =>
 Wrapper target (I o) =>
 (forall e ee . Wrapper target (T'I'II source e ee)) =>
 a -> target (source a o) (tt (t o))
yj x = unwrap @target `compose` yo (component @(AR) @I @(tt `T'TT'I` t) (wrap x))

yij, hj, hj_, hj__, hj___, hj____, hj_____, hj______, hj_______, hj________ :: forall source target t tt i ii a o .
 Adjoint Functor (AR) (AR) (t `T'II'I` i) (T'I'II tt ii) =>
 Covariant Yoneda Functor source target (T'I'II tt ii `T'TT'I` T'II'I t i) =>
 Covariant Endo Semi Functor target (T'I'II tt ii) =>
 (forall e . Wrapper target ((T'I'II tt ii `T'TT'I` T'II'I t i) e)) =>
 (forall e . Wrapper target (I e)) =>
 (forall e . Wrapper target (T'II'I t i e)) =>
 (forall e . Wrapper target (T'I'II tt ii e)) =>
 (forall e ee . Wrapper target (T'I'II source e ee)) =>
 a -> target (source a o) (tt ii (t o i))
yij x = unwrap @target `compose` fo (unwrap @target)
 `compose` wrapped (yoneda @T'I'II @Functor @source (component @(AR) @I @(T'I'II tt ii `T'TT'I` T'II'I t i) (wrap x)))

hj = yij
hj_ = yij
hj__ = yij
hj___ = yij
hj____ = yij
hj_____ = yij
hj______ = yij
hj_______ = yij
hj________ = yij

ydi'ydi, hd'hd :: forall source target t tt ttt tttt i ii iii iiii a o .
 Adjoint Functor source source (T'II'I ttt iii) (T'I'II tttt iiii) =>
 Adjoint Functor target target (T'II'I t i) (T'I'II tt ii) =>
 Covariant Endo Semi Functor (AR) (T'II'I t i) =>
 Covariant Endo Semi Functor source (T'II'I ttt iii) =>
 Covariant Endo Semi Functor target (T'I'II tt ii) =>
 Covariant Endo Semi Functor source (T'I'II tttt iiii) =>
 Covariant Endo Semi Functor target (T'II'I t i) =>
 Covariant Yoneda Functor source target (T'II'I t i `T'TT'I` T'I'II tt ii) =>
 Contravariant Endo Semi Functor (AR) (T'II'I target o) =>
 (forall e ee . Wrapper source (T'II'I t e ee)) =>
 (forall e ee . Wrapper source (T'I'II tt e ee)) =>
 (forall e ee . Wrapper source (T'II'I ttt e ee)) =>
 (forall e ee . Wrapper source (T'I'II tttt e ee)) =>
 (forall e ee . Wrapper target (T'I'II source e ee)) =>
 (forall e . Wrapper source (I e)) =>
 (forall e . Wrapper target (I e)) =>
 (forall e . Wrapper target (T'II'I t i `T'TT'I` T'I'II tt ii `T'I_` e)) =>
 (forall e . Wrapper target (T'I'II tt ii `T'TT'I` T'II'I t i `T'I_` e)) =>
 (forall e . Wrapper source (T'II'I ttt iii `T'TT'I` T'I'II tttt iiii `T'I_` e)) =>
 t (tt ii (ttt a iii)) i `AR___` target (source a (tttt iiii o)) o
ydi'ydi x = fai @(AR) fdi (ydi @source @target x)

hd'hd = ydi'ydi

ydi'yij, hd'hj :: forall source target t tt ttt tttt i ii iii iiii a o .
 Contravariant Endo Semi Functor (AR) (T'II'I target (tttt iiii o)) =>
 Covariant Yoneda Functor source target (T'II'I t i `T'TT'I` T'I'II tt ii) =>
 Covariant Endo Semi Functor source (T'II'I ttt iii) =>
 Covariant Endo Semi Functor target (T'II'I t i) =>
 Covariant Endo Semi Functor (AR) (T'II'I t i) =>
 Adjoint Functor target target (T'II'I t i) (T'I'II tt ii) =>
 Adjoint Functor source source (T'II'I ttt iii) (T'I'II tttt iiii) =>
 (forall e . Wrapper target (I e)) =>
 (forall e . Wrapper source (I e)) =>
 (forall e ee . Wrapper source (T'II'I t e ee)) =>
 (forall e ee . Wrapper source (T'II'I ttt e ee)) =>
 (forall e ee . Wrapper source (T'I'II tt e ee)) =>
 (forall e ee . Wrapper source (T'I'II tttt e ee)) =>
 (forall e ee . Wrapper target (T'I'II source e ee)) =>
 (forall e . Wrapper source (T'I'II tttt iiii `T'TT'I` T'II'I ttt iii `T'I_` e)) =>
 (forall e . Wrapper target (T'I'II tt ii `T'TT'I` T'II'I t i `T'I_` e)) =>
 (forall e . Wrapper target (T'II'I t i `T'TT'I` T'I'II tt ii `T'I_` e)) =>
 t (tt ii a) i `AR___` target (source (ttt a iii) o) (tttt iiii o)
ydi'yij x = fai @(AR) fij (ydi @source @target x)

hd'hj = ydi'yij

-- yij'ydi --, hj'hd
 -- :: forall source target t tt ttt tttt i ii iii iiii a o .
 -- Contravariant Endo Semi Functor (AR) (T'II'I target (tt ii (t o i))) =>
 -- Covariant Yoneda Functor source target (T'I'II tt ii `T'TT'I` T'II'I t i) =>
 -- Covariant Endo Semi Functor source (T'I'II ttt iii) =>
 -- Covariant Endo Semi Functor source (T'II'I tttt iiii) =>
 -- Covariant Endo Semi Functor target (T'I'II tt ii) =>
 -- Covariant Endo Semi Functor (AR) (T'II'I t i) =>
 -- Covariant Endo Semi Functor (AR) (T'I'II tt ii) =>
 -- Adjoint Functor source target (T'II'I t i) (T'I'II tt ii) =>
 -- Adjoint Functor source source (T'II'I ttt iii) (T'I'II tttt iiii) =>
 -- (forall e . Wrapper target (I e)) =>
 -- (forall e ee . Wrapper target (T'II'I t e ee)) =>
 -- (forall e ee . Wrapper target (T'I'II tt e ee)) =>
 -- (forall e ee . Wrapper source (T'I'II tttt e ee)) =>
 -- (forall e ee . Wrapper source (T'II'I ttt e ee)) =>
 -- (forall e ee . Wrapper target (T'I'II source e ee)) =>
 -- (forall e . Wrapper source (T'I'II ttt iii `T'TT'I`T'II'I tttt iiii  `T'I_` e)) =>
 -- (forall e . Wrapper target (T'I'II tt ii `T'TT'I` T'II'I t i `T'I_` e)) =>
 -- (forall e . Wrapper target (T'II'I t i `T'TT'I` T'I'II tt ii `T'I_` e)) =>
 -- tttt a iiii `AR___` target (source a (ttt iii o)) (tt ii (t o i))
-- yij'ydi x = fai fdi (yij @source @target x)

-- hj'hd = yij'ydi

-- TODO: should become obsolete as soon as we get used to generate these types of operators
-- yo'hj :: forall source target t tt ttt e a o .
--  Precategory target =>
--  Adjoint Functor source source (T'II'I ttt e) (T'I'II tt e) =>
--  Covariant Functor source source (T'I'II tt e) =>
--  Covariant Yoneda Functor source target t =>
--  (forall ee . Wrapper source ((T'TT'I (T'I'II tt e) (T'II'I ttt e)) ee)) =>
--  (forall ee . Wrapper source ((T'TT'I (T'II'I ttt e) (T'I'II tt e)) ee)) =>
--  (forall ee . Wrapper source (I ee)) =>
--  Wrapper source (T'II'I ttt e a) =>
--  Wrapper source (T'I'II tt e o) =>
--  (forall e ee . Wrapper target (T'I'II source e ee)) =>
--  Contravariant Endo Semi Functor (AR) (T'II'I target (t o)) =>
--  t (ttt a e) -> target (source a (tt e o)) (t o)
-- yo'hj x = fai hj (yo @source @target x)

-- TODO: yo_yo : t (tt a) -> target (source a b) (tt a -> target (source b o) (t (tt o)))

ya :: forall source target t a o .
 Precategory target =>
 Contravariant Yoneda Functor source target t =>
 Elicitable T'II'I target (T'II'I source a o) =>
 t a -> target (source o a) (t o)
ya x = yoneda @T'II'I @Functor x `compose` wrap

yai, ha, ha_, ha__, ha___, ha____, ha_____, ha______, ha_______, ha________ :: forall source target t i a o .
 Precategory target =>
 Contravariant Yoneda Functor source target (T'II'I t i) =>
 Elicitable T'II'I target (T'II'I source a o) =>
 Elicitable T'I'II target (T'II'I t i o) =>
 t a i -> target (source o a) (t o i)
yai x = compose unwrap (yoneda @T'II'I @Functor @source @target @(T'II'I t i) (wrap x) `compose` wrap)

ha = yai
ha_ = yai
ha__ = yai
ha___ = yai
ha____ = yai
ha_____ = yai
ha______ = yai
ha_______ = yai
ha________ = yai

yai'yij :: forall source target t tt ttt i ii iii a o .
 Precategory target =>
 Contravariant Functor source (AR) (T'II'I target (t o i)) =>
 Adjoint Functor source source (T'II'I tt ii) (T'I'II ttt iii) =>
 Covariant Functor source (AR) (T'I'II target (source (tt ii (t o i)) a)) =>
 Contravariant Yoneda Functor source target (T'II'I t i) =>
 Contravariant Endo Semi Functor (AR) (T'II'I target (t o i)) =>
 (forall e ee . Wrapper target (T'II'I source e ee)) =>
 (forall e . Wrapper source (I e)) =>
 (forall e . Wrapper target (T'II'I t i e)) =>
 (forall e . Wrapper source (T'II'I tt ii e)) =>
 (forall e . Wrapper source (T'I'II ttt iii e)) =>
 (forall e . Wrapper source (T'TT'I (T'I'II ttt iii) (T'II'I tt ii) e)) =>
 t (ttt iii a) i -> target (source (tt o ii) a) (t o i)
yai'yij = fai fij `compose` yai @source @target

-- t (ii `AR` a) i -> target ((o `P` ii) `AR` a) (t o i)

yai'ydi, ha'hd :: forall source target t tt ttt i ii iii a o .
 Precategory target =>
 Contravariant Functor source (AR) (T'II'I target (t o i)) =>
 Adjoint Functor source source (T'II'I tt ii) (T'I'II ttt iii) =>
 Covariant Functor source (AR) (T'I'II target (source (tt ii (t o i)) a)) =>
 Covariant Endo Semi Functor source (T'I'II tt ii) =>
 Contravariant Yoneda Functor source target (T'II'I t i) =>
 Contravariant Endo Semi Functor (AR) (T'II'I target (t (tt o ii) i)) =>
 (forall e ee . Wrapper target (T'II'I source e ee)) =>
 (forall e . Wrapper source (I e)) =>
 (forall e . Wrapper target (T'II'I t i e)) =>
 (forall e . Wrapper source (T'II'I tt ii e)) =>
 (forall e . Wrapper source (T'I'II ttt iii e)) =>
 (forall e . Wrapper source (T'TT'I (T'II'I tt ii) (T'I'II ttt iii) e)) =>
 t a i -> target (source o (ttt iii a)) (t (tt o ii) i)
yai'ydi x = fai (fdi @source) (yai @source @target x)

-- t a i `AR__` target (o `AR_` (ii `AR_` a)) (t (o `P` ii) i)

ha'hd = yai'ydi

yai'ydi'ydi, ha'hd'hd :: forall source target t tt ttt tttt ttttt i ii iii iiii iiiii a o .
 Precategory target =>
 Contravariant Functor source (AR) (T'II'I target (t o i)) =>
 Adjoint Functor source source (T'II'I tt ii) (T'I'II ttt iii) =>
 Adjoint Functor source source (T'II'I tttt iiii) (T'I'II ttttt iiiii) =>
 Covariant Functor source (AR) (T'I'II target (source (tt ii (t o i)) a)) =>
 Covariant Endo Semi Functor source (T'I'II tt ii) =>
 Covariant Endo Semi Functor source (T'II'I ttt iii) =>
 Covariant Endo Semi Functor source (T'II'I tttt iiii) =>
 Covariant Endo Semi Functor source (T'I'II ttttt iiiii) =>
 Contravariant Yoneda Functor source target (T'II'I t i) =>
 Contravariant Endo Semi Functor (AR) (T'II'I target (t (tttt (tt o ii) iiii) i)) =>
 (forall e ee . Wrapper target (T'II'I source e ee)) =>
 (forall e . Wrapper source (I e)) =>
 (forall e . Wrapper target (T'II'I t i e)) =>
 (forall e . Wrapper source (T'II'I tt ii e)) =>
 (forall e . Wrapper source (T'I'II ttt iii e)) =>
 (forall e . Wrapper source (T'II'I tttt iiii e)) =>
 (forall e . Wrapper source (T'I'II ttttt iiiii e)) =>
 (forall e . Wrapper source (T'TT'I (T'II'I tt ii) (T'I'II ttt iii) e)) =>
 (forall e . Wrapper source (T'TT'I (T'II'I tttt iiii) (T'I'II ttttt iiiii) e)) =>
 t a i -> target (source o (ttt iii (ttttt iiiii a))) (t (tttt (tt o ii) iiii) i)
yai'ydi'ydi x = fai (fdi @source `compose` fdi @source) (yai @source @target x)

ha'hd'hd = yai'ydi'ydi

yio'ydi, ho'hd, ho_'hd, ho__'hd, ho___'hd, ho____'hd, ho_____'hd, ho______'hd, ho_______'hd, ho________'hd
 :: forall source target t tt ttt i ii iii a o .
 Precategory target =>
 Contravariant Endo Semi Functor (AR) (T'II'I target (t o i)) =>
 Adjoint Functor source source (T'II'I tt ii) (T'I'II ttt iii) =>
 Covariant Functor source (AR) (T'I'II target (source (ttt iii (t o i)) a)) =>
 Covariant Yoneda Functor source target (T'I'II t i) =>
 Covariant Endo Semi Functor source (T'II'I tt ii) =>
 Covariant Endo Semi Functor source (T'I'II ttt iii) =>
 Contravariant Endo Semi Functor (AR) (T'II'I target (t i o)) =>
 (forall e ee . Wrapper target (T'I'II source e ee)) =>
 (forall e . Wrapper source (I e)) =>
 (forall e . Wrapper target (T'I'II t i e)) =>
 (forall e . Wrapper source (T'I'II ttt iii e)) =>
 (forall e . Wrapper source (T'II'I tt ii e)) =>
 (forall e . Wrapper source (T'TT'I (T'II'I tt ii) (T'I'II ttt iii) e)) =>
 t i (tt a ii) -> target (source a (ttt iii o)) (t i o)
yio'ydi x = fai fdi (yio @source @target x)

ho'hd = yio'ydi
ho_'hd = yio'ydi
ho__'hd = yio'ydi
ho___'hd = yio'ydi
ho____'hd = yio'ydi
ho_____'hd = yio'ydi
ho______'hd = yio'ydi
ho_______'hd = yio'ydi
ho________'hd = yio'ydi

yio'ydi'ydi, ho'hd'hd :: forall source target t tt ttt tttt ttttt i ii iii iiii iiiii a o .
 Precategory target =>
 Contravariant Endo Semi Functor (AR) (T'II'I target (t o i)) =>
 Adjoint Functor source source (T'II'I tt ii) (T'I'II ttt iii) =>
 Adjoint Functor source source (T'II'I tttt iiii) (T'I'II ttttt iiiii) =>
 Covariant Functor source (AR) (T'I'II target (source (ttt iii (t o i)) a)) =>
 Covariant Yoneda Functor source target (T'I'II t i) =>
 Covariant Endo Semi Functor source (T'II'I tt ii) =>
 Covariant Endo Semi Functor source (T'I'II ttt iii) =>
 Covariant Endo Semi Functor source (T'II'I tttt iii) =>
 Contravariant Endo Semi Functor (AR) (T'II'I target (t i o)) =>
 (forall e ee . Wrapper target (T'I'II source e ee)) =>
 (forall e . Wrapper source (I e)) =>
 (forall e . Wrapper target (T'I'II t i e)) =>
 (forall e . Wrapper source (T'I'II ttt iii e)) =>
 (forall e . Wrapper source (T'II'I tt ii e)) =>
 (forall e . Wrapper source (T'II'I tttt iiii e)) =>
 (forall e . Wrapper source (T'I'II ttttt iiiii e)) =>
 (forall e . Wrapper source (T'TT'I (T'II'I tt ii) (T'I'II ttt iii) e)) =>
 (forall e . Wrapper source (T'TT'I (T'II'I tttt iiii) (T'I'II ttttt iiiii) e)) => 
 t i (tt (tttt a iiii) ii) -> target (source a (ttttt iiiii (ttt iii o))) (t i o)
yio'ydi'ydi x = fai (fdi @source `compose` fdi @source) (yio @source @target x)

ho'hd'hd = yio'ydi'ydi

yio'yij, ho'hj :: forall source target t tt ttt i ii iii a o .
 Precategory target =>
 Contravariant Endo Semi Functor (AR) (T'II'I target (t o i)) =>
 Adjoint Functor source source (T'II'I tt ii) (T'I'II ttt iii) =>
 Covariant Functor source (AR) (T'I'II target (source (ttt iii (t o i)) a)) =>
 Covariant Yoneda Functor source target (T'I'II t i) =>
 Covariant Endo Semi Functor source (T'II'I tt ii) =>
 Covariant Endo Semi Functor source (T'I'II ttt iii) =>
 Contravariant Endo Semi Functor (AR) (T'II'I target (t i (ttt iii o))) =>
 (forall e ee . Wrapper target (T'I'II source e ee)) =>
 (forall e . Wrapper source (I e)) =>
 (forall e . Wrapper target (T'I'II t i e)) =>
 (forall e . Wrapper source (T'I'II ttt iii e)) =>
 (forall e . Wrapper source (T'II'I tt ii e)) =>
 (forall e . Wrapper source (T'TT'I (T'I'II ttt iii) (T'II'I tt ii) e)) =>
 t i a -> target (source (tt a ii) o) (t i (ttt iii o))
yio'yij x = fai fij (yio @source @target x)

-- t i a -> target (source (a `P` ii) o) (t i (ii `AR` o))


ho'hj = yio'yij

yio'yij'yij, ho'hj'hj :: forall source target t tt ttt tttt ttttt i ii iii iiii iiiii a o .
 Precategory target =>
 Contravariant Endo Semi Functor (AR) (T'II'I target (t o i)) =>
 Adjoint Functor source source (T'II'I tt ii) (T'I'II ttt iii) =>
 Adjoint Functor source source (T'II'I tttt iiii) (T'I'II ttttt iiiii) =>
 Covariant Functor source (AR) (T'I'II target (source (ttt iii (t o i)) a)) =>
 Covariant Yoneda Functor source target (T'I'II t i) =>
 Covariant Endo Semi Functor source (T'II'I tt ii) =>
 Covariant Endo Semi Functor source (T'I'II ttt iii) =>
 Contravariant Endo Semi Functor (AR) (T'II'I target (t i (ttttt iiiii (ttt iii o)))) =>
 (forall e ee . Wrapper target (T'I'II source e ee)) =>
 (forall e . Wrapper source (I e)) =>
 (forall e . Wrapper target (T'I'II t i e)) =>
 (forall e . Wrapper source (T'II'I tt ii e)) =>
 (forall e . Wrapper source (T'I'II ttt iii e)) =>
 (forall e . Wrapper source (T'II'I tttt iiii e)) =>
 (forall e . Wrapper source (T'I'II ttttt iiiii e)) =>
 (forall e . Wrapper source (T'TT'I (T'I'II ttt iii) (T'II'I tt ii) e)) =>
 (forall e . Wrapper source (T'TT'I (T'I'II ttttt iiiii) (T'II'I tttt iiii) e)) =>
 t i a -> target (source (tt (tttt a iiii) ii) o) (t i (ttttt iiiii (ttt iii o)))
yio'yij'yij = fai (fij @source `compose` fij @source) `compose` yio @source @target

ho'hj'hj = yio'yij'yij

-- t i a -> target (source (a `P` iii `P` ii) o) (t i (iii `AR` (ii `AR` o)))

yia :: forall source target t e a o .
 Precategory target =>
 Contravariant Yoneda Functor source target (T'I'II t e) =>
 Elicitable T'II'I target (T'II'I source a o) =>
 Elicitable T'I'II target (T'I'II t e o) =>
 t e a -> target (source o a) (t e o)
yia x = compose unwrap (yoneda @T'II'I @Functor @source @target @(T'I'II t e) (wrap x) `compose` wrap)

yok, yok_, yok__, yok___, yok____, yok_____, yok______
 , li'yok, li_'yok, li__'yok, li___'yok, li____'yok, li_____'yok, li______'yok, li_______'yok
 :: forall source target t tt ll a o .
 Covariant Endo Transformation Functor target (t `T'TT'I` tt `L` tt `T` ll) t =>
 Covariant Yoneda Functor source target t =>
 (forall e ee . Wrapper target (T'I'II source e ee)) =>
 (forall e . Wrapper target (t `T'TT'I` tt `L` tt `T` ll `T'I_` e)) =>
 t a -> target (source a (tt `L` tt `T` ll `T` o)) (t o)
yok x = component @target @(T'TT'I t (tt `L` tt `T` ll))
 `compose` wrap @target @(T'TT'I t (tt `L` tt `T` ll) _)
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
--  :: forall source target tt t l a o .
--  Covariant Endo Transformation Functor target (T'TT'I t (tt `L` tt `T` l)) t =>
--  Covariant Semi Functor target target tt =>
--  Covariant Yoneda Functor source target t =>
--  Contravariant Semi Functor source target (T'II'I source (tt `L` tt `T` l `T` o)) =>
--  (forall e ee . Wrapper target (T'II'I source (tt `L` tt `T` ll `T` e) ee)) =>
--  (forall e ee . Wrapper target (T'I'II source (tt `L` tt `T` ll `T` e) ee)) =>
--  (forall e . Wrapper target (T'TT'I t (tt `L` tt `T` l) e)) =>
--  Wrapper target (T'TT'I t (tt `L` tt `T` l) o) =>
--  Elicitable T'I'II source a =>
--  t a -> target (source (Supertype a) (tt `L` tt `T` l `T` o)) (t o)
-- yok'he x = yok @source @target x `compose` fai @source he

-- yok_'he = yok'he
-- yok__'he = yok'he
-- yok___'he = yok'he
-- yok____'he = yok'he
-- yok_____'he = yok'he
-- yok______'he = yok'he

-- yok'he'he, yok_'he'he, yok__'he'he, yok___'he'he, yok____'he'he, yok_____'he'he, yok______'he'he
--  :: forall source target tt t l a o .
--  Covariant Endo Transformation Functor target (T'TT'I t (tt `L` tt `T` l)) t =>
--  Covariant Semi Functor target target tt =>
--  Covariant Yoneda Functor source target t =>
--  Contravariant Semi Functor source target (T'II'I source (tt `L` tt `T` l `T` o)) =>
--  Wrapper target (T'I'II source a (tt `L` tt `T` l `T` o)) =>
--  Wrapper target (T'II'I source (tt `L` tt `T` l `T` o) a) =>
--  Wrapper target (T'II'I source (tt `L` tt `T` l `T` o) (Supertype (Supertype a))) =>
--  (forall e . Wrapper target (T'TT'I t (tt `L` tt `T` l) e)) =>
--  Elicitable T'I'II source a =>
--  Elicitable T'I'II source (Supertype a) =>
--  t a -> target (source (Supertype (Supertype a)) (tt `L` tt `T` l `T` o)) (t o)
-- yok'he'he x = yok @source @target x `compose` fai @source he'he

-- yok_'he'he = yok'he'he
-- yok__'he'he = yok'he'he
-- yok___'he'he = yok'he'he
-- yok____'he'he = yok'he'he
-- yok_____'he'he = yok'he'he
-- yok______'he'he = yok'he'he

yuk, yuk_, yuk__, yuk___, yuk____, yuk_____, yuk______, yi'yuk
 :: forall target tt t l a o .
 Covariant Yoneda Functor target target t =>
 Covariant Endo Transformation Functor target (T'TT'I t (tt `L` tt `T` l)) t =>
 Mapping T'I'II T'I'II target target I (T'I'II target a) =>
 (forall e . Wrapper target ((t `T'TT'I` tt `L` tt `T` l) e)) =>
 (forall e ee . Wrapper target (T'I'II target e ee)) =>
 Wrapper target (I (tt `L` tt `T` l `T` o)) =>
 t a -> target (tt `L` tt `T` l `T` o) (t o)
yuk x = yok @target @target x `compose` constant

yuk_ = yuk @target @tt
yuk__ = yuk @target @tt
yuk___ = yuk @target @tt
yuk____ = yuk @target @tt
yuk_____ = yuk @target @tt
yuk______ = yuk @target @tt
yi'yuk = yuk @target @tt

kyo :: forall source target t tt ll a o .
 Component (AR) t (t `T'TT'I` tt `L` tt `T` ll) =>
 Covariant Yoneda Functor source target t =>
 (forall e . Covariant Functor source target (T'I'II source e)) =>
 (forall e . Contravariant Functor source target (T'II'I source e)) =>
 (forall e ee . Wrapper target (T'I'II source e ee)) =>
 (forall e ee . Wrapper target (T'II'I source e ee)) =>
 (forall e . Wrapper source (I e)) =>
 (forall e . Wrapper source (I `L` tt `T` ll `T'I` e)) =>
 (forall e . Wrapper source (tt `L` tt `T` ll `T'I` e)) =>
 t a -> target (source (tt a) (I `L` tt `T` ll `T` o)) (t o)
kyo x = fai @target (fai @source unwrap `compose` fio @source (unwrap @_ @(I _) `compose` unwrap))
 `compose` yo @source @target @t
 `compose` unwrap `identity` component @(AR) @t @(t `T'TT'I` tt `L` tt `T` ll) x

kyok :: forall source target t tt ttt l ll lll a o .
 Covariant Yoneda Functor source target t =>
 Component (AR) t (t `T'TT'I` tt `L` tt `T` ll) =>
 Component source (t `T'TT'I` ttt `L` ttt `T` lll) t =>
 (forall e . Contravariant Functor source target (T'II'I source e)) =>
 (forall e . Covariant Functor source target (T'I'II source e)) =>
 (forall e . Covariant Functor source (AR) (T'I'II target e)) =>
 (forall e ee . Wrapper target (T'I'II source e ee)) =>
 (forall e ee . Wrapper target (T'II'I source e ee)) =>
 (forall e . Wrapper source (I `L` tt `T` ll `T` e)) =>
 (forall e . Wrapper source (tt `L` tt `T` ll `T` e)) =>
 (forall e . Wrapper source (t `TT'T'I` ttt `T'I_` e)) =>
 (forall e . Wrapper source (t `T'TT'I` ttt `L` ttt `T` lll `T'I_` e)) =>
 (forall e . Wrapper source (I e)) =>
 t a -> target (source (tt a) (I `L` tt `T` ll `T'I` ttt `L` ttt `T` lll `T` o)) (t o)
kyok = fio @source (component @source @(t `T'TT'I` ttt `L` ttt `T` lll) @t `compose` wrap)
 `compose` kyo @source @target @t @tt @ll

kyokl :: forall source target t tt ttt l ll lll a o .
 Covariant Yoneda Functor source target t =>
 Component (AR) t (t `T'TT'I` tt `L` tt `T` ll) =>
 Component source (t `T'TT'I` ttt `L` ttt `T` lll `L` t `T` l) (t `TT'T'I` ttt) =>
 (forall e . Contravariant Functor source target (T'II'I source e)) =>
 (forall e . Covariant Functor source target (T'I'II source e)) =>
 (forall e . Covariant Functor source (AR) (T'I'II target e)) =>
 (forall e ee . Wrapper target (T'I'II source e ee)) =>
 (forall e ee . Wrapper target (T'II'I source e ee)) =>
 (forall e . Wrapper source (I `L` tt `T` ll `T` e)) =>
 (forall e . Wrapper source (tt `L` tt `T` ll `T` e)) =>
 (forall e . Wrapper source (t `TT'T'I` ttt `T'I_` e)) =>
 (forall e . Wrapper source (t `T'TT'I` ttt `L` ttt `T` lll `L` t `T` l `T'I_` e)) =>
 (forall e . Wrapper source (I e)) =>
 t a -> target (source (tt a) (I `L` tt `T` ll `T'I` ttt `L` ttt `T` lll `L` t `T` l `T` o)) (ttt (t o))
kyokl = fio @source (wrapped (component @source @(t `T'TT'I` ttt `L` ttt `T` lll `L` t `T` l) @(t `TT'T'I` ttt)))
 `compose` kyo @source @target @t @tt @ll

yokl, yokl_, yokl__, yokl___, yokl____, yokl_____, li'yokl ::
 forall source target t tt l ll a o .
 -- Category target =>
 Covariant Endo Transformation Functor target (t `T'TT'I` tt `L` tt `T` ll `L` t `T` l) (t `TT'T'I` tt) =>
 Covariant Yoneda Functor source target t =>
 (forall i . Wrapper target (t `T'TT'I` tt `L` tt `T` ll `L` t `T` l `T'I_` i)) =>
 (forall i . Wrapper target ((t `TT'T'I` tt) i)) =>
 (forall e ee . Wrapper target (T'I'II source e ee)) =>
 t a -> target (source a (tt `L` tt `T` ll `L` t `T` l `T` o)) (tt (t o))
yokl x = unwrap @target @(TT'T'I t tt _)
 `compose` component @target @(t `T'TT'I` tt `L` tt `T` ll `L` t `T` l) @(t `TT'T'I` tt)
 `compose` wrap @target @((t `T'TT'I` tt `L` tt `T` ll `L` t `T` l) _)
 `compose` yo x

yokl_ = yokl
yokl__ = yokl
yokl___ = yokl
yokl____ = yokl
yokl_____ = yokl

li'yokl = yokl

yukl, yukl_, yukl__, yukl___, yukl____, yukl_____
 :: forall target t tt l ll a o .
 Category target =>
 Covariant Endo Transformation Functor target (t `T'TT'I` tt `L` tt `T` ll `L` t `T` l) (t `TT'T'I` tt) =>
 Component target I (T'I'II target a) =>
 Covariant Yoneda Functor target target t =>
 (forall i . Wrapper target ((t `T'TT'I` tt `L` tt `T` ll `L` t `T` l) i)) =>
 (forall i . Wrapper target ((t `TT'T'I` tt) i)) =>
 (forall i ii . Wrapper target (T'I'II target i (tt `L` tt `T` ll `L` t `T` l `T` ii))) =>
 (forall i ii . Wrapper target (T'I'II target ((tt `L` tt `T` ll) i) ii)) =>
 (forall i ii . Wrapper target (T'II'I target (tt `L` tt `T` ll `L` t `T` l `T` i) ii)) =>
 (forall e . Wrapper target (I (tt `L` tt `T` ll `L` t `T` l `T` e))) =>
 (forall e ee . Wrapper target (T'I'II target e ee)) =>
 t a -> target (tt `L` tt `T` ll `L` t `T` l `T` o) (tt (t o))
yukl x = yokl @target @target x `compose` constant

yukl_ = yukl
yukl__ = yukl
yukl___ = yukl
yukl____ = yukl
yukl_____ = yukl

yiokl :: forall source target t tt l ll a o i .
 Category target =>
 Covariant Endo Transformation Functor target (T'I'II t i `T'TT'I` tt `L` tt `T` ll `L` t `T` l) (T'I'II t i `TT'T'I` tt) =>
 Covariant Yoneda Functor source target (T'I'II t i) =>
 Covariant Functor source target tt =>
 (forall e . Wrapper target (T'I'II t i `T'TT'I` tt `L` tt `T` ll `L` t `T` l `T'I_` e)) =>
 (forall e . Wrapper target (T'I'II t i `TT'T'I` tt `T'I_` e)) =>
 (forall e . Wrapper source (T'I'II t i e)) =>
 (forall e ee . Wrapper target (T'I'II source e ee)) =>
 t i a -> target (source a (tt `L` tt `T` ll `L` t `T` l `T'I` o)) (tt (t i o))
yiokl x = fo @source unwrap
 `compose` unwrap @target @(TT'T'I (T'I'II t i) tt _)
 `compose` component @target @(T'I'II t i `T'TT'I` tt `L` tt `T` ll `L` t `T` l) @(T'I'II t i `TT'T'I` tt)
 `compose` wrap @target @((T'I'II t i `T'TT'I` tt `L` tt `T` ll `L` t `T` l) _)
 `compose` yo (wrap x)

yiokl'yokl :: forall source target t tt ttt l ll lll a o i .
 Covariant Yoneda Functor source target (T'I'II t i) =>
 Covariant Endo Semi Functor source tt =>
 Covariant Functor source target ttt =>
 Covariant Endo Transformation Functor target (T'I'II t i `T'TT'I` ttt `L` ttt `T` lll `L` t `T` l) (T'I'II t i `TT'T'I` ttt) =>
 Covariant Endo Transformation Functor source (tt `T'TT'I` ttt `L` ttt `T` lll `L` tt `T` ll) (tt `TT'T'I` ttt) =>
 Contravariant Endo Semi Functor (AR) (T'II'I target (ttt (t i (tt o)))) =>
 (forall e . Wrapper source (ttt `L` ttt `T` lll `L` t `T` l `T` e)) =>
 (forall e . Wrapper source (ttt `L` ttt `T` lll `L` tt `T` ll `L` t `T` l `T` e)) =>
 (forall e . Wrapper source (TT'T'I tt (ttt `L` ttt `T` lll) e)) =>
 (forall e . Wrapper source (T'I'II t i e)) =>
 (forall e . Wrapper source (ttt `L` ttt `T` lll `T` e)) =>
 (forall e . Wrapper source (ttt `L` ttt `T` lll `L` tt `T` ll `T` e)) =>
 (forall e . Wrapper source (T'TT'I tt (ttt `L` ttt `T` lll `L` tt `T` ll) e)) =>
 (forall e . Wrapper target (ttt `L` ttt `T` lll `T` e)) =>
 (forall e . Wrapper target (ttt `L` ttt `T` lll `L` t `T` l `T` e)) =>
 (forall e . Wrapper target (ttt `L` ttt `T` lll `L` t `T` l `T` e)) =>
 (forall e . Wrapper target (T'I'II t i `T'TT'I` ttt `L` ttt `T` lll `L` t `T` l `T'I_` e)) =>
 (forall e . Wrapper target (T'I'II t i `TT'T'I` ttt `L` ttt `T` lll `L` t `T` l `T'I_` e)) =>
 (forall e . Wrapper target (T'TT'I (T'I'II t i) ttt e)) =>
 (forall e . Wrapper target (TT'T'I (T'I'II t i) ttt e)) =>
 (forall e . Wrapper source (TT'T'I tt ttt e)) =>
 (forall e ee . Wrapper target (T'I'II source e ee)) =>
 t i (tt a) -> target (source a (ttt `L` ttt `T` lll `L` tt `T` ll `L` t `T` l `T` o)) (ttt (t i (tt o)))
yiokl'yokl x = fai
 (fio @source (wrap `compose` wrap)
  `compose` fokl @source @source @tt @ttt @ll @lll
  `compose` fio @source unwrap
 )
 (yiokl @source @target @t @ttt @l @lll @(tt a) @(tt o) x)

yoikl :: forall source target t tt l ll a o i .
 Category target =>
 Covariant Endo Transformation Functor target (T'II'I t i `T'TT'I` tt `L` tt `T` ll `L` t `T` l) (T'II'I t i `TT'T'I` tt) =>
 Covariant Yoneda Functor source target (T'II'I t i) =>
 Covariant Functor source target tt =>
 (forall e . Wrapper target (T'II'I t i `T'TT'I` tt `L` tt `T` ll `L` t `T` l `T'I_` e)) =>
 (forall e . Wrapper target (T'II'I t i `TT'T'I` tt `T'I_` e)) =>
 (forall e . Wrapper source (T'II'I t i e)) =>
 (forall e ee . Wrapper target (T'I'II source e ee)) =>
 t a i -> target (source a (tt `L` tt `T` ll `L` t `T` l `T'I` o)) (tt (t o i))
yoikl x = fo @source unwrap
 `compose` unwrap @target @(TT'T'I (T'II'I t i) tt _)
 `compose` component @target @(T'II'I t i `T'TT'I` tt `L` tt `T` ll `L` t `T` l) @(T'II'I t i `TT'T'I` tt)
 `compose` wrap @target @((T'II'I t i `T'TT'I` tt `L` tt `T` ll `L` t `T` l) _)
 `compose` yo (wrap x)

yoikl'yokl :: forall source target t tt ttt l ll lll a o i .
 Covariant Yoneda Functor source target (T'II'I t i) =>
 Covariant Endo Semi Functor source tt =>
 Covariant Functor source target ttt =>
 Covariant Endo Transformation Functor target (T'II'I t i `T'TT'I` ttt `L` ttt `T` lll `L` t `T` l) (T'II'I t i `TT'T'I` ttt) =>
 Covariant Endo Transformation Functor source (tt `T'TT'I` ttt `L` ttt `T` lll `L` tt `T` ll) (tt `TT'T'I` ttt) =>
 Contravariant Endo Semi Functor (AR) (T'II'I target (ttt (t (tt o) i))) =>
 (forall e . Wrapper source (ttt `L` ttt `T` lll `L` t `T` l `T` e)) =>
 (forall e . Wrapper source (ttt `L` ttt `T` lll `L` tt `T` ll `L` t `T` l `T` e)) =>
 (forall e . Wrapper source (TT'T'I tt (ttt `L` ttt `T` lll) e)) =>
 (forall e . Wrapper source (T'II'I t i e)) =>
 (forall e . Wrapper source (ttt `L` ttt `T` lll `T` e)) =>
 (forall e . Wrapper source (ttt `L` ttt `T` lll `L` tt `T` ll `T` e)) =>
 (forall e . Wrapper source (T'TT'I tt (ttt `L` ttt `T` lll `L` tt `T` ll) e)) =>
 (forall e . Wrapper target (ttt `L` ttt `T` lll `T` e)) =>
 (forall e . Wrapper target (ttt `L` ttt `T` lll `L` t `T` l `T` e)) =>
 (forall e . Wrapper target (ttt `L` ttt `T` lll `L` t `T` l `T` e)) =>
 (forall e . Wrapper target (T'II'I t i `T'TT'I` ttt `L` ttt `T` lll `L` t `T` l `T'I_` e)) =>
 (forall e . Wrapper target (T'II'I t i `TT'T'I` ttt `L` ttt `T` lll `L` t `T` l `T'I_` e)) =>
 (forall e . Wrapper target (T'TT'I (T'II'I t i) ttt e)) =>
 (forall e . Wrapper target (TT'T'I (T'II'I t i) ttt e)) =>
 (forall e . Wrapper source (TT'T'I tt ttt e)) =>
 (forall e ee . Wrapper target (T'I'II source e ee)) =>
 t (tt a) i -> target (source a (ttt `L` ttt `T` lll `L` tt `T` ll `L` t `T` l `T` o)) (ttt (t (tt o) i))
yoikl'yokl x = fai
 (fio @source (wrap `compose` wrap)
  `compose` fokl @source @source @tt @ttt @ll @lll
  `compose` fio @source unwrap
 )
 (yoikl @source @target @t @ttt @l @lll @(tt a) @(tt o) x)

-- TODO: labeling
yiok :: forall source target tt t i a o .
 Category target =>
 Component target (T'I'II t i `T'TT'I` tt) (T'I'II t i) =>
 Covariant Yoneda Functor source target (T'I'II t i) =>
 (forall e ee . Wrapper target (T'I'II source e ee)) =>
 Elicitable T'I'II target (T'I'II t i o) =>
 Elicitable T'II'I target (T'TT'I (T'I'II t i) tt o) =>
 t i a -> target (source a (tt o)) (t i o)
yiok x = unwrap @target @(T'I'II t i o)
 `compose` component @target @(T'TT'I (T'I'II t i) tt)
 `compose` wrap @target @(T'TT'I (T'I'II t i) tt _)
 `compose` yo (T'I'II x)

-- TODO: yok'yo
-- TODO: yok'he'yo

-- yok'yokl--, yok_'yokl, yok__'yokl, yok___'yokl, yok____'yokl, yok_____'yokl, yok______'yokl
--  :: forall source target t tt ttt l ll lll a o .
--  Covariant Yoneda Functor source target t =>
--  Covariant Endo Semi Functor target t =>
--  Covariant Endo Semi Functor source tt =>
--  Covariant Endo Semi Functor source ttt =>
--  Covariant Semi Functor source target (T'I'II source a) =>
--  Contravariant Endo Semi Functor (AR) (T'II'I target (t (ttt o))) =>

--  Covariant Transformation Functor source target (t `T'TT'I` tt `L` tt `T` lll) t =>
--  Covariant Endo Transformation Functor source (ttt `T'TT'I` tt `L` tt `T` lll `L` ttt `T` ll) (ttt `TT'T'I` tt) =>

--  -- (forall e ee . Wrapper target (T'I'II source e ee)) =>
--  -- (forall e . Wrapper source (ttt `T'TT'I` t `L` ll `L` lll `T'I_` e)) =>
--  -- (forall e . Wrapper source (tt `L` tt `T` ll `T` e)) =>
--  -- (forall e . Wrapper source (tt `L` lll `T` e)) =>
--  -- (forall e . Wrapper target (t `T'TT'I` tt `L` tt `T` ll `T` e)) =>
--  -- (forall e . Wrapper target (t `T'TT'I` tt `L` lll `L` ll `T'I_` e)) =>
--  -- (forall e . Wrapper source (ttt `T'TT'I` tt `L` lll `L` ll `T'I_` e)) =>
--  -- (forall e . Wrapper target (ttt `TT'T'I` tt `L` lll `L` ll `T'I_` e)) =>
--  -- (forall e . Wrapper source (ttt `T'TT'I` tt `L` lll `T'I_` e)) =>
--  -- (forall e . Wrapper source (ttt `TT'T'I` tt `T'I_` e)) =>
--  t (ttt a) -> target (source a (tt `L` tt `T` ll `L` _ `T` lll `T'I` o)) (t (ttt o))
-- yok'yokl x = fai (fio (wrap @source @(tt `L` _ `T` _ `T` _)) `compose` fokl @source @source @ttt @tt @l @ll)
--  (yok @source @target @t @tt @ll x `compose` fio (unwrap @target @()))

-- (tt `L` tt `T` ll `L` t `T` lll `T` _)

-- yok_'yokl = yok'yokl
-- yok__'yokl = yok'yokl
-- yok___'yokl = yok'yokl
-- yok____'yokl = yok'yokl
-- yok_____'yokl = yok'yokl
-- yok______'yokl = yok'yokl

-- li'yok'yokl = yok'yokl

-- yok'yukl, yok_'yukl, yok__'yukl, yok___'yukl, yok____'yukl, yok_____'yukl, yok______'yukl
 -- :: forall target t tt ttt l ll lll a o .
 -- Covariant Yoneda Functor (AR) target t =>
 -- Covariant Endo Semi Functor target tt =>
 -- Covariant Endo Semi Functor (AR) tt =>
 -- Covariant Endo Semi Functor (AR) ttt =>
 -- Covariant Semi Functor (AR) target (T'I'II (AR) a) =>
 -- Contravariant Endo Semi Functor (AR) (T'II'I target (t (ttt o))) =>
 -- Covariant Endo Transformation Functor target (t `T'TT'I` tt `L` tt `T` ll) t =>
 -- Covariant Endo Transformation Functor (AR) (ttt `T'TT'I` tt `L` tt `T` ll `L` ttt `T` lll) (ttt `TT'T'I` tt) =>
 -- (forall e ee . Wrapper target (T'I'II (AR) e ee)) =>
 -- (forall e . Wrapper (AR) (ttt `T'TT'I` tt `L` tt `T` ll `L` t `T` l `T'I_` e)) =>
 -- (forall e . Wrapper target (tt `L` tt `T` ll `T` e)) =>
 -- (forall e . Wrapper (AR) (tt `L` tt `T` ll `T` e)) =>
 -- (forall e . Wrapper target (tt `L` tt `T` ll `L` t `T` l `T` e)) =>
 -- (forall e . Wrapper target (tt `L` tt `T` ll `T` e)) =>
 -- (forall e . Wrapper (AR) (tt `L` tt `T` ll `L` t `T` l `T` e)) =>
 -- (forall e . Wrapper target (t `T'TT'I` tt `L` tt `T` ll `T'I_` e)) =>
 -- (forall e . Wrapper target (t `T'TT'I` tt `L` tt `T` ll `L` t `T` l `T'I_` e)) =>
 -- (forall e . Wrapper (AR) (ttt `T'TT'I` tt `L` tt `T` ll `T'I_` e)) =>
 -- (forall e . Wrapper (AR) (TT'T'I ttt tt e)) =>
 -- (forall e . Wrapper (AR) (TT'T'I ttt (tt `L` tt `T` ll `L` t `T` l) e)) =>
 -- t (tt a) -> target (ttt `L` ttt `T` ll `L` ttt `T` l `T` o) (t (tt o))
-- yok'yukl x = fai
 -- (fio (wrap @(AR) @(ttt `L` tt `T` ll `T` _)) `compose` fukl @(AR) @tt @ttt @ll @lll)
 -- (yok @(AR) @target @t @ttt @lll x)

-- (ttt a) `AR` (tt `L` tt `T` w0 `T` o) (t o)

-- T (T (L (T (L tt tt) ll) t) l) o -> ttt a `AR` tt (ttt o)
-- T (T (L (T (L tt tt) ll) ttt) l) o -> ttt a `AR` (tt (ttt o)))

-- yok_'yukl = yok'yukl
-- yok__'yukl = yok'yukl
-- yok___'yukl = yok'yukl
-- yok____'yukl = yok'yukl
-- yok_____'yukl = yok'yukl
-- yok______'yukl = yok'yukl

-- TODO: , yokl_'yokl, yokl__'yokl, yokl___'yokl, yokl____'yokl, yokl_____'yokl
yokl'yokl :: forall source target t tt ttt l ll lll a o .
 Covariant Yoneda Functor source target t =>
 Covariant Semi Functor source target t =>
 Covariant Endo Semi Functor source tt =>
 Covariant Endo Semi Functor source ttt =>
 Covariant Semi Functor source target ttt =>
 Covariant Endo Transformation Functor target (t `T'TT'I` ttt `L` ttt `T` lll `L` t `T` l) (t `TT'T'I` ttt) =>
 Covariant Endo Transformation Functor source (tt `T'TT'I` ttt `L` ttt `T` lll `L` tt `T` ll) (tt `TT'T'I` ttt) =>
 Contravariant Endo Semi Functor (AR) (T'II'I target (ttt (t (tt o)))) =>
 (forall e . Wrapper source (ttt `L` ttt `T` lll `L` t `T` l `T` e)) =>
 (forall e . Wrapper source (ttt `L` ttt `T` lll `L` tt `T` ll `L` t `T` l `T` e)) =>
 (forall e . Wrapper source (tt `TT'T'I` ttt `L` ttt `T` lll `T'I_` e)) =>
 (forall e . Wrapper source (ttt `L` ttt `T` lll `T` e)) =>
 (forall e . Wrapper source (ttt `L` ttt `T` lll `L` tt `T` ll `T` e)) =>
 (forall e . Wrapper source (tt `T'TT'I` ttt `L` ttt `T` lll `L` tt `T` ll `T'I_` e)) =>
 (forall e . Wrapper target (ttt `L` ttt `T` lll `T` e)) =>
 (forall e . Wrapper target (ttt `L` ttt `T` lll `L` t `T` l `T` e)) =>
 (forall e . Wrapper target (ttt `L` ttt `T` lll `L` t `T` l `T` e)) =>
 (forall e . Wrapper target (t `T'TT'I` ttt `L` ttt `T` lll `L` t `T` l `T'I_` e)) =>
 (forall e . Wrapper target (t `TT'T'I` ttt `L` ttt `T` lll `L` t `T` l `T'I_` e)) =>
 (forall e . Wrapper target (t `T'TT'I` ttt `T'I_` e)) =>
 (forall e . Wrapper target (t `TT'T'I` ttt `T'I_` e)) =>
 (forall e . Wrapper source (tt `TT'T'I` ttt `T'I_` e)) =>
 (forall e ee . Wrapper target (T'I'II source e ee)) =>
 t (tt a) -> target (source a (ttt `L` ttt `T` lll `L` tt `T` ll `L` t `T` l `T` o)) (ttt (t (tt o)))
yokl'yokl x = fai
 (fio @source (wrap `compose` wrap)
  `compose` fokl @source @source @tt @ttt @ll @lll
  `compose` fio @source unwrap
 )
 (yokl @source @target @t @ttt @l @lll @(tt a) @(tt o) x)



-- yokl x: target (source (tt a) (L l (ttt `L` ttt `T` lll) o)) (ttt (t (tt o)))

-- fokl: source a (L ll (ttt `L` ttt `T` lll) o) -> target (tt a) (ttt (tt o))

-- yokl'yok :: forall source target t tt ttt l a o .
 -- Covariant Yoneda Functor source target t =>
 -- Covariant Endo Semi Functor source tt =>
 -- Covariant Endo Semi Functor source ttt =>
 -- Contravariant Endo Semi Functor (AR) (T'II'I target (ttt (t o))) =>
 -- Covariant Transformation Functor source source (T'TT'I ttt tt) ttt =>
 -- Covariant Transformation Functor source target (T'TT'I t ttt) (TT'T'I t ttt) =>
 -- Elicitable T'II'I target (T'I'II source (ttt a) (ttt o)) =>
 -- Elicitable T'I'II target (TT'T'I t ttt o) =>
 -- Elicitable T'II'I target (T'TT'I t ttt o) =>
 -- Elicitable T'II'I source (T'TT'I ttt tt o) =>
 -- t (ttt a) -> target (source a (tt `L` tt `T` l `T` o)) (ttt (t o))
-- yokl'yok x = fai fok (yokl @source @target x)

ho, ho_, ho__, ho___, ho____, ho_____, ho______, ho_______, ho________, yi'ho :: forall source target u i a o .
 Precategory target =>
 Covariant Yoneda Functor source target (T'I'II u i) =>
 (forall e . Wrapper target (T'I'II u i e)) =>
 (forall e ee . Wrapper target (T'I'II source e ee)) =>
 u i a -> target (source a o) (u i o)
ho = yio @source @target @u

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
 :: forall source target u i a o .
 Covariant Yoneda Functor source target (T'I'II u i) =>
 Contravariant Semi Functor source target (T'II'I source o) =>
 Covariant Semi Functor source target (T'I'II source o) =>
 Wrapper source a =>
 (forall e ee . Wrapper target (T'I'II source e ee)) =>
 (forall e ee . Wrapper target (T'II'I source e ee)) =>
 (forall e ee . Wrapper target (T'I'II u e ee)) =>
 u i a -> target (source (Supertype a) o) (u i o)
ho'he = fai @target (fai @source he) `compose` yio @source @target @u

ho_'he = ho'he
ho__'he = ho'he
ho___'he = ho'he
ho____'he = ho'he
ho_____'he = ho'he
ho______'he = ho'he
ho_______'he = ho'he
ho________'he = ho'he

ho'he'he, ho_'he'he, ho__'he'he, ho___'he'he, ho____'he'he, ho_____'he'he, ho______'he'he, ho_______'he'he, ho________'he'he
 :: forall source target u i a o .
 Covariant Yoneda Functor source target (T'I'II u i) =>
 Contravariant Semi Functor source target (T'II'I source o) =>
 Covariant Semi Functor source target (T'I'II source o) =>
 Wrapper source a =>
 Wrapper source (Supertype a) =>
 (forall e . Wrapper target (T'I'II u i e)) =>
 (forall e ee . Wrapper target (T'I'II source e ee)) =>
 (forall e ee . Wrapper target (T'II'I source e ee)) =>
 Wrapper target (T'II'I source o (Supertype a)) =>
 Wrapper target (T'II'I source o (Supertype (Supertype a))) =>
 u i a -> target (source (Supertype (Supertype a)) o) (u i o)
ho'he'he = fai @target (fai @source (he `compose` he)) `compose` yio @source @target @u

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
 :: forall source target u i a o .
 Precategory source =>
 Precategory target =>
 Covariant Yoneda Functor source target (T'I'II u i) =>
 Contravariant Semi Functor source target (T'II'I source o) =>
 Covariant Semi Functor source target (T'I'II source o) =>
 Wrapper source a =>
 Wrapper source (Supertype a) =>
 Wrapper source (Supertype (Supertype a)) =>
 (forall e . Wrapper target (T'I'II u i e)) =>
 (forall e ee . Wrapper target (T'I'II source e ee)) =>
 (forall e ee . Wrapper target (T'II'I source e ee)) =>
 Wrapper target (T'II'I source o (Supertype a)) =>
 Wrapper target (T'II'I source o (Supertype (Supertype a))) =>
 Wrapper target (T'II'I source o (Supertype (Supertype (Supertype a)))) =>
 u i a -> target (source (Supertype (Supertype (Supertype a))) o) (u i o)
ho'he'he'he x = yio @source @target @u x `compose` fai @source he `compose` fai @source he `compose` fai @source he

ho_'he'he'he = ho'he'he'he
ho__'he'he'he = ho'he'he'he
ho___'he'he'he = ho'he'he'he
ho____'he'he'he = ho'he'he'he
ho_____'he'he'he = ho'he'he'he
ho______'he'he'he = ho'he'he'he
ho_______'he'he'he = ho'he'he'he
ho________'he'he'he = ho'he'he'he

ho'he'he'he'he, ho_'he'he'he'he, ho__'he'he'he'he, ho___'he'he'he'he, ho____'he'he'he'he, ho_____'he'he'he'he, ho______'he'he'he'he, ho_______'he'he'he'he, ho________'he'he'he'he
 :: forall source target u i a o .
 Precategory source =>
 Precategory target =>
 Covariant Yoneda Functor source target (T'I'II u i) =>
 Contravariant Semi Functor source target (T'II'I source o) =>
 Covariant Semi Functor source target (T'I'II source o) =>
 Wrapper source a =>
 Wrapper source (Supertype a) =>
 Wrapper source (Supertype (Supertype a)) =>
 Wrapper source (Supertype (Supertype (Supertype a))) =>
 (forall e . Wrapper target (T'I'II u i e)) =>
 (forall e ee . Wrapper target (T'I'II source e ee)) =>
 (forall e ee . Wrapper target (T'II'I source e ee)) =>
 Wrapper target (T'II'I source o (Supertype a)) =>
 Wrapper target (T'II'I source o (Supertype (Supertype a))) =>
 Wrapper target (T'II'I source o (Supertype (Supertype (Supertype a)))) =>
 Wrapper target (T'II'I source o (Supertype (Supertype (Supertype (Supertype a))))) =>
 u i a -> target (source (Supertype (Supertype (Supertype (Supertype a)))) o) (u i o)
ho'he'he'he'he x = yio @source @target @u x `compose` fai @source he `compose` fai @source he `compose` fai @source he `compose` fai @source he

ho_'he'he'he'he = ho'he'he'he'he
ho__'he'he'he'he = ho'he'he'he'he
ho___'he'he'he'he = ho'he'he'he'he
ho____'he'he'he'he = ho'he'he'he'he
ho_____'he'he'he'he = ho'he'he'he'he
ho______'he'he'he'he = ho'he'he'he'he
ho_______'he'he'he'he = ho'he'he'he'he
ho________'he'he'he'he = ho'he'he'he'he

-- ho'ho, ho_'ho :: forall source u uu i ii a o .
--  Covariant Yoneda Functor u source (T'I'II u i) =>
--  Covariant Semi Functor source u (T'I'II uu ii) =>
--  Contravariant Yoneda Functor (AR) (AR) (T'II'I u i) =>
--  Covariant Endo Semi Functor (AR) (T'I'II (AR) (u i (uu a ii))) =>
--  Contravariant Semi Functor (AR) (AR) (T'II'I source (u i (uu ii o))) =>
--  (forall e ee . Wrapper source (T'I'II u e ee)) =>
--  (forall e ee . Wrapper source (T'I'II uu e ee)) =>
--  (forall e ee . Wrapper u (T'I'II uu e ee)) =>
--  u i (uu ii a) -> source (source a o) (u i (uu ii o))
-- ho'ho x = fai @(AR) @(AR) (fio @source @u) (ho @u @source x)

-- ho_'ho = ho'ho

-- ho'ho'ho :: forall source u uu uuu o i ii iii a .
--  Covariant Yoneda Functor u source (T'I'II u i) =>
--  Contravariant Yoneda Functor (AR) (AR) (T'II'I u i) =>
--  Covariant Semi Functor source u (T'I'II uu ii) =>
--  Covariant Endo Semi Functor source (T'I'II uuu iii) =>
--  Covariant Endo Semi Functor (AR) (T'I'II (AR) (u i (uu a ii))) =>
--  Contravariant Semi Functor (AR) (AR) (T'II'I source (u i (uu ii (uuu iii o)))) =>
--  (forall e ee . Wrapper source (T'I'II uuu e ee)) =>
--  (forall e ee . Wrapper u (T'I'II uu e ee)) =>
--  (forall e ee . Wrapper source (T'I'II u e ee)) =>
--  -- Wrapper source (T'I'II uu ii (uuu iii o)) =>
--  -- Wrapper source (T'I'II u e (uu ii (uuu iii o))) =>
--  -- Wrapper source (T'I'II u (uu ii a) (uu ii o)) =>
--  -- Wrapper source (T'I'II u (uu ii (uuu iii a)) (uu ii (uuu iii o))) =>
--  u i (uu ii (uuu iii a)) -> source (source a o) (u i (uu ii (uuu iii o)))
-- ho'ho'ho x = fai @(AR) @(AR) (fio @source `compose` fio @source) (ho @u @source x)

yio'yio'yui, yio'ho'yui, ho'yio'yui, ho'ho'yui
 :: forall source u uu uuu o i ii iii a .
 Terminal source =>
 Category source =>
 Covariant Yoneda Functor u source (T'I'II u i) =>
 Contravariant Yoneda Functor (AR) (AR) (T'II'I u i) =>
 Covariant Semi Functor source u (T'I'II uu ii) =>
 Covariant Endo Semi Functor source (T'II'I uuu iii) =>
 Covariant Endo Semi Functor (AR) (T'I'II (AR) (u i (uu a ii))) =>
 Contravariant Semi Functor (AR) (AR) (T'II'I source (u i (uu ii (uuu o iii)))) =>
 (forall e ee . Wrapper source (T'II'I uuu e ee)) =>
 (forall e ee . Wrapper source (T'I'II uu e ee)) =>
 (forall e ee . Wrapper source (T'I'II u e ee)) =>
 (forall e ee . Wrapper u (T'I'II uu e ee)) =>
 (forall e . Wrapper (AR) (source Unit e)) =>
 u i (uu ii (uuu a iii)) -> source (Supertype (source Unit o)) (u i (uu ii (uuu o iii)))
yio'yio'yui x = fai @(AR) @(AR) (fio @source `compose` fui @source) (ho @u @source x)

ho'yio'yui = yio'yio'yui
yio'ho'yui = yio'yio'yui
ho'ho'yui = yio'yio'yui

-- ho'ho'hu :: forall source u uu uuu o i ee eee a .
 -- Category source =>
 -- Terminal source =>
 -- Covariant Yoneda Functor uuu (AR) (T'I'II u i) =>
 -- Covariant Semi Functor source uuu (T'I'II uu ee) =>
 -- Covariant Endo Semi Functor source (T'I'II uuu eee) =>
 -- Constant Endo Semi Functor source (T'I'II uuu eee) =>
 -- (forall i . Wrapper uuu (T'I'II uu ee i)) =>
 -- (forall i . Wrapper source (T'I'II uuu eee i)) =>
 -- Wrapper (AR) (source Unit o) =>
 -- u i (uu ee (uuu eee a)) -> Supertype (source Unit o) -> u i (uu ee (uuu eee o))
-- ho'ho'hu = fai (fio @source `compose` fiu @source) `compose` ho @uuu

ho'hu :: forall source t tt o i ii a .
 Category source =>
 Terminal source =>
 Covariant Yoneda Functor t source (T'I'II t i) =>
 Contravariant Yoneda Functor (AR) (AR) (T'II'I t i) =>
 Covariant Semi Functor source t (T'I'II tt ii) =>
 Covariant Endo Semi Functor (AR) (T'I'II (AR) (t i (tt a ii))) =>
 Contravariant Semi Functor (AR) (AR) (T'II'I source (t i (tt ii o))) =>
 (forall e . Wrapper t (T'I'II tt ii e)) =>
 (forall e . Wrapper (AR) (source Unit e)) =>
 Wrapper source (T'I'II tt ii o) =>
 (forall e ee . Wrapper source (T'I'II t e ee)) =>
 t i (tt ii a) -> source (Supertype (source Unit o)) (t i (tt ii o))
ho'hu = fai (fiu @source) `compose` ho @t

-- ho'ha, ho_'ha, ho__'ha, ho___'ha, ho____'ha, ho_____'ha, ho______'ha, ho_______'ha, ho________'ha
--  :: forall source u uu o i ii a .
--  Covariant Yoneda Functor u (AR) (T'I'II u i) =>
--  Contravariant Yoneda Functor u (AR) (T'II'I u i) =>
--  Contravariant Semi Functor source u (T'II'I uu ii) =>
--  Contravariant Endo Semi Functor (AR) (T'II'I (AR) (u i (uu a ii))) =>
--  (forall e ee . Wrapper u (T'II'I uu e ee)) =>
--  (forall e ee . Wrapper source (T'I'II u e ee)) =>
--  u i (uu o ii) -> source a o -> u i (uu a ii)
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
--  :: forall source u uu o i ii a .
--  Covariant Yoneda Functor u (AR) (T'I'II u i) =>
--  Contravariant Semi Functor source u (T'II'I uu ii) =>
--  (forall e ee . Wrapper u (T'II'I uu e ee)) =>
--  Wrapper source a =>
--  u i (uu o ii) -> source (Supertype a) o -> u i (uu a ii)
-- ho'ha'he x = fai (fai `compose` fai @source unwrap) (ho @u x)

-- ho_'ha'he = ho'ha'he
-- ho__'ha'he = ho'ha'he
-- ho___'ha'he = ho'ha'he
-- ho____'ha'he = ho'ha'he
-- ho_____'ha'he = ho'ha'he
-- ho______'ha'he = ho'ha'he
-- ho_______'ha'he = ho'ha'he
-- ho________'ha'he = ho'ha'he

-- ho'ha'he'he, ho_'ha'he'he, ho__'ha'he'he, ho___'ha'he'he, ho____'ha'he'he, ho_____'ha'he'he, ho______'ha'he'he, ho_______'ha'he'he, ho________'ha'he'he
--  :: forall source u uu o i ii a .
--  Covariant Yoneda Functor u (AR) (T'I'II u i) =>
--  Contravariant Semi Functor source u (T'II'I uu ii) =>
--  (forall e ee . Wrapper u (T'II'I uu e ee)) =>
--  Wrapper source a =>
--  Wrapper source (Supertype a) =>
--  u i (uu o ii) -> source (Supertype (Supertype a)) o -> u i (uu a ii)
-- ho'ha'he'he x = fai (fai `compose` fai @source he'he) (ho @u x)

-- ho_'ha'he'he = ho'ha'he'he
-- ho__'ha'he'he = ho'ha'he'he
-- ho___'ha'he'he = ho'ha'he'he
-- ho____'ha'he'he = ho'ha'he'he
-- ho_____'ha'he'he = ho'ha'he'he
-- ho______'ha'he'he = ho'ha'he'he
-- ho_______'ha'he'he = ho'ha'he'he
-- ho________'ha'he'he = ho'ha'he'he

-- ho'yo, ho_'yo, ho__'yo, ho___'yo, ho____'yo, ho_____'yo, ho______'yo, ho_______'yo, ho________'yo
--  :: forall source u t o e a .
--  Covariant Yoneda Functor source (AR) (T'I'II u e) =>
--  Contravariant Yoneda Functor source (AR) (T'II'I u e) =>
--  Covariant Endo Semi Functor source t =>
--  Constant Semi Functor source (AR) t =>
--  u e (t a) -> source a o -> u e (t o)
-- ho'yo x = fai (fo @source) (ho @source x)

-- ho_'yo = ho'yo
-- ho__'yo = ho'yo
-- ho___'yo = ho'yo
-- ho____'yo = ho'yo
-- ho_____'yo = ho'yo
-- ho______'yo = ho'yo
-- ho_______'yo = ho'yo
-- ho________'yo = ho'yo

ho'yoo, ho_'yoo, ho__'yoo, ho___'yoo, ho____'yoo, ho_____'yoo, ho______'yoo, ho_______'yoo, ho________'yoo
 :: forall source target t i tt a o .
 Covariant Endo Semi Functor source (T'I'I tt) =>
 Covariant Yoneda Functor source target (T'I'II t i) =>
 (forall e ee . Wrapper target (T'I'II t e ee)) =>
 Contravariant Endo Semi Functor (AR) (T'II'I target (t i ((tt o o)))) =>
 (forall e ee . Wrapper target (T'I'II source e ee)) =>
 (forall e . Wrapper source (T'I'I tt e)) =>
 (t i ((tt a a))) -> target (source (a) o) (t i ((tt o o)))
ho'yoo x = fai (foo @source @source @tt) (yio @source @target x)

ho_'yoo = ho'yoo
ho__'yoo = ho'yoo
ho___'yoo = ho'yoo
ho____'yoo = ho'yoo
ho_____'yoo = ho'yoo
ho______'yoo = ho'yoo
ho_______'yoo = ho'yoo
ho________'yoo = ho'yoo

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
--  :: forall source u t o e a .
--  Covariant Yoneda Functor source (AR) (T'I'II u e) =>
--  Contravariant Yoneda Functor source (AR) (T'II'I u e) =>
--  Covariant Endo Semi Functor source (T'II'I t e) =>
--  (forall ee . Wrapper source (T'II'I t e ee)) =>
--  u e (t a e) -> source a o -> u e (t o e)
-- ho'yoi x = fai (foi @source) (ho @source x)

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

ho'yioi :: forall source u t o i ii iii a .
 Covariant Yoneda Functor source (AR) (T'I'II u i) =>
 Contravariant Yoneda Functor source (AR) (T'II'I u i) =>
 Covariant Endo Semi Functor source (W_III_I_II t iii ii) =>
 (forall e . Wrapper source (W_III_I_II t iii ii e)) =>
 u i (t ii a iii) -> source a o -> u i (t ii o iii)
ho'yioi x = fai (fioi @source) (ho @source x)

he'ho, he_'ho, he__'ho, he___'ho, he____'ho, he_____'ho, he______'ho, he_______'ho, he________'ho
 :: forall source target u i a o .
 Covariant Yoneda Functor source target (T'I'II u (Supertype i)) =>
 Contravariant Semi Functor target target (T'II'I u o) =>
 Wrapper target i =>
 (forall e ee . Wrapper target (T'I'II source e ee)) =>
 (forall e ee . Wrapper target (T'I'II u e ee)) =>
 (forall e ee . Wrapper target (T'II'I u e ee)) =>
 u (Supertype i) a -> target (source a o) (u i o)
he'ho x = fai @target he
 `compose` yio @source @target @u x

he_'ho= he'ho
he__'ho= he'ho
he___'ho= he'ho
he____'ho= he'ho
he_____'ho= he'ho
he______'ho= he'ho
he_______'ho= he'ho
he________'ho= he'ho

he'ho'he, he_'ho'he, he__'ho'he, he___'ho'he, he____'ho'he, he_____'ho'he, he______'ho'he, he_______'ho'he, he________'ho'he
 :: forall source target u i a o .
 Covariant Yoneda Functor source target (T'I'II u (Supertype i)) =>
 Contravariant Semi Functor source target (T'II'I u o) =>
 Contravariant Semi Functor source target (T'II'I source o) =>
 Wrapper source a =>
 Wrapper source i =>
 (forall e ee . Wrapper target (T'II'I source e ee)) =>
 (forall e ee . Wrapper target (T'I'II source e ee)) =>
 (forall e ee . Wrapper target (T'II'I u e ee)) =>
 (forall e ee . Wrapper target (T'I'II u e ee)) =>
 Wrapper target (T'II'I u o (Supertype i)) =>
 Wrapper target (T'II'I source o (Supertype a)) =>
 u (Supertype i) a -> target (source (Supertype a) o) (u i o)
he'ho'he x = fai @source @target he
 `compose` yio @source @target @u x
 `compose` fai @source @target he

he_'ho'he = he'ho'he
he__'ho'he = he'ho'he
he___'ho'he = he'ho'he
he____'ho'he = he'ho'he
he_____'ho'he = he'ho'he
he______'ho'he = he'ho'he
he_______'ho'he = he'ho'he
he________'ho'he = he'ho'he

-- he'hu
 -- :: forall source target u i a o .
 -- Precategory source =>
 -- Category target =>
 -- Covariant Yoneda Functor target target (T'I'II u i) =>
 -- Constant Semi Functor (AR) (AR) (T'I'II u i) =>
 -- Mapping T'I'II T'I'II (AR) (AR) (T'I'II u i) (T'I'II u i) =>
 -- Contravariant Semi Functor source (AR) (T'II'I u a) =>
 -- Covariant Semi Functor source target (T'I'II source o) =>
 -- Wrapper source i =>
 -- Wrapper target (target () o) =>
 -- Wrapper target (T'I'II target () o) =>
 -- Wrapper target (T'I'II u i o) =>
 -- Wrapper target (T'I'II source a o) =>
 -- u (Supertype i) a -> target (Supertype (target () o)) (u i o)
-- he'hu = yiu @target @u `compose` he @source

-- he'he'ho
 -- :: forall source target u i a o .
 -- Precategory source =>
 -- Precategory target =>
 -- Covariant Yoneda Functor source target (T'I'II u i) =>
 -- Contravariant Semi Functor source (AR) (T'II'I u a) =>
 -- Covariant Semi Functor source target (T'I'II source o) =>
 -- Elicitable T'I'II source i =>
 -- Elicitable T'I'II source (Supertype i) =>
 -- Elicitable T'I'II target (T'I'II u i o) =>
 -- Elicitable T'II'I target (T'I'II source a o) =>
 -- Wrapper target (T'II'I source o a) =>
 -- Wrapper target (T'II'I source o (Supertype a)) =>
 -- u (Supertype (Supertype i)) a -> target (source a o) (u i o)
-- -- he'he'ho = yio @source @target @u `compose` fai @source he'he

-- he'he'he'ho
 -- :: forall source target u i a o .
 -- Precategory source =>
 -- Precategory target =>
 -- Covariant Yoneda Functor source target (T'I'II u i) =>
 -- Contravariant Semi Functor source (AR) (T'II'I u a) =>
 -- Covariant Semi Functor source target (T'I'II source o) =>
 -- Wrapper source i =>
 -- Wrapper source (Supertype i) =>
 -- Wrapper source (Supertype (Supertype i)) =>
 -- Wrapper target (T'I'II u i o) =>
 -- Wrapper target (T'I'II source a o) =>
 -- Wrapper target (T'II'I source o a) =>
 -- -- Wrapper target (T'II'I source o (Supertype a)) =>
 -- u (Supertype (Supertype (Supertype i))) a -> target (source a o) (u i o)
-- he'he'he'ho = yio @source @target @u `compose` fai @source he'he'he

-- ha, ha_, ha__, ha___, ha____, ha_____, ha______, ha_______, ha________ :: forall source target t i a o .
 -- Contravariant Yoneda Functor source target (T'II'I t i) =>
 -- u a i -> target (source o a) (u o i)
-- ha x = yai @source @(AR) $t x

-- ha_ = ha
-- ha__ = ha
-- ha___ = ha
-- ha____ = ha
-- ha_____ = ha
-- ha______ = ha
-- ha_______ = ha
-- ha________ = ha

ha'he, ha_'he, ha__'he, ha___'he, ha____'he, ha_____'he, ha______'he, ha_______'he, ha________'he :: forall source u e a o .
 Contravariant Yoneda Functor source (AR) (T'II'I u e) =>
 Wrapper source o =>
 u a e -> source (Supertype o) a -> u o e
ha'he x = yai @source @(AR) @u x `compose` fai (he @source)

ha_'he = ha'he
ha__'he = ha'he
ha___'he = ha'he
ha____'he = ha'he
ha_____'he = ha'he
ha______'he = ha'he
ha_______'he = ha'he
ha________'he = ha'he

ha'he'he, ha_'he'he, ha__'he'he, ha___'he'he, ha____'he'he, ha_____'he'he, ha______'he'he, ha_______'he'he, ha________'he'he
 :: forall source target u e a o .
 Contravariant Yoneda Functor source target (T'II'I u e) =>
 Contravariant Semi Functor source target (T'II'I source a) =>
 Wrapper source o =>
 (forall e . Wrapper target (T'II'I source a e)) =>
 -- Wrapper target (T'II'I source a o) =>
 Wrapper target (T'II'I u e o) =>
 -- Wrapper target (T'II'I source a (Supertype (Supertype o))) =>
 Wrapper source (Supertype o) =>
 u a e -> target (source (Supertype (Supertype o)) a) (u o e)
ha'he'he = fai @target (fai @source (he `compose` he)) `compose` yai @source @target @u

ha_'he'he = ha'he'he
ha__'he'he = ha'he'he
ha___'he'he = ha'he'he
ha____'he'he = ha'he'he
ha_____'he'he = ha'he'he
ha______'he'he = ha'he'he
ha_______'he'he = ha'he'he
ha________'he'he = ha'he'he

he'ha :: forall source target (u :: * -> * -> *) i a o .
 Contravariant Yoneda Functor source target (T'II'I u i) =>
 Contravariant Semi Functor target target (T'II'I u i) =>
 Wrapper target o =>
 (forall e ee . Wrapper target (T'II'I source e ee)) =>
 (forall e ee . Wrapper target (T'I'II u e ee)) =>
 (forall e ee . Wrapper target (T'II'I u e ee)) =>
 u a i -> target (source (Supertype o) a) (u o i)
he'ha x = fai @target he `compose` yai @source @target @u x

yvi, hv, hv_, hv__, hv___, hv____, hv_____, hv______, hv_______, hv________
 :: forall target a o .
 Category target =>
 Terminal target =>
 target a o `AR` target a o
yvi = identity

-- hu: t i a -> target (source Unit o) (t i o)
-- hv: t a i -> target (source o Void) (t o i)

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
 :: forall target a o .
 Category target =>
 Terminal target =>
 Wrapper target a =>
 target (Supertype a) o -> target a o
yvi'he = fai @target unwrap

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
 :: forall target a o .
 Category target =>
 Terminal target =>
 Wrapper target a =>
 Wrapper target (Supertype a) =>
 target (Supertype (Supertype a)) o -> target a o
yvi'he'he = fai @target (unwrap `compose` unwrap)

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
 :: forall target a o e .
 Category target =>
 Terminal target =>
 Wrapper (AR) e =>
 (Supertype e ~ target a o) =>
 e -> Supertype e
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
 :: forall target a o e .
 Category target =>
 Terminal target =>
 Wrapper (AR) e =>
 Wrapper (AR) (Supertype e) =>
 (Supertype (Supertype e) ~ target a o) =>
 e -> target a o
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

-- he'ho: u (Supertype i) a -> target (source a o) (u i o)
-- ho'he: u i a -> target (source (Supertype a) o) (u i o)

-- he'ho: u (Supertype i) a -> target (source a o) (u i o)
-- ho'he: u i a -> target (source (Supertype a) o) (u i o)
-- ha'he: u a i -> target (source (Supertype o) a) (u o i)

-- ha_ha :: forall source u uu a o e ee .
--  Contravariant Yoneda Functor u (AR) (T'II'I u e) =>
--  Contravariant Semi Functor source u (T'II'I uu ee) =>
--  Contravariant Semi Functor u u (T'II'I uu ee) =>
--  Wrapper u (T'II'I uu ee (Supertype a)) =>
--  Wrapper u (T'II'I uu ee o) =>
--  Wrapper u (T'II'I uu ee a) =>
--  Wrapper u a =>
--  Wrapper source a =>
--  u (uu a ee) e -> source (Supertype a) o -> u (uu o ee) e
-- ha_ha x = fai @(AR) @(AR) fai_ (ha @u x)

-- ha'ho :: forall source u uu o i ii a .
--  Covariant Yoneda Functor u (AR) (T'I'II u i) =>
--  Contravariant Yoneda Functor u (AR) (T'II'I u i) =>
--  Covariant Semi Functor source u (T'I'II uu ii) =>
--  (forall e ee . Wrapper u (T'I'II uu e ee)) =>
--  u (uu ii o) i -> source a o -> u (uu ii a) i
-- ha'ho x = fai @(AR) @(AR) fio (ha @u x)

-- ha'ho'hu :: forall source target u uu u__ o e ee eee a .
 -- Precategory source =>
 -- Contravariant Yoneda Functor u__ (AR) (T'II'I u e) =>
 -- Covariant Semi Functor source u__ (T'I'II uu ee) =>
 -- Covariant Endo Semi Functor source (T'I'II u__ eee) =>
 -- Mapping T'I'II T'I'II target target I (T'I'II target a) =>
 -- Wrapper u__ (T'I'II uu ee (u__ eee a)) =>
 -- Wrapper u__ (T'I'II uu ee (u__ eee o)) =>
 -- Wrapper source (T'I'II u__ eee o) =>
 -- Wrapper source (T'I'II u__ eee a) =>
 -- Wrapper (AR) (U_1_I source a o) =>
 -- u (uu ee (u__ eee o)) e -> Supertype (U_1_I source a o) -> u (uu ee (u__ eee a)) e
-- ha'ho'hu = fai (fio @source `compose` fiu) `compose` ha @u__

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

-- ha'he'hu :: forall source u uu o e ee a .
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
 (forall e . Wrapper (AR) (u Unit e)) =>
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

-- ha'yo :: forall source u t o e a .
--  Covariant Yoneda Functor source (AR) (T'I'II u e) =>
--  Contravariant Yoneda Functor source (AR) (T'II'I u e) =>
--  Covariant Endo Semi Functor source t =>
--  Constant Semi Functor source (AR) t =>
--  u (t a) e -> source o a -> u (t o) e
-- ha'yo x = fai (fo @source) (ha @source x)

ha'yioi :: forall source u t o i ii iii a .
 Covariant Yoneda Functor source (AR) (T'I'II u i) =>
 Contravariant Yoneda Functor source (AR) (T'II'I u i) =>
 Covariant Endo Semi Functor source (W_III_I_II t iii ii) =>
 (forall e . Wrapper source (W_III_I_II t iii ii e)) =>
 u (t ii a iii) i -> source o a -> u (t ii o iii) i
ha'yioi x = fai (fioi @source) (ha @source x)

-- -- TODO: replace with `ho_`
-- ho_yi :: forall source u e a o .
--  Covariant Endo Semi Functor source (T'I'II source a) =>
--  Covariant Yoneda Functor source (AR) (T'I'II u e) =>
--  Contravariant Semi Functor source (AR) (T'II'I (AR) (u e (Supertype o))) =>
--  Contravariant Yoneda Functor source (AR) (T'II'I (AR) (u e (Supertype o))) =>
--  Elicitable T'I'II (AR) (T'I'II u e o) =>
--  Elicitable T'I'II source o =>
--  Wrapper source (T'I'II source a o) =>
--  Wrapper source (T'I'II source a (Supertype o)) =>
--  u e a -> source a o -> u e (Supertype o)
-- ho_yi x = fai @source (fio @source he) (ho x)

-- -- TODO: replace with `ho_ho`
-- ho_yi'ho :: forall source u e a o .
--  Covariant Yoneda Functor source (AR) (T'I'II u e) =>
--  Elicitable T'I'II source a =>
--  u e a -> source (Supertype a) o -> u e o
-- ho_yi'ho x xx = x `ho` he @source `ho` xx

-- hu, hu_, hu__, hu___, hu____, hu_____, hu______, hu_______, hu________ ::
 -- forall target t i a o .
 -- Covariant Yoneda Functor target target (T'I'II t i) =>
 -- Mapping T'I'II T'I'II target target I (T'I'II target a) =>
 -- Wrapper target (T'I'II target a o) =>
 -- Wrapper target (T'I'II t i o) =>
 -- Wrapper target (I o) =>
 -- t i a -> target o (t i o)
-- hu = yiu

-- hu, hu_, hu__, hu___, hu____, hu_____, hu______, hu_______, hu________ ::
 -- forall source target t i a o .
 -- Terminal source =>
 -- Category source =>
 -- Covariant Yoneda Functor source target (T'I'II t i) =>
 -- Covariant Functor source target (T'I'II source a) =>
 -- Contravariant Functor source target (T'II'I source o) =>
 -- Wrapper target (T'I'II source a o) =>
 -- Wrapper target (T'II'I source o a) =>
 -- Wrapper target (T'II'I source o Unit) =>
 -- Wrapper target (T'I'II t i o) =>
 -- t i a -> target (source Unit o) (t i o)
-- hu x = yio @source x `compose` fai @source terminal

-- hu_ = hu
-- hu__ = hu
-- hu___ = hu
-- hu____ = hu
-- hu_____ = hu
-- hu______ = hu
-- hu_______ = hu
-- hu________ = hu

-- hu'he, hu_'he, hu__'he, hu___'he, hu____'he, hu_____'he, hu______'he, hu_______'he, hu________'he
--  :: forall source target a o .
--  Precategory target =>
--  Precategory source =>
--  Covariant Yoneda Functor source target (U_1_I source ()) =>
--  Contravariant Endo Semi Functor source (T'II'I source o) =>
--  Elicitable T'II'I target (T'I'II source a o) =>
--  Elicitable T'II'I target (U_1_I source a o) =>
--  Elicitable T'I'II target (U_1_I source a o) =>
--  Elicitable T'I'II source a =>
--  Wrapper source (T'II'I source o a) =>
--  Wrapper source (T'II'I source o (Supertype a)) =>
--  Elicitable T'I'II target (T'I'II source a o) =>
--  Elicitable T'I'II target (U_1_I source a o) =>
--  Contravariant Yoneda Functor source (AR) (T'II'I target (Supertype (U_1_I source a o))) =>
--  Supertype (U_1_I source a o) -> target (source (Supertype a) o) (Supertype (U_1_I source a o))
-- hu'he x = hu @source @target @a x `yai'yai` he @source @a
-- hu_'he x = hu @source @target @a x `yai'yai` he @source @a
-- hu__'he x = hu @source @target @a x `yai'yai` he @source @a
-- hu___'he x = hu @source @target @a x `yai'yai` he @source @a
-- hu____'he x = hu @source @target @a x `yai'yai` he @source @a
-- hu_____'he x = hu @source @target @a x `yai'yai` he @source @a
-- hu______'he x = hu @source @target @a x `yai'yai` he @source @a
-- hu_______'he x = hu @source @target @a x `yai'yai` he @source @a
-- hu________'he x = hu @source @target @a x `yai'yai` he @source @a

-- hu_'he = hu'he
-- hu__'he = hu'he
-- hu___'he = hu'he
-- hu____'he = hu'he
-- hu_____'he = hu'he
-- hu______'he = hu'he
-- hu_______'he = hu'he
-- hu________'he = hu'he

-- hu'he'he, hu_'he'he, hu__'he'he, hu___'he'he, hu____'he'he, hu_____'he'he, hu______'he'he, hu_______'he'he, hu________'he'he
 -- :: forall source target a o .
 -- Precategory target =>
 -- Precategory source =>
 -- Covariant Yoneda Functor source target (U_1_I source a) =>
 -- Constant Yoneda Functor source target (U_1_I source a) =>
 -- Contravariant Endo Semi Functor source (T'II'I source o) =>
 -- Elicitable T'II'I target (T'I'II source a o) =>
 -- Elicitable T'II'I target (U_1_I source a a) =>
 -- Elicitable T'I'II target (U_1_I source a o) =>
 -- Elicitable T'I'II source a =>
 -- Elicitable T'I'II source (Supertype a) =>
 -- Wrapper source (T'II'I source o a) =>
 -- Wrapper source (T'II'I source o (Supertype (Supertype a))) =>
 -- Elicitable T'I'II target (T'I'II source a o) =>
 -- Wrapper target (U_1_I source a o) =>
 -- Contravariant Yoneda Functor source (AR) (T'II'I target (Supertype (U_1_I source a o))) =>
 -- a -> target (source (Supertype (Supertype a)) o) o
-- hu'he'he x = hu @source @target @a x `yai'yai` he'he @source @a
-- hu_'he'he x = hu @source @target @a x `yai'yai` he'he @source @a
-- hu__'he'he x = hu @source @target @a x `yai'yai` he'he @source @a
-- hu___'he'he x = hu @source @target @a x `yai'yai` he'he @source @a
-- hu____'he'he x = hu @source @target @a x `yai'yai` he'he @source @a
-- hu_____'he'he x = hu @source @target @a x `yai'yai` he'he @source @a
-- hu______'he'he x = hu @source @target @a x `yai'yai` he'he @source @a
-- hu_______'he'he x = hu @source @target @a x `yai'yai` he'he @source @a
-- hu________'he'he x = hu @source @target @a x `yai'yai` he'he @source @a

-- v :: (a -> o) -> a -> e -> o
-- v source x y = source (constant x y)

-- vv = v
-- vvv = v
-- vvvv = v
-- vvvvv = v
-- vvvvvv = v
-- vvvvvvv = v
-- vvvvvvvv = v
-- vvvvvvvvv = v

ro :: forall target hom t i .
 Category target =>
 Covariant (Representable hom) target target t =>
 Elicitable T'I'II target (T'I'II hom (Representation t) i) =>
 target (t i) (hom (Representation t) i)
ro = he `compose` map @T'I'II @T'I'II @target @target @t @(T'I'II hom (Representation t)) identity

ra :: forall target hom t i .
 Category target =>
 Contravariant (Representable hom) target target t =>
 Elicitable T'I'II target (T'II'I hom (Representation t) i) =>
 target (t i) (hom i (Representation t))
ra = he `compose` map @T'II'I @T'I'II @target @target @t @(T'II'I hom (Representation t)) identity

lu'q, lu_'q, lu__'q, lu___'q, lu____'q, lu_____'q, lu______'q, lu_______'q, lu________'q
 :: forall target a .
 Adjoint Functor target target (T'II'I (P) a) (T'I'II target a) =>
 (forall e . Wrapper target ((T'I'II target a `T'TT'I` T'II'I (P) a) e)) =>
 (forall e . Wrapper target (T'II'I (P) a e)) =>
 (forall e . Wrapper target (T'I'II target a e)) =>
 (forall e . Wrapper target (I e)) =>
 Setoid target a =>
 target a (target a (a `P` a `S` a))
lu'q = fij @target @target @(P) @target q

lu_'q = lu'q
lu__'q = lu'q
lu___'q = lu'q
lu____'q = lu'q
lu_____'q = lu'q
lu______'q = lu'q
lu_______'q = lu'q
lu________'q = lu'q

lo'q, lo_'q, lo__'q, lo___'q, lo____'q, lo_____'q, lo______'q, lo_______'q, lo________'q
 :: forall target i a .
 Category target =>
 Covariant Limit target target =>
 (forall e . Covariant Endo Semi Functor target (T'I'II Product e)) =>
 (forall e . Covariant Endo Semi Functor target (T'II'I Product e)) =>
 (forall e . Wrapper target (T'I'I P e)) =>
 (forall e ee . Wrapper target (P'II'I e ee)) =>
 (forall e ee . Wrapper target (P'I'II e ee)) =>
 (forall e . Wrapper target (I e)) =>
 Setoid target a =>
 target i a `AR__` target i a `AR_` target i (a `P` a `S` a)
lo'q x y = q `compose` lo x y

lo_'q = lo'q
lo__'q = lo'q
lo___'q = lo'q
lo____'q = lo'q
lo_____'q = lo'q
lo______'q = lo'q
lo_______'q = lo'q
lo________'q = lo'q

lu's, lu_'s, lu__'s, lu___'s, lu____'s, lu_____'s, lu______'s, lu_______'s, lu________'s
 :: forall target a .
 Adjoint Functor target target (T'II'I (P) a) (T'I'II target a) =>
 (forall e . Wrapper target ((T'I'II target a `T'TT'I` T'II'I (P) a) e)) =>
 (forall e . Wrapper target (T'II'I (P) a e)) =>
 (forall e . Wrapper target (T'I'II target a e)) =>
 (forall e . Wrapper target (I e)) =>
 Semigroup target a =>
 target a (target a a)
lu's = fij @target @target @(P) @target s

lu_'s = lu's
lu__'s = lu's
lu___'s = lu's
lu____'s = lu's
lu_____'s = lu's
lu______'s = lu's
lu_______'s = lu's
lu________'s = lu's

-- hj'hj :: forall source target t tt ttt tttt i ii a o .
 -- Category target =>
-- hj'hj :: forall source target t tt ttt tttt i ii a o .
 -- Category target =>
 -- Adjoint Functor source source (T'II'I t ii) (T'I'II tttt ii) =>
 -- Adjoint Functor source source (T'II'I ttt i) (T'I'II tt i) =>
 -- Covariant Functor target source (T'II'I ttt i) =>
 -- Covariant Functor source source (T'I'II tt i) =>
 -- Wrapper source (T'II'I t ii a) =>
 -- Wrapper target (T'I'II tt i o) =>
 -- Wrapper target (T'I'II tt i (tttt ii o)) =>
 -- Wrapper source (I o) =>
 -- Wrapper source (I (tttt ii o)) =>
 -- Wrapper source (I (T'I'II tttt ii o)) =>
 -- Wrapper source (T'II'I ttt i a) =>
 -- Wrapper source (T'I'II tttt ii o) =>
 -- Wrapper source (T'II'I t ii (ttt a i)) =>
 -- Wrapper source ((T'TT'I (T'II'I ttt i) (T'I'II tt i)) (tttt ii o)) =>
 -- Wrapper source ((T'TT'I (T'II'I t ii) (T'I'II tttt ii)) o) =>
 -- (forall e . Wrapper source (T'II'I ttt i `T'TT'I` T'I'II tt i `T'I_` e)) =>
 -- (forall e . Wrapper source (T'I'II tt i `T'TT'I` T'II'I ttt i `T'I_` e)) =>
 -- a -> source (source (target (source _ o) (tt ii (t o i))) _) (tt ii (t o i))
-- hj'hj = hj @source @source `compose` hj @source @target

-- TODO: it shouldn't exist by itself
he, he_, he__, he___, he____, he_____, he______, he_______, he________ :: forall target e .
 Elicitable T'I'II target e =>
 target e (Supertype e)
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
 :: forall target e .
 Precategory target =>
 Elicitable T'I'II target e =>
 Elicitable T'I'II target (Supertype e) =>
 target e (Supertype (Supertype e))
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
he'he'he, he_'he'he, he__'he'he, he___'he'he, he____'he'he, he_____'he'he, he______'he'he, he_______'he'he, he________'he'he :: forall target e .
 Precategory target =>
 Elicitable T'I'II target e =>
 Elicitable T'I'II target (Supertype e) =>
 Elicitable T'I'II target (Supertype (Supertype e)) =>
 target e (Supertype (Supertype (Supertype e)))
he'he'he = unwrap `compose` unwrap `compose` unwrap

he_'he'he = he'he'he
he__'he'he = he'he'he
he___'he'he = he'he'he
he____'he'he = he'he'he
he_____'he'he = he'he'he
he______'he'he = he'he'he
he_______'he'he = he'he'he
he________'he'he = he'he'he

he'he'he'he, he_'he'he'he, he__'he'he'he, he___'he'he'he, he____'he'he'he, he_____'he'he'he, he______'he'he'he, he_______'he'he'he, he________'he'he'he :: forall target e .
 Precategory target =>
 Elicitable T'I'II target e =>
 Elicitable T'I'II target (Supertype e) =>
 Elicitable T'I'II target (Supertype (Supertype e)) =>
 Elicitable T'I'II target (Supertype (Supertype (Supertype e))) =>
 target e (Supertype (Supertype (Supertype (Supertype e))))
he'he'he'he = unwrap `compose` unwrap `compose` unwrap `compose` unwrap

he_'he'he'he = he'he'he'he
he__'he'he'he = he'he'he'he
he___'he'he'he = he'he'he'he
he____'he'he'he = he'he'he'he
he_____'he'he'he = he'he'he'he
he______'he'he'he = he'he'he'he
he_______'he'he'he = he'he'he'he
he________'he'he'he = he'he'he'he

he'ya :: forall source target t a o e .
 Precategory target =>
 (Supertype e ~ t a) =>
 Contravariant Yoneda Functor source target t =>
 Wrapper target (T'II'I source a o) =>
 Wrapper (AR) e =>
 e -> target (source o a) (t o)
he'ya = ya @source @target `compose` unwrap

he'yo :: forall source target t a o e .
 Precategory target =>
 (Supertype e ~ t a) =>
 Covariant Yoneda Functor source target t =>
 (forall e ee . Wrapper target (T'I'II source e ee)) =>
 Wrapper (AR) e =>
 e -> target (source a o) (t o)
he'yo = yo @source @target `compose` unwrap

he'yu :: forall target t a o e .
 Precategory target =>
 Covariant Yoneda Functor target target t =>
 Mapping T'I'II T'I'II (AR) (AR) t t =>
 Mapping T'I'II T'I'II target target I (T'I'II target a) =>
 Wrapper target (T'I'II target a o) =>
 Wrapper (AR) (target () o) =>
 Wrapper target (target () o) =>
 Elicitable T'II'I target (T'I'II target () o) =>
 Wrapper target (I o) =>
 Wrapper (AR) e =>
 t a -> target o (t o)
he'yu = yu @target

lo, lo_, lo__, lo___, lo____, lo_____, lo______, lo_______
 :: forall target r a o oo .
 Category target =>
 Limit T'I'II target target =>
 Contravariant Objective target r (o `P` oo) =>
 Covariant Endo Semi Functor target (T'I'II Product a) =>
 Covariant Endo Semi Functor target (T'II'I Product oo) =>
 (forall e ee . Wrapper target (T'I'II Product e ee)) =>
 (forall e ee . Wrapper target (T'II'I Product e ee)) =>
 (forall e . Wrapper target (Both Product e)) =>
 (forall e . Wrapper target (I e)) =>
 target a o -> target a oo -> target a r
lo l r = objective @T'II'I @target @_ @(o `P` oo)
 `compose` foi @target @target l `compose` fio @target @target r
 `compose` wrapped (map @T'II'I @T'II'I @target @target @(Both Product) @I identity)

lo_ = lo
lo__ = lo
lo___ = lo
lo____ = lo
lo_____ = lo
lo______ = lo
lo_______ = lo

-- TODO: define longer versions of this operator
lo'lu :: forall target a aa o oo .
 Category target =>
 Limit T'I'II target target =>
 Covariant Endo Semi Functor target (P'I'II (a `P` aa)) =>
 Covariant Endo Semi Functor target (T'II'I (P) oo) =>
 (forall e ee . Wrapper target (e `P'I'II` ee)) =>
 (forall e ee . Wrapper target (T'II'I (P) e ee)) =>
 (forall e . Wrapper target (Both (P) e)) =>
 (forall e . Wrapper target (I e)) =>
 target a o -> target aa oo -> target (a `P` aa) (o `P` oo)
lo'lu l r = lo
 (l `compose` (wrapped (left @T'I'II @target identity)))
 (r `compose` (wrapped (right @T'I'II @target identity)))

lo'yp, lo_'yp, lo__'yp, lo___'yp, lo____'yp, lo_____'yp, lo______'yp, lo_______'yp
 :: forall t tt l a o oo .
 Mapping T'I'II T'I'II (AR) (AR) (Covariant Day (AR) (P) P t (tt `L` tt `T` l) o oo) t =>
 Arrow a (t o) -> Arrow a ((tt `L` tt `T` l) oo) -> Arrow a (t (Product o oo))
lo'yp l r = yp `compose` lo @(AR) @(t o `P` (tt `L` tt `T` l) oo) l r

lo_'yp = lo'yp
lo__'yp = lo'yp
lo___'yp = lo'yp
lo____'yp = lo'yp
lo_____'yp = lo'yp
lo______'yp = lo'yp
lo_______'yp = lo'yp

lo'yp'yo'q, lo_'yp'yo'q, lo__'yp'yo'q, lo___'yp'yo'q, lo____'yp'yo'q, lo_____'yp'yo'q, lo______'yp'yo'q, lo_______'yp'yo'q
 :: forall a o t tt ll .
 Mapping T'I'II T'I'II (AR) (AR) (Covariant Day (AR) (P) P t (tt `L` tt `T` ll) o o) t =>
 Covariant Yoneda Functor (AR) (AR) (T'I'II Product (t o)) =>
 Covariant Yoneda Functor (AR) (AR) (T'II'I Product ()) =>
 Setoid (AR) o =>
 Arrow a (t o) -> Arrow a (tt `L` tt `T` ll `T` o) -> Arrow a (t (o `P` o `S` o))
lo'yp'yo'q x xx xxx = yp'yo (lo x xx xxx) q

lo_'yp'yo'q = lo'yp'yo'q
lo__'yp'yo'q = lo'yp'yo'q
lo___'yp'yo'q = lo'yp'yo'q
lo____'yp'yo'q = lo'yp'yo'q
lo_____'yp'yo'q = lo'yp'yo'q
lo______'yp'yo'q = lo'yp'yo'q
lo_______'yp'yo'q = lo'yp'yo'q

lo'ys, lo_'ys, lo__'ys, lo___'ys, lo____'ys, lo_____'ys, lo______'ys, lo_______'ys
 :: forall t tt l a o oo .
 Mapping T'I'II T'I'II (AR) (AR) (Covariant Day (AR) (P) (S) t (tt `L` tt `T` l) o oo) t =>
 Arrow a (t o) -> Arrow a ((tt `L` tt `T` l) oo) -> Arrow a (t (Sum o oo))
lo'ys l r = ys `compose` lo @(AR) @(t o `P` (tt `L` tt `T` l) oo) l r

lo_'ys = lo'ys
lo__'ys = lo'ys
lo___'ys = lo'ys
lo____'ys = lo'ys
lo_____'ys = lo'ys
lo______'ys = lo'ys
lo_______'ys = lo'ys

lo'ys'la, lo_'ys'la, lo__'ys'la, lo___'ys'la, lo____'ys'la, lo_____'ys'la, lo______'ys'la, lo_______'ys'la
 :: forall t tt l a o .
 Mapping T'I'II T'I'II (AR) (AR) (Covariant Day (AR) (P) (S) t (tt `L` tt `T` l) o o) t =>
 Arrow a (t o) -> Arrow a ((tt `L` tt `T` l) o) -> Arrow a (t o)
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
 Mapping T'I'II T'I'II (AR) (AR) (Covariant Day (AR) (P) (S) t (tt `L` tt `T` l) o o) t =>
 Covariant Yoneda Functor (AR) (AR) (T'I'II Product (t o)) =>
 Covariant Yoneda Functor (AR) (AR) (T'II'I Product ()) =>
 t o -> (tt `L` tt `T` l) o -> (t o)
lu'ys'la l r = ys'yo (lu @(t o `P` _) l r) (identity @(AR) `la` identity)

lu_'ys'la = lu'ys'la
lu__'ys'la = lu'ys'la
lu___'ys'la = lu'ys'la
lu____'ys'la = lu'ys'la
lu_____'ys'la = lu'ys'la
lu______'ys'la = lu'ys'la
lu_______'ys'la = lu'ys'la

-- x `lo'la` y

-- target a o -> target a oo -> target a (Product o oo)

-- cn :: forall target a aa o oo .
 -- Cone T'I'II target target Product =>
 -- Functor T'I'II target target (T'I'II Product o) =>
 -- Functor T'I'II target target (T'I'II Product aa) =>
 -- Functor T'I'II target target (T'II'I Product aa) =>
 -- Wrapper target (T'I'II Product o aa) =>
 -- Wrapper target (T'I'II Product o oo) =>
 -- Wrapper target (T'II'I Product aa o) =>
 -- Wrapper target (T'II'I Product aa a) =>
 -- (forall e . Wrapper target (T'II'I Product aa e)) =>
 -- target a o -> target aa oo -> target (Product a aa) (Product o oo)
-- cn l r = fio r `compose` foi l

-- target a o -> target a oo -> target a (Product target o oo)

-- cnz :: forall target e a aa o oo .
 -- Cone T'I'II target target (Object T'I'II target) =>
 -- Functor T'I'II target target (T'I'II (Product target) o) =>
 -- Functor T'I'II target target (T'I'II (Product target) aa) =>
 -- Functor T'I'II target target (T'II'I (Product target) aa) =>
 -- Wrapper target (T'I'II (Product target) o aa) =>
 -- Wrapper target (T'I'II (Product target) o oo) =>
 -- Wrapper target (T'II'I (Product target) aa o) =>
 -- Wrapper target (T'II'I (Product target) aa a) =>
 -- Elicitable T'I'II target e =>
 -- (Supertype e ~ (Product target a aa)) =>
 -- target a o -> target aa oo -> target e (Product target o oo)
-- cnz l r = fio r `compose` foi l `compose` _' @target

-- TODO: try to generalize
-- cn'yp, yi'cn'yp :: forall t a aa o oo .
 -- Mapping T'I'II T'I'II (AR) (AR) (Covariant Day (AR) (Product (AR)) (Product (AR)) t t o oo) t =>
 -- Arrow a (t o) -> Arrow aa (t oo) -> Arrow (Product (AR) a aa) (t (Product Arrow o oo))
-- cn'yp l r = yp `compose` cn l r

-- yi'cn'yp = cn'yp

-- TODO: try to generalize
-- cnz'yp, yi'cnz'yp :: forall e t a aa o oo .
--  Mapping T'I'II T'I'II (AR) (AR) (Covariant Day (AR) (Product (AR)) (Product (AR)) t t o oo) t =>
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

lu, lu_, lu__, lu___, lu____, lu_____, lu______, lu_______ :: forall ooo o oo .
 Limit T'I'II (AR) (AR) =>
 Mapping T'I'II T'I'II (AR) (AR) I (T'I'I Product) =>
 Covariant Yoneda Functor (AR) (AR) (T'I'II Product o) =>
 Covariant Yoneda Functor (AR) (AR) (T'II'I Product ()) =>
 Contravariant Objective (AR) ooo (o `P` oo) =>
 Wrapper (AR) (T'I'I Product ()) =>
 Wrapper (AR) (I ()) =>
 o -> oo -> ooo
lu l r = objective @T'II'I (wrapped (map @T'I'II @T'I'II @(AR) @(AR) @I @(T'I'I Product) identity) Unit `yui` l `yiu` r)

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
 -- source e o -> source e oo -> Product o oo
-- ho'lu l r = wrapped (map @T'I'II @T'I'II @(AR) @(AR) @I @(T'I'I Product) identity) () `yui` l `yiu` r

la, la_, la__, la___, la____, la_____, la______, la_______ :: forall source i a o oo .
 Category source =>
 Limit T'II'I source source =>
 Covariant Objective source a (o `S` oo) =>
 Covariant Endo Semi Functor source (S'I'II o) =>
 Covariant Endo Semi Functor source (T'II'I Sum i) =>
 (forall ee eee . Wrapper source (S'I'II ee eee)) =>
 (forall ee eee . Wrapper source (T'II'I Sum ee eee)) =>
 (forall ee . Wrapper source (T'I'I Sum ee)) =>
 (forall ee . Wrapper source (I ee)) =>
 source o i -> source oo i -> source a i
la l r = wrapped (map @T'II'I @T'II'I @source @source @I @(Both Sum) identity)
 `compose` foi @source @source l
 `compose` fio @source @source r
 `compose` objective @T'I'II @source @a @(o `S` oo)

la_ = la
la__ = la
la___ = la
la____ = la
la_____ = la
la______ = la
la_______ = la

lv, lv_, lv__, lv___, lv____, lv_____, lv______, lv_______
 :: forall a aa aaa o .
 Covariant Endo Semi Functor (AR) (S'I'II aa) =>
 Covariant Endo Semi Functor (AR) (T'II'I Sum o) =>
 Covariant Objective (AR) a (aa `S` aaa) =>
 (forall ee eee . Wrapper (AR) (S'I'II ee eee)) =>
 (forall ee eee . Wrapper (AR) (T'II'I Sum ee eee)) =>
 (forall ee . Wrapper (AR) (T'I'I Sum ee)) =>
 (forall ee . Wrapper (AR) (I ee)) =>
 Wrapper (AR) ((AR) Unit o) =>
 (Supertype ((AR) Unit o) ~ o) =>
 o -> o -> a -> o
lv l r = wrapped (map @T'II'I @T'II'I @(AR) @(AR) @I @(Both Sum) identity)
 `compose` fui @(AR) @(AR) l
 `compose` fiu @(AR) @(AR) r
 `compose` objective @T'I'II @(AR) @a @(aa `S` aaa)

lv_ l r = wrapped (map @T'II'I @T'II'I @(AR) @(AR) @I @(Both Sum) identity)
 `compose` fui @(AR) @(AR) l
 `compose` fiu @(AR) @(AR) r
 `compose` objective @T'I'II @(AR) @a @(aa `S` aaa)
lv__ l r = wrapped (map @T'II'I @T'II'I @(AR) @(AR) @I @(Both Sum) identity)
 `compose` fui @(AR) @(AR) l
 `compose` fiu @(AR) @(AR) r
 `compose` objective @T'I'II @(AR) @a @(aa `S` aaa)
lv___ l r = wrapped (map @T'II'I @T'II'I @(AR) @(AR) @I @(Both Sum) identity)
 `compose` fui @(AR) @(AR) l
 `compose` fiu @(AR) @(AR) r
 `compose` objective @T'I'II @(AR) @a @(aa `S` aaa)
lv____ l r = wrapped (map @T'II'I @T'II'I @(AR) @(AR) @I @(Both Sum) identity)
 `compose` fui @(AR) @(AR) l
 `compose` fiu @(AR) @(AR) r
 `compose` objective @T'I'II @(AR) @a @(aa `S` aaa)
lv_____ l r = wrapped (map @T'II'I @T'II'I @(AR) @(AR) @I @(Both Sum) identity)
 `compose` fui @(AR) @(AR) l
 `compose` fiu @(AR) @(AR) r
 `compose` objective @T'I'II @(AR) @a @(aa `S` aaa)
lv______ l r = wrapped (map @T'II'I @T'II'I @(AR) @(AR) @I @(Both Sum) identity)
 `compose` fui @(AR) @(AR) l
 `compose` fiu @(AR) @(AR) r
 `compose` objective @T'I'II @(AR) @a @(aa `S` aaa)
lv_______ l r = wrapped (map @T'II'I @T'II'I @(AR) @(AR) @I @(Both Sum) identity)
 `compose` fui @(AR) @(AR) l
 `compose` fiu @(AR) @(AR) r
 `compose` objective @T'I'II @(AR) @a @(aa `S` aaa)

-- `yp`: u (t e) (t ee) -> t (uu e ee)
-- `hs`: source o i -> source oo i -> source (o `S` oo) i
-- `lo`: target a o -> target a oo -> target a (o `P` oo)
--     : u (source o i) (source oo i) -> source (uu o oo) i

-- TODO: to test
-- rwr'hs :: forall source target r o a aa .
 -- Category source =>
 -- Limit T'II'I source target =>
 -- Covariant Functor target target (S'I'II a) =>
 -- Covariant Functor target target (T'II'I Sum (Sum (Supertype r) (Supertype r))) =>
 -- Elicitable T'II'I target (Both Sum (Sum (Supertype r) (Supertype r))) =>
 -- Elicitable T'II'I target (S'I'II a aa) =>
 -- Elicitable T'I'II target (S'I'II (Supertype r) (Supertype r)) =>
 -- Elicitable T'I'II target (T'II'I Sum (Supertype r) (Supertype r)) =>
 -- Elicitable T'II'I target (Both Sum (Supertype r)) =>
 -- Elicitable T'I'II target (That Sum a (Sum (Supertype r) (Supertype r))) =>
 -- Elicitable T'II'I target (T'II'I Sum (Sum (Supertype r) (Supertype r)) a) =>
 -- Elicitable T'I'II target (T'II'I Sum (Sum (Supertype r) (Supertype r)) (Sum (Supertype r) (Supertype r))) =>
 -- (Supertype o ~ Sum a aa) =>
 -- (forall eee_ . Wrapper target (I eee_)) =>
 -- Elicitable T'II'I target r =>
 -- Elicitable T'I'II target o =>
 -- source a (Supertype r) -> source aa (Supertype r) -> target o r
-- rwr'hs l r = rwr /
 -- wrapped (map @T'II'I @T'II'I @source @target @I @(Both Sum) identity) `compose`
 -- wrapped (map @T'II'I @T'II'I @source @target @I @(Both Sum) identity) `compose`
 -- i_ (map @T'I'II @T'I'II (wrapped (left @T'II'I l))) `compose`
 -- __ (map @T'I'II @T'I'II (wrapped (right @T'II'I r)))

-- TODO: try to generalize
yp :: forall u e ee t tt l .
 Mapping T'I'II T'I'II (AR) (AR) (Covariant Day (AR) u (P) t (tt `L` tt `T` l) e ee) t =>
 -- Covariant Monoidal Functor (AR) (AR) u (P) l t =>
 u (t e) (tt `L` tt `T` l `T` ee) -> t (e `P` ee)
yp = day @T'I'II @(AR) @l @t @tt @u @(P) identity identity

-- TODO: try to generalize
yp'yo, yp_'yo :: forall e ee r t tt l .
 Mapping T'I'II T'I'II (AR) (AR) (Covariant Day (AR) (P) P t (tt `L` tt `T` l) e ee) t =>
 t e `P` (tt `L` tt `T` l) ee -> (e `P` ee `AR` r) -> t r
yp'yo x f = day @T'I'II @(AR) @l @t @tt @(P) @P identity f x

yp_'yo = yp'yo

yp'yo'hd :: forall e ee r t tt l .
 Mapping T'I'II T'I'II (AR) (AR) (Covariant Day (AR) (P) P t (tt `L` tt `T` l) e ee) t =>
 t e `P` (tt `L` tt `T` l) ee -> (e `AR_` ee `AR` r) -> t r
yp'yo'hd x f = day @T'I'II @(AR) @l @t @tt @(P) @P identity (fdi f) x

yp'yu :: forall e ee r t tt l .
 Mapping T'I'II T'I'II (AR) (AR) (Covariant Day (AR) (P) P t (tt `L` tt `T` l) e ee) t =>
 t e `P` (tt `L` tt `T` l) ee -> r -> t r
yp'yu x xx = day @T'I'II @(AR) @l @t @tt @(P) @P identity (constant xx) x

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
 Mapping T'I'II T'I'II (AR) (AR) (Covariant Day (AR) u (P) tt (tt `L` tt `T` ll) e ee) tt =>
 t (u (tt e) ((tt `L` tt `T` ll) ee)) -> t (tt (e `P` ee))
yo'yp = fo (day @T'I'II @(AR) @ll @tt @tt @u @(P) identity identity)

-- TODO: try to generalize
yio'yp :: forall u e ee eee t tt ll .
 Covariant Endo Semi Functor (AR) (T'I'II t eee) =>
 Mapping T'I'II T'I'II (AR) (AR) (Covariant Day (AR) u (P) tt (tt `L` tt `T` ll) e ee) tt =>
 t eee (u (tt e) ((tt `L` tt `T` ll) ee)) -> t eee (tt (e `P` ee))
yio'yp = fio (day @T'I'II @(AR) @ll @tt @tt @u @(P) identity identity)

-- TODO: try to generalize
ys :: forall u e ee t tt l .
 Mapping T'I'II T'I'II (AR) (AR) (Covariant Day (AR) u (S) t (tt `L` tt `T` l) e ee) t =>
 u (t e) ((tt `L` tt `T` l) ee) -> t (e `S` ee)
ys = day @T'I'II @(AR) @l @t @tt @u @(S) identity identity

-- TODO: try to generalize
ys'yo :: forall source t tt l e ee u r .
 Category source =>
 -- Covariant Monoidal Functor source (AR) u (S) l t =>
 Mapping T'I'II T'I'II source (AR) (Covariant Day source u (S) t (tt `L` tt `T` l) e ee) t =>
 u (t e) ((tt `L` tt `T` l) ee) -> source (e `S` ee) r -> t r
ys'yo x f = day @T'I'II @source @l @t @tt @u @(S) identity f x

-- TODO: try to generalize
ys'yu :: forall t tt l e ee u r .
 (forall e . Mapping T'I'II T'I'II (->) (->) I (T'I'II (AR) e)) =>
 Mapping T'I'II T'I'II (AR) (AR) (Covariant Day (AR) u (S) t (tt `L` tt `T` l) e ee) t =>
 u (t e) ((tt `L` tt `T` l) ee) -> r -> t r
ys'yu x r = day @T'I'II @(AR) @l @t @tt @u @(S) identity (constant r) x

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
yr :: forall u e ee t tt l .
 -- Covariant Monoidal Functor (AR) (AR) u (R) l t =>
 Mapping T'I'II T'I'II (AR) (AR) (Covariant Day (AR) u (R) t (tt `L` tt `T` l) e ee) t =>
 u (t e) ((tt `L` tt `T` l) ee) -> t (e `S` ee `S_` e `P` ee)
yr = day @T'I'II @(AR) @l @t @tt @u @(R) identity unwrap

-- TODO: try to generalize
yr'yo :: forall source u e ee r t tt ll .
 Category source =>
 Mapping T'I'II T'I'II source (AR) (Covariant Day source u (R) t (tt `L` tt `T` ll) e ee) t =>
 Wrapper source (e `R` ee) =>
 u (t e) (tt `L` tt `T` ll `T` ee) -> source (e `S` ee `S_` e `P` ee) r -> t r
yr'yo x f = day @T'I'II @source @ll @t @tt @u @(R) identity (f `compose` unwrap) x

-- TODO: try to generalize
yr'yokl :: forall source u e ee r t tt ttt l ll lll .
 Category source =>
 Covariant Endo Transformation Functor (AR) (t `T'TT'I` ttt `L` ttt `T` lll `L` t `T` l) (t `TT'T'I` ttt) =>
 Mapping T'I'II T'I'II source (AR) (Covariant Day source u (R) t (tt `L` tt `T` ll) e ee) t =>
 Wrapper source (e `R` ee) =>
 u (t e) (tt `L` tt `T` ll `T` ee) -> source (e `S` ee `S_` e `P` ee) (ttt `L` ttt `T` lll `L` t `T` l `T` r) -> ttt (t r)
yr'yokl x f = wrapped (component @(AR) @(t `T'TT'I` ttt `L` ttt `T` lll `L` t `T` l) @(t `TT'T'I` ttt))
 (day @T'I'II @source @ll @t @tt @u @(R) identity (f `compose` unwrap) x)

-- TODO: try to generalize
yp'yp :: forall u e ee t tt ttt tttt l ll .
 -- Covariant Monoidal Functor (AR) (AR) u (P) l t =>
 -- Covariant Monoidal Functor (AR) (AR) (P) P ll tt =>
 Covariant Transformation Functor (AR) (AR) (Covariant Day (AR) u (P) t (ttt `L` ttt `T` l) (tt e) (tttt `L` tttt `T` ll `T` ee)) t =>
 Covariant Transformation Functor (AR) (AR) (Covariant Day (AR) (P) P tt (tttt `L` tttt `T` ll) e ee) tt =>
 u (t (tt e)) ((ttt `L` ttt `T` l) (tttt `L` tttt `T` ll `T` ee)) -> t (tt (e `P` ee))
yp'yp = day @T'I'II @(AR) @l @t @ttt @u @(P) identity
 (day @T'I'II @(AR) @ll @tt @tttt @(P) @P identity identity)

-- TODO: generalize
yp'ys :: forall u e ee t tt l ll .
 Covariant Lax Monoidal Functor (AR) (AR) u (P) l t =>
 Covariant Lax Monoidal Functor (AR) (AR) (P) (S) ll tt =>
 u (t (tt e)) ((t `L` t `T` l) ((tt `L` tt `T` ll) ee)) -> t (tt (e `S` ee))
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
yp'yok :: forall i ii source target t tt ttt l ll o .
 Covariant Transformation Functor (AR) (AR) (Covariant Day (AR) (P) P t (ttt `L` ttt `T` l) i ii) t =>
 Covariant Endo Semi Functor target tt =>
 Covariant Endo Semi Functor target t =>
 Covariant Yoneda Functor source target t =>
 Covariant Endo Transformation Functor target (t `T'TT'I` tt `L` tt `T` ll) t =>
 (forall e ee . Wrapper target (T'I'II source e ee)) =>
 (forall e . Wrapper target ((t `T'TT'I` tt `L` tt `T` ll) e)) =>
 t i `P` (ttt `L` ttt `T` l) ii -> target (source (i `P` ii) ((tt `L` tt `T` ll) o)) (t o)
yp'yok = yok @source @target `compose` yp

-- TODO: try to generalize
yp'yokl :: forall e ee source target t tt ttt l ll lll o .
 Covariant Endo Transformation Functor target (t `T'TT'I` tt `L` tt `T` ll `L` t `T` l) (t `TT'T'I` tt) =>
 Covariant Transformation Functor (AR) (AR) (Covariant Day (AR) (P) P t (ttt `L` ttt `T` lll) e ee) t =>
 Covariant Yoneda Functor source target t =>
 Elicitable T'II'I target (T'I'II source (e `P` ee) (tt o)) =>
 (forall i . Wrapper target (t `T'TT'I` tt `T'I_` i)) =>
 (forall i . Wrapper target (TT'T'I t tt i)) =>
 (forall i . Wrapper target ((t `T'TT'I` tt `L` tt `T` ll `L` t `T` l) i)) =>
 (forall e ee . Wrapper target (T'I'II source e ee)) =>
 t e `P` (ttt `L` ttt `T` lll) ee -> target (source (e `P` ee) (tt `L` tt `T` ll `L` t `T` l `T` o)) (tt (t o))
yp'yokl = yokl @source @target `compose` yp

-- TODO: try to generalize
yp'yp'yo :: forall source e ee r t tt ttt tttt l ll .
 Covariant Transformation Functor (AR) (AR) (Covariant Day (AR) (P) P t (ttt `L` ttt `T` l) (tt e) (tttt `L` tttt `T` ll `T` ee)) t =>
 Covariant Transformation Functor source (AR) (Covariant Day source (P) P tt (tttt `L` tttt `T` ll) e ee) tt =>
 t (tt e) `P` (ttt `L` ttt `T` l) (tttt `L` tttt `T` ll `T` ee) -> source (e `P` ee) r -> t (tt r)
yp'yp'yo x f = day @T'I'II @(AR) @l @t @ttt @(P) @P identity
 (day @T'I'II @source @ll @tt @tttt @(P) @P identity f) x

-- w'rw :: forall target a o
 -- Precategory target =>
 -- Elicitable T'II'I target o =>
 -- Elicitable T'I'II target a =>
 -- target (Supertype a) (Supertype o) -> target a o
-- w'rw target = wrap @target `compose` target `compose` he @target

-- rw'w :: forall target a o .
 -- Precategory target =>
 -- Elicitable T'II'I target a =>
 -- Elicitable T'I'II target o =>
 -- target a o -> target (Supertype a) (Supertype o)
-- rw'w target = _' @target `compose` target `compose` wrap @target

-- yi__, yi___, yi____, yi_____, yi______ :: forall target a .
 -- Precategory target =>
 -- Elicitable T'I'II target a =>
 -- Elicitable T'I'II target (Supertype a) =>
 -- target a (Supertype (Supertype a))
-- yi__ = _' @target `compose` _' @target

-- yi___ = yi__
-- yi____ = yi__
-- yi_____ = yi__
-- yi______ = yi__

-- yi___, yi____, yi_____, yi______, yi_______ :: forall target a .
 -- Precategory target =>
 -- Elicitable T'I'II target a =>
 -- Elicitable T'I'II target (Supertype a) =>
 -- Elicitable T'I'II target (Supertype (Supertype a)) =>
 -- target a (Supertype (Supertype (Supertype a)))
-- yi___ = _' @target `compose` _' @target `compose` _' @target

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

-- TODO: defined manually temporarily, replace with generated version
yo'yok
 :: forall source target t tt ttt lll a o .
 Covariant Endo Semi Functor source tt =>
 Component source (tt `T'TT'I` ttt `L` ttt `T` lll) tt =>
 Covariant Yoneda Functor source target t =>
 Contravariant Endo Semi Functor (AR) (T'II'I target (t (tt o))) =>
 (forall e ee . Wrapper target (T'I'II source e ee)) =>
 (forall e . Wrapper source (tt `T'TT'I` ttt `L` ttt `T` lll `T'I_` e)) =>
 (t (tt a)) -> target (source (a) (ttt `L` ttt `T` lll `T'I` o)) (t (tt o))
yo'yok = fai (fok @source @source @tt @ttt) `compose` yo @source @target

-- TODO: defined manually temporarily, replace with generated version
ho'yok, ho_'yok, ho__'yok, ho___'yok, ho____'yok, ho_____'yok, ho______'yok, ho_______'yok, ho________'yok :: forall source u t tt ll a o e .
 Covariant Endo Semi Functor source tt =>
 Covariant Endo Semi Functor source t =>
 Mapping T'I'II T'I'II source source (t `T'TT'I` tt `L` tt `T` ll) t =>
 Covariant Yoneda Functor source (AR) (T'I'II u e) =>
 (forall ee . Wrapper source ((t `T'TT'I` tt `L` tt `T` ll) ee)) =>
 (forall ee . Wrapper source ((t `T'TT'I` tt) ee)) =>
 (forall ee . Wrapper source (tt `L` tt `T` ll `T` ee)) =>
 u e (t a) -> source a (tt `L` tt `T` ll `T` o) -> u e (t o)
ho'yok x = fai fok (ho @source x)

ho_'yok = ho'yok
ho__'yok = ho'yok
ho___'yok = ho'yok
ho____'yok = ho'yok
ho_____'yok = ho'yok
ho______'yok = ho'yok
ho_______'yok = ho'yok
ho________'yok = ho'yok

-- TODO: defined manually temporarily, replace with generated version
ho'yuk, ho_'yuk, ho__'yuk, ho___'yuk, ho____'yuk, ho_____'yuk, ho______'yuk, ho_______'yuk, ho________'yuk
 :: forall source t tt ll a o i .
 Covariant Endo Semi Functor source tt =>
 Constant Functor (AR) source t =>
 Covariant Endo Transformation Functor source (t `T'TT'I` tt `L` tt `T` ll) t =>
 Covariant Yoneda Functor source (AR) (T'I'II source i) =>
 (forall e . Wrapper source (t `T'TT'I` tt `L` tt `T` ll `T'I_` e)) =>
 (forall e . Wrapper source (I `T'I` tt `L` tt `T` ll `T` e)) =>
 source i (t a) -> (tt `L` tt `T` ll) o -> source i (t o)
ho'yuk x = fai (fuk @source @t @tt) (ho @source x)
ho_'yuk x = fai (fuk @source @t @tt) (ho @source x)
ho__'yuk x = fai (fuk @source @t @tt) (ho @source x)
ho___'yuk x = fai (fuk @source @t @tt) (ho @source x)
ho____'yuk x = fai (fuk @source @t @tt) (ho @source x)
ho_____'yuk x = fai (fuk @source @t @tt) (ho @source x)
ho______'yuk x = fai (fuk @source @t @tt) (ho @source x)
ho_______'yuk x = fai (fuk @source @t @tt) (ho @source x)
ho________'yuk x = fai (fuk @source @t @tt) (ho @source x)

ha'kyo, ha_'kyo, ha__'kyo, ha___'kyo, ha____'kyo, ha_____'kyo, ha______'kyo, ha_______'kyo
 :: forall source target t tt ttt l a o i .
 Contravariant Yoneda Functor source target (T'II'I t i) =>
 Covariant Endo Semi Functor source tt =>
 Covariant Endo Semi Functor source ttt =>
 (forall e . Covariant Endo Semi Functor (AR) (T'I'II source e)) =>
 Covariant Endo Transformation Functor source tt (tt `T'TT'I` ttt `L` ttt `T` l) =>
 (forall e . Contravariant Endo Yoneda Functor (AR) (T'II'I target e)) =>
 (forall e . Wrapper source ((tt `T'TT'I` ttt `L` ttt `T` l) e)) =>
 (forall e . Wrapper source ((tt `T'TT'I` ttt) e)) =>
 (forall e . Wrapper source (ttt `L` ttt `T` l `T` e)) =>
 (forall e . Wrapper source (I `L` ttt `T` l `T` e)) =>
 (forall e . Wrapper source (I e)) =>
 (forall e ee . Wrapper target (T'II'I source e ee)) =>
 (forall e ee . Wrapper target (T'II'I t e ee)) =>
 t (tt o) i -> target (source (ttt a) (I `L` ttt `T` l `T` o)) (t (tt a) i)
ha'kyo = fai kfo `compose` ha @source @target @t

ha_'kyo = ha'kyo
ha__'kyo = ha'kyo
ha___'kyo = ha'kyo
ha____'kyo = ha'kyo
ha_____'kyo = ha'kyo
ha______'kyo = ha'kyo
ha_______'kyo = ha'kyo

ha'kyok, ha_'kyok, ha__'kyok, ha___'kyok, ha____'kyok, ha_____'kyok, ha______'kyok, ha_______'kyok
 :: forall source target t tt ttt tttt lll llll a o i .
 Contravariant Yoneda Functor source target (T'II'I t i) =>
 Covariant Endo Semi Functor source tt =>
 Covariant Endo Semi Functor source ttt =>
 (forall e . Covariant Endo Semi Functor (AR) (T'I'II source e)) =>
 Covariant Endo Transformation Functor source tt (tt `T'TT'I` ttt `L` ttt `T` lll) =>
 Covariant Endo Transformation Functor source (tt `T'TT'I` tttt `L` tttt `T` llll) tt =>
 (forall e . Contravariant Endo Yoneda Functor (AR) (T'II'I target e)) =>
 (forall e . Wrapper source (tt `T'TT'I` ttt `L` ttt `T` lll `T'I_` e)) =>
 (forall e . Wrapper source (tt `T'TT'I` ttt `T'I_` e)) =>
 (forall e . Wrapper source (tt `T'TT'I` tttt `L` tttt `T` llll `T'I_` e)) =>
 (forall e . Wrapper source (ttt `L` ttt `T` lll `T` e)) =>
 (forall e . Wrapper source (I e)) =>
 (forall e . Wrapper source (I `L` ttt `T` lll `T` e)) =>
 (forall e ee . Wrapper target (T'II'I source e ee)) =>
 (forall e ee . Wrapper target (T'II'I t e ee)) =>
 t (tt o) i -> target (source (ttt a) (I `L` ttt `T` lll `T'I` tttt `L` tttt `T` llll `T` o)) (t (tt a) i)
ha'kyok = fai kfok `compose` ha @source @target @t

ha_'kyok = ha'kyok
ha__'kyok = ha'kyok
ha___'kyok = ha'kyok
ha____'kyok = ha'kyok
ha_____'kyok = ha'kyok
ha______'kyok = ha'kyok
ha_______'kyok = ha'kyok

-- TODO: defined manually temporarily, replace with generated version later
ha'yok, ha_'yok, ha__'yok, ha___'yok, ha____'yok, ha_____'yok, ha______'yok, ha_______'yok, ha________'yok
 :: forall source target t tt ttt l a o i .
 Contravariant Yoneda Functor source target (T'II'I t i) =>
 Covariant Endo Semi Functor source tt =>
 Covariant Endo Semi Functor source ttt =>
 Covariant Endo Transformation Functor source (tt `T'TT'I` ttt `L` ttt `T` l) tt =>
 -- Contravariant Yoneda Functor source (AR) (T'II'I t i) =>
 (forall e . Contravariant Endo Yoneda Functor (AR) (T'II'I target e)) =>
 (forall e . Wrapper source ((tt `T'TT'I` ttt `L` ttt `T` l) e)) =>
 (forall e . Wrapper source ((tt `T'TT'I` ttt) e)) =>
 (forall e . Wrapper source (ttt `L` ttt `T` l `T` e)) =>
 (forall e ee . Wrapper target (T'II'I source e ee)) =>
 (forall e ee . Wrapper target (T'II'I t e ee)) =>
 t (tt o) i -> target (source a (ttt `L` ttt `T` l `T` o)) (t (tt a) i)
ha'yok = fai fok `compose` ha @source @target @t

ha_'yok = ha'yok
ha__'yok = ha'yok
ha___'yok = ha'yok
ha____'yok = ha'yok
ha_____'yok = ha'yok
ha______'yok = ha'yok
ha_______'yok = ha'yok
ha________'yok = ha'yok

-- TODO: defined manually temporarily, replace with generated version
ha'yuk, ha_'yuk, ha__'yuk, ha___'yuk, ha____'yuk, ha_____'yuk, ha______'yuk, ha_______'yuk, ha________'yuk
 :: forall target t tt ttt l a o i .
 Contravariant Yoneda Functor (AR) target (T'II'I t i) =>
 Covariant Endo Semi Functor (AR) tt =>
 Covariant Endo Semi Functor (AR) ttt =>
 Covariant Endo Transformation Functor (AR) (tt `T'TT'I` ttt `L` ttt `T` l) tt =>
 Contravariant Yoneda Functor (AR) (AR) (T'II'I t i) =>
 (forall e . Contravariant Yoneda Functor (AR) (AR) (T'II'I target e)) =>
 (forall e . Wrapper (AR) ((tt `T'TT'I` ttt `L` ttt `T` l) e)) =>
 (forall e . Wrapper (AR) (ttt `L` ttt `T` l `T` e)) =>
 (forall e ee . Wrapper target (T'II'I (AR) e ee)) =>
 (forall e . Wrapper target (T'II'I t i e)) =>
 t (tt o) i -> target (ttt `L` ttt `T` l `T` o) (t (tt a) i)
ha'yuk = fai fuk `compose` ha @(AR) @target @t

ha_'yuk = ha'yuk
ha__'yuk = ha'yuk
ha___'yuk = ha'yuk
ha____'yuk = ha'yuk
ha_____'yuk = ha'yuk
ha______'yuk = ha'yuk
ha_______'yuk = ha'yuk
ha________'yuk = ha'yuk

-- TODO: defined manually temporarily, replace with generated version
ha'yokl, ha_'yokl, ha__'yokl, ha___'yokl, ha____'yokl, ha_____'yokl, ha______'yokl, ha_______'yokl, ha________'yokl
 :: forall source target t tt ttt l ll a o i .
 Contravariant Yoneda Functor source target (T'II'I t i) =>
 Covariant Endo Semi Functor source tt =>
 Covariant Endo Semi Functor source ttt =>
 Covariant Endo Transformation Functor source (tt `T'TT'I` ttt `L` ttt `T` ll `L` tt `T` l) (tt `TT'T'I` ttt) =>
 (forall e . Contravariant Endo Yoneda Functor (AR) (T'II'I target e)) =>
 Contravariant Yoneda Functor source (AR) (T'II'I t i) =>
 (forall e . Wrapper source ((tt `T'TT'I` ttt `L` ttt `T` ll `L` tt `T` l) e)) =>
 (forall e . Wrapper source ((tt `T'TT'I` ttt) e)) =>
 (forall e . Wrapper source ((tt `TT'T'I` ttt) e)) =>
 (forall e . Wrapper source (ttt `L` ttt `T` l `T` e)) =>
 (forall e ee . Wrapper target (T'II'I source e ee)) =>
 (forall e ee . Wrapper target (T'II'I t e ee)) =>
 t (ttt (tt o)) i -> target (source a (ttt `L` ttt `T` ll `L` tt `T` l `T` o)) (t (tt a) i)
ha'yokl = fai fokl `compose` ha @source @target @t

ha_'yokl = ha'yokl
ha__'yokl = ha'yokl
ha___'yokl = ha'yokl
ha____'yokl = ha'yokl
ha_____'yokl = ha'yokl
ha______'yokl = ha'yokl
ha_______'yokl = ha'yokl
ha________'yokl = ha'yokl

-- TODO: defined manually temporarily, replace with generated version
yai'yukl, ha'yukl, ha_'yukl, ha__'yukl, ha___'yukl, ha____'yukl, ha_____'yukl, ha______'yukl, ha_______'yukl, ha________'yukl
 :: forall target t ttt tt l ll a o i .
 Constant Endo Semi Functor (AR) ttt =>
 Covariant Endo Semi Functor (AR) tt =>
 Covariant Endo Transformation Functor (AR) (ttt `T'TT'I` tt `L` tt `T` ll `L` ttt `T` l) (ttt `TT'T'I` tt) =>
 Contravariant Yoneda Functor (AR) target (T'II'I t i) =>
 (forall e . Contravariant Endo Semi Functor (AR) (T'II'I target e)) =>
 (forall e . Covariant Semi Functor target (AR) (T'I'II target e)) =>
 (forall e . Wrapper (AR) ((ttt `T'TT'I` tt `L` tt `T` ll `L` ttt `T` l) e)) =>
 (forall e . Wrapper (AR) ((ttt `T'TT'I` tt) e)) =>
 (forall e . Wrapper (AR) ((ttt `TT'T'I` tt) e)) =>
 (forall e . Wrapper (AR) (tt `L` tt `T` l `T` e)) =>
 (forall e ee . Wrapper target (T'II'I AR e ee)) =>
 (forall e . Wrapper target (T'II'I t i e)) =>
 Wrapper (AR) (I `T'I_` tt `L` tt `T` ll `L` ttt `T` l `T'I` o) =>
 t (tt (ttt o)) i -> target (tt `L` tt `T` ll `L` ttt `T` l `T` o) (t (ttt a) i)
yai'yukl = fai fukl `compose` ha @(AR) @target @t

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
-- yok'ho :: forall source t tt l a o e .
 -- Covariant Functor (AR) (AR) tt =>
 -- Contravariant Functor (AR) (AR) (T'II'I source (t o)) =>
 -- Covariant Functor source source (T'I'II source e) =>
 -- Contravariant Functor source source (T'II'I source o) =>
 -- Covariant Functor (AR) source t =>
 -- Covariant Functor source source t =>
 -- Covariant Functor (AR) (AR) t =>
 -- Covariant Functor (AR) source tt =>
 -- Covariant Functor source source tt =>
 -- Covariant Yoneda Functor source source t =>
 -- Contravariant Yoneda Functor source (AR) (T'II'I source (tt `L` tt `T` l `T` o)) =>
 -- Mapping T'I'II T'I'II source source (T'TT'I t (tt `L` tt `T` l)) t =>
 -- (forall ee . Wrapper source ((t `T'TT'I` tt `L` l) ee)) =>
 -- Wrapper source (T'II'I source e (tt `L` tt `T` l `T` o)) =>
 -- Wrapper source (T'I'II source e (tt `L` tt `T` l `T` o)) =>
 -- (forall ee . Wrapper source (tt `L` tt `T` l `T` ee)) =>
 -- (forall ee . Wrapper source (T'I'II source e ee)) =>
 -- Wrapper source (T'II'I source o a) =>
 -- Wrapper source (T'II'I source o e) =>
 -- Wrapper source (T'I'II source e a) =>
 -- t e -> source a (tt `L` tt `T` l `T` o) -> source (source e a) (t o)
-- yok'ho x f = yok x `compose` fio f

-- TODO: try to gereralize
-- yok'ha :: forall target t tt l a o i .
 -- Category target =>
 -- Covariant Yoneda Functor target target t =>
 -- Covariant Functor target target t =>
 -- Covariant Functor target target tt =>
 -- Contravariant Functor target target (T'II'I target (tt `L` tt `T` l `T` o)) =>
 -- Contravariant Yoneda Functor target (AR) (T'II'I target (tt `L` tt `T` l `T` o)) =>
 -- Mapping T'I'II T'I'II target target (T'TT'I t (tt `L` tt `T` l)) t =>
 -- (forall e . Wrapper target ((t `T'TT'I` tt `L` l) e)) =>
 -- (forall e . Wrapper target (tt `L` tt `T` ll `T` e)) =>
 -- (forall e ee . Wrapper target (T'I'II target e (tt `L` tt `T` l `T` ee))) =>
 -- (forall e ee . Wrapper target (T'II'I target (tt `L` tt `T` ll `T` e) ee)) =>
 -- t i -> target i a -> target (target a (tt `L` tt `T` l `T` o)) (t o)
-- yok'ha x f = yok @target @target x `compose` fai @target f

-- yok'hj, yok_'hj, yok__'hj, yok___'hj, yok____'hj, yok_____'hj, yok______'hj
 -- :: forall source t tt ttt tttt l a o e .
 -- Category source =>
 -- Adjoint Functor source source (T'II'I ttt e) (T'I'II tttt e) =>
 -- Contravariant Functor (AR) (AR) (T'II'I source (t o)) =>
 -- Covariant Functor source source t =>
 -- Covariant Functor source source tt =>
 -- Covariant Endo Transformation Functor source (T'TT'I t (tt `L` tt `T` l)) t =>
 -- Covariant Yoneda Functor source source t =>
 -- (forall ee . Wrapper source (T'I'II source (ttt a e) (tt `L` tt `T` l `T` ee))) =>
 -- (forall ee . Wrapper source (T'II'I ttt e ee)) =>
 -- (forall ee . Wrapper source (T'II'I tttt e (tt `L` l `T'I` ee))) =>
 -- (forall ee . Wrapper source (T'I'II tttt e (tt `L` l `T'I` ee))) =>
 -- (forall ee . Wrapper source (tt `L` tt `T` l `T` ee)) =>
 -- (forall ee . Wrapper source (t `T'TT'I` tt `L` l `WR___` ee)) =>
 -- (forall ee . Wrapper source (I (tt `L` l `T'I` ee))) =>
 -- (forall ee . Wrapper source (T'II'I ttt e `T'TT'I` T'I'II tttt e `WR___` tt `L` l `T'I` ee)) =>
 -- t (ttt a e) -> source (source a (tttt e (tt `L` tt `T` l `T` o))) (t o)
-- yok'hj x = fai hj (yok @source @source x)

-- yok_'hj = yok'hj
-- yok__'hj = yok'hj
-- yok___'hj = yok'hj
-- yok____'hj = yok'hj
-- yok_____'hj = yok'hj
-- yok______'hj = yok'hj

-- yok'hu :: forall source t tt a o e .
  -- Precategory source =>
  -- Covariant Yoneda Functor source source t =>
  -- Mapping T'I'II T'I'II source source (T'I'II source e) (T'I'II source e) =>
  -- Constant Semi Functor source source (T'I'II source e) =>
  -- Covariant Semi Functor source source t =>
  -- Covariant Semi Functor (AR) source t =>
  -- Covariant Semi Functor source (AR) tt =>
  -- Covariant Semi Functor (AR) source tt =>
  -- Mapping T'I'II T'I'II (AR) source (T'TT'I t tt) t =>
  -- (forall ee . Wrapper source ((t `T'TT'I` tt) ee)) =>
  -- Elicitable T'II'I source (T'TT'I t tt o) =>
  -- Wrapper source (T'I'II source e (tt o)) =>
  -- Elicitable T'II'I source (T'I'II source e a) =>
  -- Elicitable T'II'I source (U_1_I source a (tt o)) =>
  -- Elicitable T'II'I (AR) (U_1_I source a (tt o)) =>
  -- t e -> Supertype (U_1_I source a (tt o)) -> source (source e a) (t o)
-- yok'hu x f = yok @_ @_ @tt x `compose` fiu @source f

-- yokl__ :: forall source u t tt a o e .
 -- Category source =>
 -- -- Covariant Endo Semi Functor source tt =>
 -- Covariant Functor source source (T'I'II u e) =>
 -- Covariant Functor (AR) u t =>
 -- Covariant Functor u u t =>
 -- -- Mapping T'I'II T'I'II source source (T'TT'I t tt) t =>
 -- Covariant Yoneda Functor source u t =>
 -- Covariant Yoneda Functor u source (T'I'II u e) =>
 -- Covariant Yoneda Functor source source (T'II'I u (t o)) =>
 -- -- Covariant Yoneda Functor source source t =>
 -- -- (forall ee . Wrapper source (T'TT'I t tt ee)) =>
 -- -- t (source a o) -> source (u e a) (t o)
 -- t (u e a) -> u (source a o) (t o)
-- yokl__ x = fai fio (yokl @source @u x)

ha'kyo, ha_'kyo, ha__'kyo, ha___'kyo, ha____'kyo, ha_____'kyo, ha______'kyo, ha_______'kyo
 :: forall source target t tt ttt l a o i .
 Contravariant Yoneda Functor source target (T'II'I t i) =>
 Covariant Endo Semi Functor source tt =>
 Covariant Endo Semi Functor source ttt =>
 (forall e . Covariant Endo Semi Functor (AR) (T'I'II source e)) =>
 Covariant Endo Transformation Functor source tt (tt `T'TT'I` ttt `L` ttt `T` l) =>
 (forall e . Contravariant Endo Yoneda Functor (AR) (T'II'I target e)) =>
 (forall e . Wrapper source ((tt `T'TT'I` ttt `L` ttt `T` l) e)) =>
 (forall e . Wrapper source ((tt `T'TT'I` ttt) e)) =>
 (forall e . Wrapper source (ttt `L` ttt `T` l `T` e)) =>
 (forall e ee . Wrapper target (T'II'I source e ee)) =>
 (forall e ee . Wrapper target (T'II'I t e ee)) =>
 t (tt o) i -> target (source (ttt a) (I `L` ttt `T` l `T` o)) (t (tt a) i)
ha'kyo = fai (kfo `compose` fai (unwrap @source @(ttt `L` ttt `T` l `T` _)) `compose` fio (unwrap @(AR) `compose` unwrap @(AR)))
 `compose` ha @source @target @t

ha_'kyo = ha'kyo
ha__'kyo = ha'kyo
ha___'kyo = ha'kyo
ha____'kyo = ha'kyo
ha_____'kyo = ha'kyo
ha______'kyo = ha'kyo
ha_______'kyo = ha'kyo

-- TODO: generalize
yio'yokl, ho'yokl, ho_'yokl, ho__'yokl, ho___'yokl, ho____'yokl, ho_____'yokl, ho______'yokl, ho_______'yokl, ho________'yokl
 :: forall source u t tt l ll a o e .
 Covariant Semi Functor source (AR) (T'I'II u e) =>
 Covariant Endo Semi Functor source tt =>
 Covariant Endo Semi Functor source t =>
 Covariant Endo Transformation Functor source (t `T'TT'I` tt `L` tt `T` ll `L` t `T` l) (t `TT'T'I` tt) =>
 Covariant Yoneda Functor source (AR) (T'I'II u e) =>
 (forall ee . Wrapper source ((t `T'TT'I` tt `L` tt `T` ll `L` t `T` l) ee)) =>
 (forall ee . Wrapper source ((t `T'TT'I` tt) ee)) =>
 (forall ee . Wrapper source ((t `TT'T'I` tt) ee)) =>
 (forall ee . Wrapper source (tt `L` tt `T` ll `L` t `T` l `T` ee)) =>
 (forall ee . Wrapper source (tt `L` tt `T` ll `T` ee)) =>
 u e (t a) -> source a (tt `L` tt `T` ll `L` t `T` l `T` o) -> u e (tt (t o))
yio'yokl x = fai fokl (ho @source x)

ho'yokl = yio'yokl
ho_'yokl = yio'yokl
ho__'yokl = yio'yokl
ho___'yokl = yio'yokl
ho____'yokl = yio'yokl
ho_____'yokl = yio'yokl
ho______'yokl = yio'yokl
ho_______'yokl = yio'yokl
ho________'yokl = yio'yokl

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
 :: forall source target u t tt ttt l ll lll a o i .
 Category source =>
 Covariant Yoneda Functor source target (T'I'II u i) =>
 Covariant Endo Semi Functor source t =>
 Covariant Endo Semi Functor source tt =>
 Covariant Semi Functor target source t =>
 Covariant Endo Semi Functor source ttt =>
 Covariant Semi Functor target source ttt =>
 Contravariant Semi Functor (AR) (AR) (T'II'I target (u i (ttt (t (tt o))))) =>
 Covariant Transformation Functor source source (t `T'TT'I` ttt `L` ttt `T` lll `L` t `T` ll) (t `TT'T'I` ttt) =>
 Covariant Transformation Functor source source (tt `T'TT'I` ttt `L` ttt `T` lll `L` tt `T` ll) (tt `TT'T'I` ttt) =>
 (forall e ee . Wrapper target (T'I'II source e ee)) =>
 (forall e . Wrapper target (T'I'II u i e)) =>
 (forall e . Wrapper source ((tt `TT'T'I` ttt) e)) =>
 (forall e . Wrapper source ((t `TT'T'I` ttt) e)) =>
 (forall e . Wrapper source (ttt `L` ttt `T` lll `T` e)) =>
 (forall e . Wrapper source (ttt `L` ttt `T` lll `L` tt `T` ll `L` t `T` l `T'I` e)) =>
 (forall e . Wrapper source ((tt `T'TT'I` ttt `L` ttt `T` lll `L` tt `T` ll) e)) =>
 (forall e . Wrapper source (t `T'TT'I` ttt `L` ttt `T` lll `L` t `T` ll `T'I_` e)) =>
 (forall e . Wrapper source (ttt `L` ttt `T` lll `L` t `T` ll `T` e)) =>
 (forall e . Wrapper source (ttt `L` ttt `T` lll `L` tt `T` ll `T` e)) =>
 u i (t (tt a)) -> target (source a (ttt `L` ttt `T` lll `L` tt `T` ll `L` t `T` l `T` o)) (u i (ttt (t (tt o))))
yio'yokl'yokl x = fai @(AR)
 (fokl @source @source @t @ttt @ll @lll
  `compose` fio @source (wrap @source @(ttt `L` ttt `T` lll `L` t `T` ll `T` _) `compose` wrap @source @(_ `L` _ `T` _ `T` _))
  `compose` fokl @source @source @tt @ttt @ll @lll
  `compose` fio @source (unwrap @source @(_ `L` _ `T` _ `T` _)))
 (yio @source x)

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
 :: forall target u t tt ttt l ll lll a o i .
 Covariant Yoneda Functor (AR) target (T'I'II u i) =>
 Covariant Endo Semi Functor (AR) t =>
 Constant Endo Semi Functor (AR) tt =>
 Covariant Semi Functor target (AR) t =>
 Covariant Endo Semi Functor (AR) ttt =>
 Covariant Semi Functor target (AR) ttt =>
 Contravariant Semi Functor (AR) (AR) (T'II'I target (u i (ttt (t (tt o))))) =>
 Covariant Transformation Functor (AR) (AR) (t `T'TT'I` ttt `L` ttt `T` lll `L` t `T` ll) (t `TT'T'I` ttt) =>
 Covariant Transformation Functor (AR) (AR) (tt `T'TT'I` ttt `L` ttt `T` lll `L` tt `T` ll) (tt `TT'T'I` ttt) =>
 (forall e ee . Wrapper target (T'I'II (AR) e ee)) =>
 (forall e . Wrapper target (T'I'II u i e)) =>
 (forall e . Wrapper (AR) ((tt `TT'T'I` ttt) e)) =>
 (forall e . Wrapper (AR) ((t `TT'T'I` ttt) e)) =>
 (forall e . Wrapper (AR) (ttt `L` ttt `T` lll `T` e)) =>
 (forall e . Wrapper (AR) (ttt `L` ttt `T` lll `L` tt `T` ll `L` t `T` l `T` e)) =>
 (forall e . Wrapper (AR) ((tt `T'TT'I` ttt `L` ttt `T` lll `L` tt `T` ll) e)) =>
 (forall e . Wrapper (AR) ((t `T'TT'I` ttt `L` ttt `T` lll `L` t `T` l) e)) =>
 (forall e . Wrapper (AR) (ttt `L` ttt `T` lll `L` t `T` l `T` e)) =>
 u i (t (tt a)) -> target (ttt `L` ttt `T` lll `L` tt `T` ll `L` t `T` l `T` o) (u i (ttt (t (tt o))))
yio'yokl'yukl x = fai @(AR)
 (fokl @(AR) @(AR) @t @ttt @ll @lll
  `compose` fio @(AR) (wrap @(AR) @(_ `L` _ `T` ll `T` _) `compose` wrap @(AR) @(_ `L` _ `T` _ `T` _))
  `compose` fukl @(AR) @tt @ttt @ll @lll
  `compose` unwrap @(AR) @(_ `L` _ `T` _ `T` _))
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
 Constant Endo Semi Functor (AR) t =>
 Covariant Endo Transformation Functor (AR) (t `T'TT'I` tt `L` tt `T` ll `L` t `T` l) (t `TT'T'I` tt) =>
 Covariant Endo Transformation Functor (AR) I (T'I'II (AR) a) =>
 Covariant Endo Yoneda Functor (AR) (T'I'II u e) =>
 (forall ee . Wrapper (AR) (t `T'TT'I` tt `L` tt `T` ll `L` t `T` l `T'I_` ee)) =>
 (forall ee . Wrapper (AR) ((t `T'TT'I` tt) ee)) =>
 (forall ee . Wrapper (AR) ((t `TT'T'I` tt) ee)) =>
 (forall ee . Wrapper (AR) (tt `L` tt `T` ll `L` t `T` l `T` ee)) =>
 (forall ee . Wrapper (AR) (tt `L` tt `T` ll `T` ee)) =>
 u e (t a) -> tt `L` tt `T` ll `L` t `T` l `T` o -> u e (tt (t o))
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

yio'yoikl, ho'yoikl, ho_'yoikl, ho__'yoikl, ho___'yoikl, ho____'yoikl, ho_____'yoikl, ho______'yoikl, ho_______'yoikl, ho________'yoikl
 :: forall source u t tt l ll a o i ii .
 Covariant Semi Functor source (AR) (T'I'II u i) =>
 Covariant Endo Semi Functor source tt =>
 Covariant Endo Semi Functor source (T'II'I t ii) =>
 Covariant Endo Transformation Functor source (T'II'I t ii `T'TT'I` tt `L` tt `T` ll `L` T'II'I t ii `T` l) (T'II'I t ii `TT'T'I` tt) =>
 Covariant Yoneda Functor source (AR) (T'I'II u i) =>
 (forall e . Wrapper source ((T'II'I t ii `T'TT'I` tt `L` tt `T` ll `L` T'II'I t ii `T` l) e)) =>
 (forall e . Wrapper source ((T'II'I t ii `T'TT'I` tt) e)) =>
 (forall e . Wrapper source ((T'II'I t ii `TT'T'I` tt) e)) =>
 (forall e . Wrapper source (tt `L` tt `T` ll `L` T'II'I t ii `T` l `T` e)) =>
 (forall e . Wrapper source (tt `L` tt `T` ll `T` e)) =>
 (forall e . Wrapper source (T'II'I t ii e)) =>
 u i (t a ii) -> source a (tt `L` tt `T` ll `L` T'II'I t ii `T` l `T` o) -> u i (tt (t o ii))
yio'yoikl x = fai foikl (ho @source x)

ho'yoikl = yio'yoikl
ho_'yoikl = yio'yoikl
ho__'yoikl = yio'yoikl
ho___'yoikl = yio'yoikl
ho____'yoikl = yio'yoikl
ho_____'yoikl = yio'yoikl
ho______'yoikl = yio'yoikl
ho_______'yoikl = yio'yoikl
ho________'yoikl = yio'yoikl

-- ha'yuk :: forall source t tt a o e .
--  Covariant Functor (AR) (AR) tt =>
--  Covariant Functor source source t =>
--  Covariant Functor source source tt =>
--  Contravariant Yoneda Functor source (AR) (T'II'I source (tt o)) =>
--  Mapping T'I'II T'I'II source source (T'TT'I tt t) tt =>
--  Constant Semi Functor source source tt =>
--  Elicitable T'II'I source (T'TT'I tt t o) =>
--  (forall ee . Wrapper source (T'TT'I tt t ee)) =>
--  Elicitable T'II'I source (T'TT'I tt tt o) =>
--  Elicitable T'II'I (AR) (U_1_I source a (t o)) =>
--  Supertype (U_1_I source a (t o)) -> source e (tt a) -> source e (tt o)
-- ha'yuk = ha `compose` fuk @source @tt @t

-- TODO: generalize
lu'yp, lu_'yp, lu__'yp, lu___'yp, lu____'yp, lu_____'yp, lu______'yp, lu_______'yp
 :: forall o oo t tt l .
 Mapping T'I'II T'I'II (AR) (AR) (Covariant Day (AR) (P) P t (tt `L` tt `T` l) o oo) t =>
 -- Covariant Monoidal Functor (AR) (AR) (P) P l t =>
 Covariant Yoneda Functor (AR) (AR) (T'I'II Product (t o)) =>
 Covariant Yoneda Functor (AR) (AR) (T'II'I Product ()) =>
 t o -> (tt `L` tt `T` l) oo -> t (o `P` oo)
lu'yp source_left r = yp (lu @(t o `P` _) source_left r)

lu_'yp = lu'yp
lu__'yp = lu'yp
lu___'yp = lu'yp
lu____'yp = lu'yp
lu_____'yp = lu'yp
lu______'yp = lu'yp
lu_______'yp = lu'yp

lu'yp'yo'q, lu_'yp'yo'q, lu__'yp'yo'q, lu___'yp'yo'q, lu____'yp'yo'q, lu_____'yp'yo'q, lu______'yp'yo'q, lu_______'yp'yo'q
 :: forall o t tt l .
 Mapping T'I'II T'I'II (AR) (AR) (Covariant Day (AR) (P) P t (tt `L` tt `T` l) o o) t =>
 -- Covariant Monoidal Functor (AR) (AR) (P) P l t =>
 Covariant Yoneda Functor (AR) (AR) (T'I'II Product (t o)) =>
 Covariant Yoneda Functor (AR) (AR) (T'II'I Product ()) =>
 Setoid (AR) o =>
 t o -> (tt `L` tt `T` l) o -> t (o `P` o `S` o)
lu'yp'yo'q source_left r = yp'yo (lu @(t o `P` _) source_left r) q

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
 Mapping T'I'II T'I'II (AR) (AR) (Covariant Day (AR) (P) (S) t (tt `L` tt `T` l) o oo) t =>
 Covariant Yoneda Functor (AR) (AR) (P'I'II (t o)) =>
 Covariant Yoneda Functor (AR) (AR) (T'II'I (P) ()) =>
 t o -> (tt `L` tt `T` l) oo -> t (o `S` oo)
lu'ys l r = ys (lu @(t o `P` _) l r)

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
 -- Covariant Yoneda Functor (AR) (AR) (P'I'II (t e o)) =>
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
 Covariant Transformation Functor (AR) (AR) (Covariant Day (AR) (P) P t (t `L` t `T` l) (tt o) (tt `L` tt `T` ll `T` oo)) t =>
 Covariant Transformation Functor (AR) (AR) (Covariant Day (AR) (P) P tt (tt `L` tt `T` ll) o oo) tt =>
 Covariant Yoneda Functor (AR) (AR) (T'I'II Product (t (tt o))) =>
 Covariant Yoneda Functor (AR) (AR) (T'II'I Product Unit) =>
 t (tt o) -> (t `L` t `T` l) ((tt `L` tt `T` ll) oo) -> t (tt (o `P` oo))
lu'yp'yp l r = yp'yp @(P) (lu @(t (tt o) `P` _) l r)

lu'yp'ys
 :: forall t tt l ll o oo .
 Covariant Lax Monoidal Functor (AR) (AR) (P) P l t =>
 Covariant Lax Monoidal Functor (AR) (AR) (P) (S) ll tt =>
 Covariant Endo Semi Functor (AR) t =>
 Covariant Yoneda Functor (AR) (AR) (T'II'I Product ()) =>
 Covariant Yoneda Functor (AR) (AR) (T'I'II Product (t (tt o))) =>
 t (tt o) -> (t `L` t `T` l) ((tt `L` tt `T` ll) oo) -> t (tt (o `S` oo))
lu'yp'ys l r = yp'ys (lu @(t (tt o) `P` _) l r)

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
 -- :: forall t tt l ll `T` o oo e ee .
 -- Covariant Monoidal Functor (AR) (AR) (P) P l (T'I'II t e) =>
 -- Covariant Monoidal Functor (AR) (AR) (P) (S) ll (T'I'II tt ee) =>
 -- Covariant Endo Semi Functor (AR) (T'I'II t e) =>
 -- Covariant Yoneda Functor (AR) (AR) (T'II'I Product ()) =>
 -- Covariant Yoneda Functor (AR) (AR) (T'I'II Product (t e (tt ee o))) =>
 -- t e (tt ee o) -> (t `L` t `T` l) e ((tt `L` tt `T` ll) ee oo) -> t e (tt ee (o `S` oo))
-- lu'yip'yis l r = yip'yis (lu l r)

lu'yr, lu_'yr, lu__'yr, lu___'yr, lu____'yr, lu_____'yr, lu______'yr, lu_______'yr
 :: forall e o oo t tt l .
 Mapping T'I'II T'I'II (AR) (AR) (Covariant Day (AR) (P) (R) t (tt `L` tt `T` l) o oo) t =>
 Covariant Yoneda Functor (AR) (AR) (T'II'I Product ()) =>
 Covariant Yoneda Functor (AR) (AR) (T'I'II Product (t o)) =>
 t o -> (tt `L` tt `T` l) oo -> t (o `S` oo `S_` o `P` oo)
lu'yr l r = yr (lu @(t o `P` _) l r)

lu_'yr = lu'yr
lu__'yr = lu'yr
lu___'yr = lu'yr
lu____'yr = lu'yr
lu_____'yr = lu'yr
lu______'yr = lu'yr
lu_______'yr = lu'yr

-- jt :: forall target f g e .
 -- Covariant Transformation Functor (AR) target (f `T'TT'I` g) (f `JNT` g) =>
 -- Elicitable T'II'I target ((f `T'TT'I` g) e) =>
 -- target (f (g e)) ((f `JNT` g) e)
-- jt = component @target @(f `T'TT'I` g) @(f `JNT` g) @e
 -- `compose` wrap @target @((f `T'TT'I` g) e)

-- TODO: generalize
-- yp'yp'jt :: forall e ee t tt .
 -- Covariant Transformation Functor (AR) (AR) (t `T'TT'I` tt) (t `JNT` tt) =>
 -- Covariant Monoidal Functor (AR) (AR) (P) P t =>
 -- Covariant Monoidal Functor (AR) (AR) (P) P tt =>
 -- t (tt e) `P` t (tt ee) -> (t `JNT` tt) (e `P` ee)
-- yp'yp'jt = jt `compose` day @T'I'II @(AR) @t @(P) @P identity
 -- (day @T'I'II @(AR) @tt @(P) @P identity identity)

-- TODO: generalize
-- yp'yp'jt'yok :: forall source target e ee t tt ttt o .
 -- Covariant Yoneda Functor source target t =>
 -- Covariant Semi Functor target target ttt =>
 -- Covariant Yoneda Functor source target (t `JNT` tt) =>
 -- Covariant Transformation Functor (AR) (AR) (t `T'TT'I` tt) (t `JNT` tt) =>
 -- Covariant Transformation Functor (AR) target (T'TT'I (t `JNT` tt) ttt) (t `JNT` tt) =>
 -- Covariant Monoidal Functor (AR) (P) P t =>
 -- Covariant Monoidal Functor (AR) (P) P tt =>
 -- Elicitable T'II'I target (T'I'II source (e `P` ee) (ttt o)) =>
 -- (forall e . Wrapper target (T'TT'I (JNT t tt) ttt e)) =>
 -- t (tt e) `P` t (tt ee) -> target (source (e `P` ee) (ttt o)) ((t `JNT` tt) o)
-- yp'yp'jt'yok = yok @source @target `compose` yp'yp'jt

q, q_, q__, q___, q____, q_____, q______, q_______, q________ ::
 forall target e .
 Setoid target e =>
 target (e `P` e) (e `P` e `S` e)
q = equality

q_ = q
q__ = q
q___ = q
q____ = q
q_____ = q
q______ = q
q_______ = q
q________ = q
