{-# LANGUAGE AllowAmbiguousTypes #-}
module Ya.Algebra.Operators where

import Ya.Algebra.Abstract
import Ya.Algebra.Definition
import Ya.Algebra.Instances ()

infixl 9 `ho`, `ho'ho`, `ho'ho'hu`, `ho'hu`, `ho'ha`, `ho'ha'he`, `ho'ha'he'he`, `ho'yo`, `ho'yioi`, `ho'yu`, `ho'yui`, `ho'yok`, `ho'yuk`, `ho'yokl`
 , `ho'he`
 , `ho'he'he`
 , `ho'he'he'he`
 , `ho'he'he'he'he`
infixl 8 `ho_`, `ho_'ho`, `ho_'ha`, `ho_'ha'he`, `ho_'ha'he'he`, `ho_'yo`, `ho_'yu`, `ho_'yok`, `ho_'yuk`, `ho_'yokl`
 , `ho_'he`
 , `ho_'he'he`
 , `ho_'he'he'he`
 , `ho_'he'he'he'he`
infixl 7 `ho__`, `ho__'ha`, `ho__'ha'he`, `ho__'ha'he'he`, `ho__'yo`, `ho__'yu`, `ho__'yok`, `ho__'yuk`, `ho__'yokl`
 , `ho__'he`
 , `ho__'he'he`
 , `ho__'he'he'he`
 , `ho__'he'he'he'he`
infixl 6 `ho___`, `ho___'ha`, `ho___'ha'he`, `ho___'ha'he'he`, `ho___'yo`, `ho___'yu`, `ho___'yok`, `ho___'yuk`, `ho___'yokl`
 , `ho___'he`
 , `ho___'he'he`
 , `ho___'he'he'he`
 , `ho___'he'he'he'he`
infixl 5 `ho____`, `ho____'ha`, `ho____'ha'he`, `ho____'ha'he'he`, `ho____'yo`, `ho____'yu`, `ho____'yok`, `ho____'yuk`, `ho____'yokl`
 , `ho____'he`
 , `ho____'he'he`
 , `ho____'he'he'he`
 , `ho____'he'he'he'he`
infixl 4 `ho_____`, `ho_____'ha`, `ho_____'ha'he`, `ho_____'ha'he'he`, `ho_____'yo`, `ho_____'yu`, `ho_____'yok`, `ho_____'yuk`, `ho_____'yokl`
 , `ho_____'he`
 , `ho_____'he'he`
 , `ho_____'he'he'he`
 , `ho_____'he'he'he'he`
infixl 3 `ho______`, `ho______'he`, `ho______'he'he`, `ho______'he'he'he`, `ho______'ha`, `ho______'ha'he`, `ho______'ha'he'he`, `ho______'yok`, `ho______'yuk`, `ho______'yokl`
infixl 2 `ho_______`, `ho_______'ha`, `ho_______'ha'he`, `ho_______'ha'he'he`, `ho_______'yok`, `ho_______'yuk`, `ho_______'yokl`
 , `ho_______'he`
 , `ho_______'he'he`
 , `ho_______'he'he'he`
 , `ho_______'he'he'he'he`
infixl 1 `ho________`, `ho________'ha`, `ho________'ha'he`, `ho________'ha'he'he`, `ho________'yok`-- , `ho________'yuk`
 , `ho________'he`
 , `ho________'he'he`
 , `ho________'he'he'he`
 , `ho________'he'he'he'he`

infixl 9 `ha`, `ha'ha`, `ha'ho`--, `ha'ho'hu`, `ha'hu` --, `ha'hu'he`, `ha'yo`, `ha'yioi`, `ha'yok`, `ha'yuk`
 , `ha'he`, `ha_ha`
infixl 8 `ha_`
 , `ha_'he`
infixl 7 `ha__`
 , `ha__'he`
infixl 6 `ha___`
 , `ha___'he`
infixl 5 `ha____`
 , `ha____'he`
infixl 4 `ha_____`
 , `ha_____'he`
infixl 3 `ha______`
 , `ha______'he`
infixl 2 `ha_______`
 , `ha_______'he`
infixl 1 `ha________`
 , `ha________'he`

infixl 9 `hu` --, `hu'he`, `hu'he'he`
infixl 8 `hu_`
infixl 7 `hu__`
infixl 6 `hu___`
infixl 5 `hu____`
infixl 4 `hu_____`
infixl 3 `hu______`
infixl 2 `hu_______`
infixl 1 `hu________`

infixl 9 `hd`, `hd'q`

infixl 9 `hj`, `hj'hj`
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

infixl 8 `lo`, `lo'yp`, `lo'ys`, `lo'ys'la`
infixl 7 `lo_`, `lo_'yp`, `lo_'ys`, `lo_'ys'la`
infixl 6 `lo__`, `lo__'yp`, `lo__'ys`, `lo__'ys'la`
infixl 5 `lo___`, `lo___'yp`, `lo___'ys`, `lo___'ys'la`
infixl 4 `lo____`, `lo____'yp`, `lo____'ys`, `lo____'ys'la`
infixl 3 `lo_____`, `lo_____'yp`, `lo_____'ys`, `lo_____'ys'la`
infixl 2 `lo______`, `lo______'yp`, `lo______'ys`, `lo______'ys'la`
infixl 1 `lo_______`, `lo_______'yp`, `lo_______'ys`, `lo_______'ys'la`

infixl 8 `la`
infixl 7 `la_`
infixl 6 `la__`
infixl 5 `la___`
infixl 4 `la____`
infixl 3 `la_____`
infixl 2 `la______`
infixl 1 `la_______`

infixl 8 `lu`, `lu'yp`, `lu'ys`, `lu'yp'yp`, `lu'yip`, `lu'yis`, `lu'yip'yp`, `lu'yip'yip`, `lu'yip'yis`
infixl 7 `lu_`, `lu_'yp`, `lu_'ys`
infixl 6 `lu__`, `lu__'yp`, `lu__'ys`
infixl 5 `lu___`, `lu___'yp`, `lu___'ys`
infixl 4 `lu____`, `lu____'yp`, `lu____'ys`
infixl 3 `lu_____`, `lu_____'yp`, `lu_____'ys`
infixl 2 `lu______`, `lu______'yp`, `lu______'ys`
infixl 1 `lu_______`, `lu_______'yp`, `lu_______'ys`

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

infixl 8 `yo`, `yo'yo`, `yo'ha`, `yo'hj`, `yo'yp`
infixl 7 `yo_`

infixl 7 `yok`, `yok'ha`, `yok'ho`, `yok'he`, `yok'he'he` --, `yok'yokl`, `yko`
infixl 6 `yok_`, `yok_'he`,  `yok_'he'he` --, `yok_'yokl`
infixl 5 `yok__`, `yok__'he`,  `yok__'he'he` --, `yok__'yokl`
infixl 4 `yok___`, `yok___'he`,  `yok___'he'he` --, `yok___'yokl`
infixl 3 `yok____`, `yok____'he`,  `yok____'he'he` --, `yok____'yokl`
infixl 2 `yok_____`, `yok_____'he`,  `yok_____'he'he` --, `yok_____'yokl`
infixl 1 `yok______`, `yok______'he`,  `yok______'he'he` --, `yok______'yokl`

infixl 6 `yiok`

infixl 7 `yuk`
infixl 6 `yuk_`
infixl 5 `yuk__`
infixl 4 `yuk___`
infixl 3 `yuk____`
infixl 2 `yuk_____`
infixl 1 `yuk______`

infixl 6 `yokl` --, `yokl'yok`, `yokl'yokl`
infixl 5 `yokl_`
infixl 4 `yokl__`
infixl 3 `yokl___`
infixl 2 `yokl____`
infixl 1 `yokl_____`

infixl 8 `ya`

infixl 8 `yu`

infixl 8 `yp`, `yp'yo`, `yp'yp`, `yp'yp'yo`, `yp'ys`, `yp'yok`, `yp'yokl` --, `yp'yp'jt`, `yp'yp'jt'yok`
infixl 7 `yp_'yo`, `yip`, `yip'yo`, `yip'yp`, `yip'yip`, `yip'yis`

infixl 8 `ys`, `ys'yo`
infixl 8 `yis`

infixl 7 `yoi`

infixl 7 `yai`, `yai'yai`

infixl 7 `yui`
infixl 7 `yiu`

infixl 7 `yio`, `yio'yo`, `yio'yp`


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

fok :: forall from into t tt l a o .
 Component Natural from into (T'TT'I t (L l tt)) t =>
 Castable Opposite into ((t `T'TT'I` L l tt) o) =>
 from a (L l tt o) -> into (t a) (t o)
fok from = component @Straight @from @into @(t `T'TT'I` L l tt) @t
 `compose` wrap `compose` fo from

fuk :: forall into t tt a o .
 Component Natural into into (T'TT'I t tt) t =>
 Component Natural into (->) Identity (U_I_II into a) =>
 Constant Semi Functor into into t =>
 Wrapper into (T'TT'I t tt o) =>
 Wrapper into (T'TT'I t t o) =>
 Wrapper into (Identity (tt o)) =>
 tt o -> into (t a) (t o)
fuk from = map @Straight @Straight @into @into @(t `T'TT'I` tt) @t identity
 `compose` wrap `compose` fu @into from

fokl :: forall from into t tt l a o .
 Covariant Semi Functor from into t =>
 Component Natural from into (t `T'TT'I` L l tt) (t `TT'T'I` tt) =>
 Castable Opposite into ((t `T'TT'I` L l tt) o) =>
 Castable Straight into (TT'T'I t tt o) =>
 from a (L l tt o) -> into (t a) (tt (t o))
fokl from = wrapped
 (component @Straight @from @into @(t `T'TT'I` L l tt) @(t `TT'T'I` tt))
 `compose` fo from

yi, yi_, yi__, yi___, yi____,  yi_____, yi______, yi_______
 :: forall from into a o .
 Precategory into =>
 Covariant Yoneda from into Identity =>
 Castable Opposite into (U_I_II from a o) =>
 Castable Straight into (Identity o) =>
 a -> into (from a o) o
yi x = unwrap `compose` yoneda @Straight (Identity x) `compose` wrap

yi_ = yi
yi__ = yi
yi___ = yi
yi____ = yi
yi_____ = yi
yi______ = yi
yi_______ = yi

yo, yo_, yi'yo :: forall from into t a o .
 Precategory into =>
 Covariant Yoneda from into t =>
 Castable Opposite into (U_I_II from a o) =>
 t a -> into (from a o) (t o)
yo x = yoneda @Straight x `compose` wrap

yo_ = yo
yi'yo = yo

yoi :: forall from into t e a o .
 Precategory into =>
 Covariant Yoneda from into (U_II_I t e) =>
 Castable Opposite into (Straight from a o) =>
 Castable Straight into (U_II_I t e o) =>
 t a e -> into (from a o) (t o e)
yoi = fio @into unwrap `compose` yo @from @into @(U_II_I t e) `compose` wrap

yio :: forall from into t e a o .
 Precategory into =>
 Covariant Yoneda from into (U_I_II t e) =>
 Castable Opposite into (Straight from a o) =>
 Castable Straight into (U_I_II t e o) =>
 t e a -> into (from a o) (t e o)
yio = fio @into unwrap `compose` yo @from @into @(U_I_II t e) `compose` wrap

-- yioi :: forall from into w e e__ a o .
--  Precategory into =>
--  Covariant Yoneda from into (W_III_I_II w e__ e) =>
--  Castable Opposite into (U_I_II from a o) =>
--  Castable Straight into (W_III_I_II w e__ e o) =>
--  w e a e__ -> into (from a o) (w e o e__)
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

-- TODO: try to gereralize
yo'ha :: forall into t tt a o e .
 Category into =>
 Covariant Yoneda into into t =>
 Covariant Functor into into t =>
 Contravariant Functor into into (U_II_I into o) =>
 Contravariant Yoneda into (->) (U_II_I into o) =>
 Wrapper into (U_I_II into e o) =>
 Wrapper into (U_II_I into o e) =>
 Wrapper into (U_II_I into o a) =>
 t e -> into e a -> into (into a o) (t o)
yo'ha x f = yo @into @into x `compose` fai @into f

yo'hj :: forall from into t tt ttt e a o .
 Precategory into =>
 Adjoint Functor from from (U_II_I ttt e) (U_I_II tt e) =>
 Covariant Functor from from (U_I_II tt e) =>
 Covariant Yoneda from into t =>
 (forall e_ . Wrapper from ((T'TT'I (U_I_II tt e) (U_II_I ttt e)) e_)) =>
 (forall e_ . Wrapper from ((T'TT'I (U_II_I ttt e) (U_I_II tt e)) e_)) =>
 (forall e_ . Wrapper from (Identity e_)) =>
 Castable Opposite from (U_II_I ttt e a) =>
 Castable Opposite from (U_I_II tt e o) =>
 Castable Opposite into (U_I_II from (ttt a e) o) =>
 Castable Opposite into (U_I_II from (tt e a) o) =>
 Contravariant Endo Semi Functor (->) (U_II_I into (t o)) =>
 t (ttt a e) -> into (from a (tt e o)) (t o)
yo'hj x = fai hj (yo @from @into x)

yio'yo :: forall from into t tt e a o .
 Precategory into =>
 Contravariant Endo Semi Functor (->) (U_II_I into (t e (tt o))) =>
 Covariant Yoneda from into (U_I_II t e) =>
 Covariant Functor from from tt =>
 Castable Opposite into (Straight from (tt a) (tt o)) =>
 Castable Straight into (U_I_II t e (tt o)) =>
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
 Contravariant Yoneda from into (U_II_I t e) =>
 Castable Opposite into (Opposite from a o) =>
 Castable Straight into (U_II_I t e o) =>
 t a e -> into (from o a) (t o e)
yai x = compose unwrap (yoneda @Opposite @from @into @(U_II_I t e) (wrap x) `compose` wrap)

yai'yai :: forall from into t tt e e_ a o .
 Precategory from =>
 Precategory into =>
 Contravariant Yoneda from into (U_II_I t e_) =>
 Contravariant Endo Semi Functor from (U_II_I tt e) =>
 Contravariant Endo Semi Functor (->) (U_II_I into (t (tt o e) e_)) =>
 Wrapper from (U_II_I tt e o) =>
 Wrapper from (U_II_I tt e a) =>
 Castable Straight into (U_II_I t e_ (tt o e)) =>
 Castable Opposite into (U_II_I from (tt a e) (tt o e)) =>
 t (tt a e) e_ -> into (from a o) (t (tt o e) e_)
yai'yai x = fai fai (yai @from @into x)

yok, yok_, yok__, yok___, yok____, yok_____, yok______
 , li'yok, li_'yok, li__'yok, li___'yok, li____'yok, li_____'yok, li______'yok, li_______'yok
 :: forall from into tt t label a o .
 Component Natural into into (T'TT'I t (Labeled label tt)) t =>
 Covariant Yoneda from into t =>
 Castable Opposite into (U_I_II from a (Labeled label tt o)) =>
 Castable Opposite into (T'TT'I t (Labeled label tt) o) =>
 t a -> into (from a (Labeled label tt o)) (t o)
yok x = component @U_I_II @into @into @(T'TT'I t (Labeled label tt))
 `compose` wrap @into @(T'TT'I t (Labeled label tt) _)
 `compose` yoneda @U_I_II @from x
 `compose` wrap

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

yok'he, yok_'he, yok__'he, yok___'he, yok____'he, yok_____'he, yok______'he
 :: forall from into tt t label a o .
 Component Natural into into (T'TT'I t (Labeled label tt)) t =>
 Covariant Semi Functor into into tt =>
 Covariant Yoneda from into t =>
 Contravariant Semi Functor from into (U_II_I from (Labeled label tt o)) =>
 Wrapper into (U_I_II from a (Labeled label tt o)) =>
 Wrapper into (U_II_I from (Labeled label tt o) a) =>
 Wrapper into (U_II_I from (Labeled label tt o) (Supertype a)) =>
 (forall e . Wrapper into (T'TT'I t (Labeled label tt) e)) =>
 Wrapper into (T'TT'I t (Labeled label tt) o) =>
 Castable Straight from a =>
 t a -> into (from (Supertype a) (Labeled label tt o)) (t o)
yok'he x = yok @from @into x `compose` fai @from he

yok_'he = yok'he
yok__'he = yok'he
yok___'he = yok'he
yok____'he = yok'he
yok_____'he = yok'he
yok______'he = yok'he

yok'he'he, yok_'he'he, yok__'he'he, yok___'he'he, yok____'he'he, yok_____'he'he, yok______'he'he
 :: forall from into tt t label a o .
 Component Natural into into (T'TT'I t (Labeled label tt)) t =>
 Covariant Semi Functor into into tt =>
 Covariant Yoneda from into t =>
 Contravariant Semi Functor from into (U_II_I from (Labeled label tt o)) =>
 Wrapper into (U_I_II from a (Labeled label tt o)) =>
 Wrapper into (U_II_I from (Labeled label tt o) a) =>
 Wrapper into (U_II_I from (Labeled label tt o) (Supertype (Supertype a))) =>
 (forall e . Wrapper into (T'TT'I t (Labeled label tt) e)) =>
 Castable Straight from a =>
 Castable Straight from (Supertype a) =>
 t a -> into (from (Supertype (Supertype a)) (Labeled label tt o)) (t o)
yok'he'he x = yok @from @into x `compose` fai @from he'he

yok_'he'he = yok'he'he
yok__'he'he = yok'he'he
yok___'he'he = yok'he'he
yok____'he'he = yok'he'he
yok_____'he'he = yok'he'he
yok______'he'he = yok'he'he

yuk, yuk_, yuk__, yuk___, yuk____, yuk_____, yuk______, yi'yuk
 :: forall into tt t label a o .
 Covariant Yoneda into into t =>
 Component Natural into into (T'TT'I t (Labeled label tt)) t =>
 Mapping Straight Straight into into Identity (U_I_II into a) =>
 Wrapper into (T'TT'I t (Labeled label tt) o) =>
 Wrapper into (Identity (Labeled label tt o)) =>
 Wrapper into (U_I_II into a (Labeled label tt o)) =>
 t a -> into (Labeled label tt o) (t o)
yuk x = yok @into @into x `compose` constant

-- yok x = component @Straight @(->) @into @(T'TT'I t tt)
 -- `compose` wrap @into @(T'TT'I t tt _)
 -- `compose` yoneda @Straight @from x
 -- `compose` wrap

yuk_ = yuk @into @tt
yuk__ = yuk @into @tt
yuk___ = yuk @into @tt
yuk____ = yuk @into @tt
yuk_____ = yuk @into @tt
yuk______ = yuk @into @tt
yi'yuk = yuk @into @tt

-- TODO: try to generalize
-- yko :: forall from into tt t a o .
--  Precategory into =>
--  Component Natural (->) (->) t (T'TT'I t tt) =>
--  Covariant Yoneda from into t =>
--  Castable Opposite into (Straight from (tt a) o) =>
--  t a -> into (from (tt a) o) (t o)
-- yko = yoneda @Straight @from @into identity `compose` unwrap
--  `compose` component @Straight @(->) @(->) @t @(T'TT'I t tt)

yokl, yokl_, yokl__, yokl___, yokl____, yokl_____, li'yokl :: forall from into tt t l a o .
 Component Natural from into (t `T'TT'I` L l tt) (t `TT'T'I` tt) =>
 Covariant Yoneda from into t =>
 (forall i . Wrapper into ((t `T'TT'I` L l tt) i)) =>
 (forall i . Wrapper into ((t `TT'T'I` tt) i)) =>
 (forall i ii . Wrapper into (U_I_II from i (L l tt ii))) =>
 t a -> into (from a (L l tt o)) (tt (t o))
yokl x = unwrap @into @(TT'T'I t tt _)
 `compose` component @Straight @from @into @(T'TT'I t (L l tt)) @(TT'T'I t tt)
 `compose` wrap @into @(T'TT'I t (L l tt) _)
 `compose` yoneda @Straight @from x
 `compose` wrap

yokl_ = yokl
yokl__ = yokl
yokl___ = yokl
yokl____ = yokl
yokl_____ = yokl

li'yokl = yokl

yiok :: forall from into tt t i a o .
 Component Natural from into (T'TT'I (U_I_II t i) tt) (U_I_II t i) =>
 Covariant Yoneda from into (U_I_II t i) =>
 Castable Opposite into (U_I_II from a (tt o)) =>
 Castable Straight into (U_I_II t i o) =>
 Castable Opposite into (T'TT'I (U_I_II t i) tt o) =>
 t i a -> into (from a (tt o)) (t i o)
yiok x = unwrap @into @(U_I_II t i o)
 `compose` component @Straight @from @into @(T'TT'I (U_I_II t i) tt)
 `compose` wrap @into @(T'TT'I (U_I_II t i) tt _)
 `compose` yoneda @Straight @from (U_I_II x)
 `compose` wrap

-- TODO: yok'yo
-- TODO: yok'he'yo

-- yok'yokl, yok_'yokl, yok__'yokl, yok___'yokl, yok____'yokl, yok_____'yokl, yok______'yokl, li'yok'yokl
 -- :: forall from into t tt ttt label a o .
 -- Covariant Yoneda from into t =>
 -- Covariant Endo Semi Functor into t =>
 -- Covariant Endo Semi Functor into tt =>
 -- Covariant Endo Semi Functor from ttt =>
 -- Contravariant Endo Semi Functor (->) (U_II_I into (t (ttt o))) =>
 -- Component Natural into into (T'TT'I t (Labeled label tt)) t =>
 -- Component Natural from from (T'TT'I ttt (Labeled label tt)) (TT'T'I ttt (Labeled label tt)) =>
 -- Castable Opposite into (U_I_II from (ttt a) (Labeled label tt (ttt o))) =>
 -- (forall e . Wrapper into (T'TT'I t (Labeled label tt) e)) =>
 -- (forall e . Wrapper from (T'TT'I ttt (Labeled label tt) e)) =>
 -- (forall e . Wrapper from (TT'T'I ttt (Labeled label tt) e)) =>
 -- t (ttt a) -> into (from a (Labeled label tt o)) (t (ttt o))
-- yok'yokl x = fai fokl (yok @from @into x)

-- yok_'yokl = yok'yokl
-- yok__'yokl = yok'yokl
-- yok___'yokl = yok'yokl
-- yok____'yokl = yok'yokl
-- yok_____'yokl = yok'yokl
-- yok______'yokl = yok'yokl

-- li'yok'yokl = yok'yokl

-- yokl'yok :: forall from into t tt ttt l a o .
 -- Covariant Yoneda from into t =>
 -- Covariant Endo Semi Functor from tt =>
 -- Covariant Endo Semi Functor from ttt =>
 -- Contravariant Endo Semi Functor (->) (U_II_I into (ttt (t o))) =>
 -- Component Natural from from (T'TT'I ttt tt) ttt =>
 -- Component Natural from into (T'TT'I t ttt) (TT'T'I t ttt) =>
 -- Castable Opposite into (U_I_II from (ttt a) (ttt o)) =>
 -- Castable Straight into (TT'T'I t ttt o) =>
 -- Castable Opposite into (T'TT'I t ttt o) =>
 -- Castable Opposite from (T'TT'I ttt tt o) =>
 -- t (ttt a) -> into (from a (L l tt o)) (ttt (t o))
-- yokl'yok x = fai fok (yokl @from @into x)

-- yokl'yokl :: forall from into t tt ttt a o .
 -- Covariant Yoneda from into t =>
 -- Covariant Endo Semi Functor from tt =>
 -- Covariant Endo Semi Functor from ttt =>
 -- Component Natural from into (T'TT'I t ttt) (TT'T'I t ttt) =>
 -- Component Natural from from (T'TT'I tt ttt) (TT'T'I tt ttt) =>
 -- Contravariant Endo Semi Functor (->) (U_II_I into (ttt (t (tt o)))) =>
 -- Castable Opposite from (T'TT'I tt ttt o) =>
 -- Castable Straight from (TT'T'I tt ttt o) =>
 -- Castable Straight into (TT'T'I t ttt (tt o)) =>
 -- Castable Opposite into (T'TT'I t ttt (tt o)) =>
 -- Castable Opposite into (Straight from (tt a) (ttt (tt o))) =>
 -- t (tt a) -> into (from a (ttt o)) (ttt (t (tt o)))
-- yokl'yokl x = fai fokl (yokl @from @into x)

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

fioi :: forall from into t a o i i_ .
 Covariant Semi Functor from into (W_III_I_II t i_ i) =>
 Wrapper into (W_III_I_II t i_ i a) =>
 Wrapper into (W_III_I_II t i_ i o) =>
 from a o -> into (t i a i_) (t i o i_)
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
fai_ = fai `compose` fai @from unwrap

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

fui :: forall from into t a o e .
 Covariant Functor from into (U_II_I t e) =>
 Mapping Straight Straight from (->) Identity (U_I_II from a) =>
 Wrapper into (U_II_I t e a) =>
 Wrapper into (U_II_I t e o) =>
 Wrapper into (Identity o) =>
 o -> into (t a e) (t o e)
fui from = unwrap `compose` fu @from @into @(U_II_I _ _) from `compose` wrap

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

ho, ho_, ho__, ho___, ho____, ho_____, ho______, ho_______, ho________, yi'ho :: forall from into u i a o .
 Precategory into =>
 Covariant Yoneda from into (U_I_II u i) =>
 Castable Straight into (U_I_II u i o) =>
 Castable Opposite into (U_I_II from a o) =>
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

ho_'he'he = ho'he'he
ho__'he'he = ho'he'he
ho___'he'he = ho'he'he
ho____'he'he = ho'he'he
ho_____'he'he = ho'he'he
ho______'he'he = ho'he'he
ho_______'he'he = ho'he'he
ho________'he'he = ho'he'he

ho'he'he'he, ho_'he'he'he, ho__'he'he'he, ho___'he'he'he, ho____'he'he'he, ho_____'he'he'he, ho______'he'he'he, ho_______'he'he'he, ho________'he'he'he
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
 Covariant Yoneda from into (U_I_II u i) =>
 Contravariant Semi Functor from into (U_II_I from o) =>
 Covariant Semi Functor from into (U_I_II from o) =>
 Wrapper from a =>
 Wrapper from (Supertype a) =>
 Wrapper from (Supertype (Supertype a)) =>
 Wrapper from (Supertype (Supertype (Supertype a))) =>
 Wrapper into (U_I_II u i o) =>
 Wrapper into (U_I_II from a o) =>
 Wrapper into (U_II_I from o a) =>
 Wrapper into (U_II_I from o (Supertype a)) =>
 Wrapper into (U_II_I from o (Supertype (Supertype a))) =>
 Wrapper into (U_II_I from o (Supertype (Supertype (Supertype a)))) =>
 Wrapper into (U_II_I from o (Supertype (Supertype (Supertype (Supertype a))))) =>
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

ho'ho, ho_'ho :: forall from u u_ o e e_ a .
 Covariant Yoneda u from (Straight u e) =>
 Contravariant Yoneda (->) (->) (Opposite u e) =>
 Covariant Semi Functor from u (Straight u_ e_) =>
 Covariant Endo Semi Functor (->) (Straight (->) (u e (u_ a e_))) =>
 Contravariant Semi Functor (->) (->) (Opposite from (u e (u_ e_ o))) =>
 Wrapper u (Straight u_ e_ a) =>
 Wrapper u (Straight u_ e_ o) =>
 Wrapper from (Straight u_ e_ o) =>
 Wrapper from (Straight u e (u_ e_ o)) =>
 Wrapper from (Straight u (u_ e_ a) (u_ e_ o)) =>
 u e (u_ e_ a) -> from (from a o) (u e (u_ e_ o))
ho'ho x = fai fio (ho @u x)

ho_'ho = ho'ho

ho'ho'hu :: forall from u u_ u__ o e e_ e__ a .
 Category from =>
 Covariant Yoneda u__ (->) (U_I_II u e) =>
 Covariant Semi Functor from u__ (U_I_II u_ e_) =>
 Covariant Endo Semi Functor from (U_I_II u__ e__) =>
 Constant Endo Semi Functor from (U_I_II u__ e__) =>
 Mapping Straight Straight from (->) Identity (U_I_II from a) =>
 Wrapper u__ (U_I_II u_ e_ (u__ e__ a)) =>
 Wrapper u__ (U_I_II u_ e_ (u__ e__ o)) =>
 Wrapper from (U_I_II u__ e__ o) =>
 Wrapper from (U_I_II u__ e__ a) =>
 Wrapper from (Identity o) =>
 Wrapper (->) (U_1_I from a o) =>
 u e (u_ e_ (u__ e__ a)) -> o -> u e (u_ e_ (u__ e__ o))
ho'ho'hu = fai (fio @from `compose` fiu @from) `compose` ho @u__

ho'hu :: forall from u u_ o e e_ a .
 Category from =>
 Covariant Yoneda u from (U_I_II u e) =>
 Contravariant Yoneda (->) (->) (Opposite u e) =>
 Covariant Semi Functor from u (U_I_II u_ e_) =>
 Covariant Endo Semi Functor (->) (Straight (->) (u e (u_ a e_))) =>
 Contravariant Semi Functor (->) (->) (Opposite from (u e (u_ e_ o))) =>
 Mapping Straight Straight from (->) Identity (U_I_II from a) =>
 Wrapper u (Straight u_ e_ a) =>
 Wrapper u (Straight u_ e_ o) =>
 Wrapper from (Straight u_ e_ o) =>
 Wrapper from (Straight u e (u_ e_ o)) =>
 Wrapper from (Straight u (u_ e_ a) (u_ e_ o)) =>
 Wrapper u (Identity o) =>
 u e (u_ e_ a) -> from o (u e (u_ e_ o))
ho'hu = fai (fiu @from) `compose` ho @u

ho'ha, ho_'ha, ho__'ha, ho___'ha, ho____'ha, ho_____'ha, ho______'ha, ho_______'ha, ho________'ha
 :: forall from u u_ o e e_ a .
 Covariant Yoneda u (->) (Straight u e) =>
 Contravariant Yoneda u (->) (Opposite u e) =>
 Contravariant Semi Functor from u (Opposite u_ e_) =>
 Contravariant Endo Semi Functor (->) (Opposite (->) (u e (u_ a e_))) =>
 Wrapper u (U_II_I u_ e_ a) =>
 Wrapper u (U_II_I u_ e_ o) =>
 Wrapper from (U_I_II u e (u_ a e_)) =>
 Wrapper from (U_I_II u (u_ o e_) (u_ a e_)) =>
 u e (u_ o e_) -> from a o -> u e (u_ a e_)
ho'ha x = fai @(->) @(->) fai (ho @u x)

ho_'ha = ho'ha
ho__'ha = ho'ha
ho___'ha = ho'ha
ho____'ha = ho'ha
ho_____'ha = ho'ha
ho______'ha = ho'ha
ho_______'ha = ho'ha
ho________'ha = ho'ha

ho'ha'he, ho_'ha'he, ho__'ha'he, ho___'ha'he, ho____'ha'he, ho_____'ha'he, ho______'ha'he, ho_______'ha'he, ho________'ha'he
 :: forall from u u_ o e e_ a .
 Covariant Yoneda u (->) (Straight u e) =>
 Contravariant Semi Functor from u (Opposite u_ e_) =>
 Wrapper u (U_II_I u_ e_ a) =>
 Wrapper u (U_II_I u_ e_ (Supertype a)) =>
 Wrapper u (U_II_I u_ e_ o) =>
 Wrapper from a =>
 u e (u_ o e_) -> from (Supertype a) o -> u e (u_ a e_)
ho'ha'he x = fai (fai `compose` fai @from unwrap) (ho @u x)

ho_'ha'he = ho'ha'he
ho__'ha'he = ho'ha'he
ho___'ha'he = ho'ha'he
ho____'ha'he = ho'ha'he
ho_____'ha'he = ho'ha'he
ho______'ha'he = ho'ha'he
ho_______'ha'he = ho'ha'he
ho________'ha'he = ho'ha'he

ho'ha'he'he, ho_'ha'he'he, ho__'ha'he'he, ho___'ha'he'he, ho____'ha'he'he, ho_____'ha'he'he, ho______'ha'he'he, ho_______'ha'he'he, ho________'ha'he'he
 :: forall from u u_ o e e_ a .
 Covariant Yoneda u (->) (Straight u e) =>
 Contravariant Semi Functor from u (Opposite u_ e_) =>
 Wrapper u (U_II_I u_ e_ a) =>
 Wrapper u (U_II_I u_ e_ (Supertype a)) =>
 Wrapper u (U_II_I u_ e_ o) =>
 Wrapper from a =>
 Wrapper from (Supertype a) =>
 u e (u_ o e_) -> from (Supertype (Supertype a)) o -> u e (u_ a e_)
ho'ha'he'he x = fai (fai `compose` fai @from he'he) (ho @u x)

ho_'ha'he'he = ho'ha'he'he
ho__'ha'he'he = ho'ha'he'he
ho___'ha'he'he = ho'ha'he'he
ho____'ha'he'he = ho'ha'he'he
ho_____'ha'he'he = ho'ha'he'he
ho______'ha'he'he = ho'ha'he'he
ho_______'ha'he'he = ho'ha'he'he
ho________'ha'he'he = ho'ha'he'he

ho'yo, ho_'yo, ho__'yo, ho___'yo, ho____'yo, ho_____'yo :: forall from u t o e a .
 Covariant Yoneda from (->) (Straight u e) =>
 Contravariant Yoneda from (->) (Opposite u e) =>
 Covariant Endo Semi Functor from t =>
 Constant Semi Functor from (->) t =>
 u e (t a) -> from a o -> u e (t o)
ho'yo x = fai (fo @from) (ho @from x)

ho_'yo = ho'yo
ho__'yo = ho'yo
ho___'yo = ho'yo
ho____'yo = ho'yo
ho_____'yo = ho'yo

ho'yu, ho_'yu, ho__'yu, ho___'yu, ho____'yu, ho_____'yu, ho______'yu, ho_______'yu, ho________'yu
 :: forall u t o e a .
 Covariant Yoneda (->) (->) (Straight u e) =>
 Contravariant Yoneda (->) (->) (Opposite u e) =>
 Mapping Straight Straight (->) (->) Identity (U_I_II (->) a) =>
 Covariant Endo Semi Functor (->) t =>
 Constant Semi Functor (->) (->) t =>
 u e (t a) -> o -> u e (t o)
ho'yu x = fai @(->) @(->) (fu @(->)) (ho @(->) x)

ho_'yu = ho'yu
ho__'yu = ho'yu
ho___'yu = ho'yu
ho____'yu = ho'yu
ho_____'yu = ho'yu
ho______'yu = ho'yu
ho_______'yu = ho'yu
ho________'yu = ho'yu

ho'yui, ho_'yui, ho__'yui, ho___'yui, ho____'yui, ho_____'yui, ho______'yui, ho_______'yui, ho________'yui
 :: forall u t o e a .
 Covariant Yoneda (->) (->) (Straight u e) =>
 Contravariant Yoneda (->) (->) (Opposite u e) =>
 Mapping Straight Straight (->) (->) Identity (U_I_II (->) a) =>
 Covariant Endo Semi Functor (->) (U_II_I t e) =>
 Constant Semi Functor (->) (->) (U_II_I t e) =>
 u e (t a e) -> o -> u e (t o e)
ho'yui x = fai @(->) @(->) (fui @(->)) (ho @(->) x)

ho_'yui = ho'yui
ho__'yui = ho'yui
ho___'yui = ho'yui
ho____'yui = ho'yui
ho_____'yui = ho'yui
ho______'yui = ho'yui
ho_______'yui = ho'yui
ho________'yui = ho'yui

ho'yioi :: forall from u t o e e_ e__ a .
 Covariant Yoneda from (->) (Straight u e) =>
 Contravariant Yoneda from (->) (Opposite u e) =>
 Covariant Endo Semi Functor from (W_III_I_II t e__ e_) =>
 Wrapper from (W_III_I_II t e__ e_ a) =>
 Wrapper from (W_III_I_II t e__ e_ o) =>
 u e (t e_ a e__) -> from a o -> u e (t e_ o e__)
ho'yioi x = fai (fioi @from) (ho @from x)

he'ho, he_'ho, he__'ho, he___'ho, he____'ho, he_____'ho, he______'ho, he_______'ho, he________'ho
 :: forall from into u i a o .
 Covariant Yoneda from into (U_I_II u (Supertype i)) =>
 Contravariant Semi Functor into into (U_II_I u o) =>
 Wrapper into i =>
 Wrapper into (U_I_II from a o) =>
 Wrapper into (U_II_I u o i) =>
 Wrapper into (U_II_I u o (Supertype i)) =>
 Wrapper into (U_I_II u (Supertype i) o) =>
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
 Covariant Yoneda from into (U_I_II u (Supertype i)) =>
 Contravariant Semi Functor from into (U_II_I u o) =>
 Contravariant Semi Functor from into (U_II_I from o) =>
 Wrapper from a =>
 Wrapper from i =>
 Wrapper into (U_I_II from a o) =>
 Wrapper into (U_II_I from o a) =>
 Wrapper into (U_II_I u o i) =>
 Wrapper into (U_II_I u o (Supertype i)) =>
 Wrapper into (U_II_I from o (Supertype a)) =>
 Wrapper into (U_I_II u (Supertype i) o) =>
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

ha, ha_, ha__, ha___, ha____, ha_____, ha______, ha_______, ha________ :: forall from u e a o .
 Contravariant Yoneda from (->) (U_II_I u e) =>
 u a e -> from o a -> u o e
ha x = yai @from @(->) @u x

ha_ = ha
ha__ = ha
ha___ = ha
ha____ = ha
ha_____ = ha
ha______ = ha
ha_______ = ha
ha________ = ha

ha'he, ha_'he, ha__'he, ha___'he, ha____'he, ha_____'he, ha______'he, ha_______'he, ha________'he :: forall from u e a o .
 Contravariant Yoneda from (->) (U_II_I u e) =>
 Wrapper from o =>
 u a e -> from (Supertype o) a -> u o e
ha'he x = yai @from @(->) @u x `compose` fai (he @from)

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
 Contravariant Yoneda from into (U_II_I u e) =>
 Contravariant Semi Functor from into (U_II_I from a) =>
 Wrapper from o =>
 Wrapper into (U_II_I from a o) =>
 Wrapper into (U_II_I u e o) =>
 Wrapper into (U_II_I from a (Supertype (Supertype o))) =>
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

ha'ha :: forall from u u_ a o e e_ .
 Contravariant Yoneda u (->) (Opposite u e) =>
 Contravariant Semi Functor from u (Opposite u_ e_) =>
 Wrapper u (Opposite u_ e_ a) =>
 Wrapper u (Opposite u_ e_ o) =>
 u (u_ a e_) e -> from a o -> u (u_ o e_) e
ha'ha x = fai @(->) @(->) fai (ha @u x)

hv :: forall from into a o e .
 Category into =>
 Terminal into =>
 Contravariant Yoneda into (->) (U_II_I into o) =>
 into () o -> into e a -> into e o
hv x = ha (x `compose` terminal)

ha_ha :: forall from u u_ a o e e_ .
 Contravariant Yoneda u (->) (Opposite u e) =>
 Contravariant Semi Functor from u (Opposite u_ e_) =>
 Contravariant Semi Functor u u (Opposite u_ e_) =>
 Wrapper u (Opposite u_ e_ (Supertype a)) =>
 Wrapper u (Opposite u_ e_ o) =>
 Wrapper u (Opposite u_ e_ a) =>
 Wrapper u a =>
 Wrapper from a =>
 u (u_ a e_) e -> from (Supertype a) o -> u (u_ o e_) e
ha_ha x = fai @(->) @(->) fai_ (ha @u x)

ha'ho :: forall from u u_ o e e_ a .
 Covariant Yoneda u (->) (Straight u e) =>
 Contravariant Yoneda u (->) (Opposite u e) =>
 Covariant Semi Functor from u (U_I_II u_ e_) =>
 Wrapper u (U_I_II u_ e_ a) =>
 Wrapper u (U_I_II u_ e_ o) =>
 u (u_ e_ o) e -> from a o -> u (u_ e_ a) e
ha'ho x = fai @(->) @(->) fio (ha @u x)

-- ha'ho'hu :: forall from into u u_ u__ o e e_ e__ a .
 -- Precategory from =>
 -- Contravariant Yoneda u__ (->) (U_II_I u e) =>
 -- Covariant Semi Functor from u__ (U_I_II u_ e_) =>
 -- Covariant Endo Semi Functor from (U_I_II u__ e__) =>
 -- Mapping Straight Straight into into Identity (U_I_II into a) =>
 -- Wrapper u__ (U_I_II u_ e_ (u__ e__ a)) =>
 -- Wrapper u__ (U_I_II u_ e_ (u__ e__ o)) =>
 -- Wrapper from (U_I_II u__ e__ o) =>
 -- Wrapper from (U_I_II u__ e__ a) =>
 -- Wrapper (->) (U_1_I from a o) =>
 -- u (u_ e_ (u__ e__ o)) e -> Supertype (U_1_I from a o) -> u (u_ e_ (u__ e__ a)) e
-- ha'ho'hu = fai (fio @from `compose` fiu) `compose` ha @u__

-- ha'hu :: forall from u u_ o e e_ a .
 -- Covariant Semi Functor u u (U_I_II u_ e_) =>
 -- Constant Semi Functor u u (U_I_II u_ e_) =>
 -- Contravariant Yoneda u (->) (Opposite u e) =>
 -- Wrapper u (U_I_II u_ e_ a) =>
 -- Wrapper u (U_I_II u_ e_ o) =>
 -- Castable Opposite u (U_1_I u a o) =>
 -- Castable Opposite (->) (U_1_I u a o) =>
 -- u (u_ e_ o) e -> Supertype (U_1_I u a o) -> u (u_ e_ a) e
-- ha'hu x = fai @(->) @(->) fiu (ha @u x)

-- ha'he'hu :: forall from u u_ o e e_ a .
 -- Covariant Semi Functor u u (U_I_II u_ e_) =>
 -- Constant Semi Functor u u (U_I_II u_ e_) (U_I_II u_ e_) =>
 -- Contravariant Yoneda u (->) (Opposite u e) =>
 -- Wrapper u (U_I_II u_ e_ a) =>
 -- Wrapper u (U_I_II u_ e_ o) =>
 -- Castable Opposite (->) (u () o) =>
 -- u (u_ e_ o) e -> Supertype (u () o) -> u (u_ e_ a) e
-- ha'he'hu x = fai @(->) @(->) fiu (ha'he @u x)

-- ha'hu'he :: forall from u u_ o e e_ a .
--  Covariant Semi Functor u u (U_I_II u_ e_) =>
--  Constant Semi Functor u u (U_I_II u_ e_) =>
--  Contravariant Yoneda u (->) (Opposite u e) =>
--  Wrapper u (U_I_II u_ e_ a) =>
--  Wrapper u (U_I_II u_ e_ o) =>
--  Castable Opposite (->) (Supertype (u () o)) =>
--  Castable Opposite (->) (u () o) =>
--  u (u_ e_ o) e -> Supertype (Supertype (u () o)) -> u (u_ e_ a) e
-- ha'hu'he x = fai @(->) @(->) fiu'_ (ha @u x)

ha'yo :: forall from u t o e a .
 Covariant Yoneda from (->) (Straight u e) =>
 Contravariant Yoneda from (->) (Opposite u e) =>
 Covariant Endo Semi Functor from t =>
 Constant Semi Functor from (->) t =>
 u (t a) e -> from o a -> u (t o) e
ha'yo x = fai (fo @from) (ha @from x)

ha'yioi :: forall from u t o e e_ e__ a .
 Covariant Yoneda from (->) (Straight u e) =>
 Contravariant Yoneda from (->) (Opposite u e) =>
 Covariant Endo Semi Functor from (W_III_I_II t e__ e_) =>
 Wrapper from (W_III_I_II t e__ e_ a) =>
 Wrapper from (W_III_I_II t e__ e_ o) =>
 u (t e_ a e__) e -> from o a -> u (t e_ o e__) e
ha'yioi x = fai (fioi @from) (ha @from x)

-- -- TODO: replace with `ho_`
-- ho_yi :: forall from u e a o .
--  Covariant Endo Semi Functor from (U_I_II from a) =>
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
--  Covariant Yoneda from (->) (U_I_II u e) =>
--  Castable Straight from a =>
--  u e a -> from (Supertype a) o -> u e o
-- ho_yi'ho x xx = x `ho` he @from `ho` xx

hu, hu_, hu__, hu___, hu____, hu_____, hu______, hu_______, hu________ ::
 forall into t i a o .
 Covariant Yoneda into into (U_I_II t i) =>
 Mapping Straight Straight into into Identity (U_I_II into a) =>
 Wrapper into (U_I_II into a o) =>
 Wrapper into (U_I_II t i o) =>
 Wrapper into (Identity o) =>
 t i a -> into o (t i o)
hu = yiu

hu_ = hu
hu__ = hu
hu___ = hu
hu____ = hu
hu_____ = hu
hu______ = hu
hu_______ = hu
hu________ = hu

-- hu'he, hu_'he, hu__'he, hu___'he, hu____'he, hu_____'he, hu______'he, hu_______'he, hu________'he
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
 Castable Straight into (Straight hom (Representation t) i) =>
 into (t i) (hom (Representation t) i)
ro = he `compose` map @Straight @Straight @into @into @t @(Straight hom (Representation t)) identity

ra :: forall into hom t i .
 Category into =>
 Contravariant (Representable hom) into into t =>
 Castable Straight into (Opposite hom (Representation t) i) =>
 into (t i) (hom i (Representation t))
ra = he `compose` map @Opposite @Straight @into @into @t @(Opposite hom (Representation t)) identity

fd :: forall from into t tt a o .
 Adjoint Functor from into t tt =>
 Castable Opposite from ((T'TT'I t tt) o) =>
 Castable Straight from (Identity o) =>
 into a (tt o) -> from (t a) o
fd from = unwrap @from @(Identity _)
 `compose` component @Straight @into @from @(t `T'TT'I` tt) @Identity
 `compose` wrap @from @((t `T'TT'I` tt) _)
 `compose` fo @into @from from

fj :: forall from into t tt a o .
 Adjoint Functor from into t tt =>
 Castable Straight into (T'TT'I tt t a) =>
 Castable Opposite into (Identity a) =>
 from (t a) o -> into a (tt o)
fj from = fo from
 `compose` unwrap @into
 `compose` component @Straight @from @into @Identity @(tt `T'TT'I` t)
 `compose` wrap @into

-- ilj :: forall from into t tt e e_ a o .
 -- Adjoint Functor from into (U_I_II t e) (U_I_II tt e_) =>
 -- Castable Straight into ((T'TT'I (U_I_II tt e_) (U_I_II t e)) a) =>
 -- Castable Straight into (U_I_II tt e_ o) =>
 -- Castable Opposite into (Identity a) =>
 -- Castable Straight from (U_I_II t e a) =>
 -- from (t e a) o -> into a (tt e_ o)
-- ilj from = he @into @(U_I_II tt _ _)
 -- `compose` fo (from `compose` he @from @(U_I_II t _ _))
 -- `compose` he @into @(T'TT'I _ _ _)
 -- `compose` component @Straight @from @into @Identity @(U_I_II tt e_ `T'TT'I` U_I_II t e)
 -- `compose` wrap @into

hd :: forall from into t tt e a o .
 Adjoint Functor from into (U_II_I t e) (U_I_II tt e) =>
 Castable Straight into ((U_I_II tt e `T'TT'I` U_II_I t e) a) =>
 Castable Straight into (U_I_II tt e o) =>
 Castable Opposite into (Identity a) =>
 Castable Straight from (U_II_I t e a) =>
 from (t a e) o -> into a (tt e o)
hd from = he @into @(U_I_II tt _ _)
 `compose` fo (from `compose` he @from @(U_II_I t _ _))
 `compose` he @into @(T'TT'I _ _ _)
 `compose` component @Straight @from @into @Identity @(U_I_II tt e `T'TT'I` U_II_I t e)
 `compose` wrap @into

hd'q :: forall into a .
 Adjoint Functor into into (U_II_I LM a) (U_I_II into a) =>
 Castable Straight into ((U_I_II into a `T'TT'I` U_II_I LM a) a) =>
 Castable Straight into (U_I_II into a (a `LM` a `ML` a)) =>
 Castable Straight into (U_II_I LM a a) =>
 Castable Opposite into (Identity a) =>
 Setoid into a =>
 into a (into a (a `LM` a `ML` a))
hd'q = hd (q @into)

hj, hj_, hj__, hj___, hj____, hj_____, hj______, hj_______, hj________ :: forall from into t tt e a o .
 Adjoint Functor from into (U_II_I t e) (U_I_II tt e) =>
 Castable Opposite from ((T'TT'I (U_II_I t e) (U_I_II tt e)) o) =>
 Castable Straight from (Identity o) =>
 Castable Opposite from (U_II_I t e a) =>
 Castable Opposite into (U_I_II tt e o) =>
 into a (tt e o) -> from (t a e) o
hj from = he @from
 `compose` component @Straight @into @from @(U_II_I t e `T'TT'I` U_I_II tt e) @Identity
 `compose` wrap @from @((U_II_I t e `T'TT'I` U_I_II tt e) _)
 `compose` fo (wrap @into @(U_I_II tt e _) `compose` from)
 `compose` wrap @from @(U_II_I t e _)

hj_ = hj
hj__ = hj
hj___ = hj
hj____ = hj
hj_____ = hj
hj______ = hj
hj_______ = hj
hj________ = hj

hj'hj :: forall from into t tt ttt tttt e e_ a o .
 Adjoint Functor from from (U_II_I t e_) (U_I_II tttt e_) =>
 Adjoint Functor from into (U_II_I ttt e) (U_I_II tt e) =>
 Castable Opposite from (U_II_I t e_ a) =>
 Castable Opposite into (U_I_II tt e o) =>
 Castable Opposite into (U_I_II tt e (tttt e_ o)) =>
 Castable Straight from (Identity o) =>
 Castable Straight from (Identity (tttt e_ o)) =>
 Castable Opposite from (Identity (U_I_II tttt e_ o)) =>
 Castable Opposite from (U_II_I ttt e a) =>
 Castable Opposite from (U_I_II tttt e_ o) =>
 Castable Opposite from (U_II_I t e_ (ttt a e)) =>
 Castable Opposite from ((T'TT'I (U_II_I ttt e) (U_I_II tt e)) (tttt e_ o)) =>
 Castable Opposite from ((T'TT'I (U_II_I t e_) (U_I_II tttt e_)) o) =>
 into a (tt e (tttt e_ o)) -> from (t (ttt a e) e_) o
hj'hj = hj @from @from `compose` hj @from @into

he, he_, he__, he___, he____, he_____, he______, he_______, he________ :: forall into e .
 Castable Straight into e =>
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
 Castable Straight into e =>
 Castable Straight into (Supertype e) =>
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

he'he'he, he_'he'he, he__'he'he, he___'he'he, he____'he'he, he_____'he'he, he______'he'he, he_______'he'he, he________'he'he :: forall into e .
 Precategory into =>
 Castable Straight into e =>
 Castable Straight into (Supertype e) =>
 Castable Straight into (Supertype (Supertype e)) =>
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
 Castable Straight into e =>
 Castable Straight into (Supertype e) =>
 Castable Straight into (Supertype (Supertype e)) =>
 Castable Straight into (Supertype (Supertype (Supertype e))) =>
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

-- TODO: define `j'__'__'`, `j'__'__'__'`, `j'__'__'__'__',

lo, lo_, lo__, lo___, lo____, lo_____, lo______, lo_______ :: forall into a o o_ .
 Category into =>
 Limit Straight into into =>
 Covariant Endo Semi Functor into (U_I_II Product a) =>
 Covariant Endo Semi Functor into (U_II_I Product o_) =>
 (forall e e_ . Wrapper into (U_I_II Product e e_)) =>
 (forall e e_ . Wrapper into (U_II_I Product e e_)) =>
 (forall e . Wrapper into (Both Product e)) =>
 (forall e . Wrapper into (Identity e)) =>
 into a o -> into a o_ -> into a (Product o o_)
lo l r = foi @into @into l `compose` fio @into @into r
 `compose` wrapped (map @Opposite @Opposite @into @into @(Both Product) @Identity identity)

lo_ = lo
lo__ = lo
lo___ = lo
lo____ = lo
lo_____ = lo
lo______ = lo
lo_______ = lo

lo'yp, lo_'yp, lo__'yp, lo___'yp, lo____'yp, lo_____'yp, lo______'yp, lo_______'yp
 :: forall t a o o_ .
 Covariant Monoidal Functor (->) LM LM t =>
 Arrow a (t o) -> Arrow a (t o_) -> Arrow a (t (Product o o_))
lo'yp from__eft from_right = yp `compose` lo from__eft from_right

lo_'yp = lo'yp
lo__'yp = lo'yp
lo___'yp = lo'yp
lo____'yp = lo'yp
lo_____'yp = lo'yp
lo______'yp = lo'yp
lo_______'yp = lo'yp

lo'ys, lo_'ys, lo__'ys, lo___'ys, lo____'ys, lo_____'ys, lo______'ys, lo_______'ys
 :: forall t a o o_ .
 Covariant Monoidal Functor (->) LM ML t =>
 Arrow a (t o) -> Arrow a (t o_) -> Arrow a (t (Sum o o_))
lo'ys from__eft from_right = ys `compose` lo from__eft from_right

lo_'ys = lo'ys
lo__'ys = lo'ys
lo___'ys = lo'ys
lo____'ys = lo'ys
lo_____'ys = lo'ys
lo______'ys = lo'ys
lo_______'ys = lo'ys

lo'ys'la, lo_'ys'la, lo__'ys'la, lo___'ys'la, lo____'ys'la, lo_____'ys'la, lo______'ys'la, lo_______'ys'la
 :: forall t a o__ .
 Covariant Monoidal Functor (->) LM ML t =>
 Arrow a (t o__) -> Arrow a (t o__) -> Arrow a (t o__)
lo'ys'la from__eft from_right = (\x -> ys'yo x (identity @AR `la` identity)) `compose` lo from__eft from_right

lo_'ys'la = lo'ys'la
lo__'ys'la = lo'ys'la
lo___'ys'la = lo'ys'la
lo____'ys'la = lo'ys'la
lo_____'ys'la = lo'ys'la
lo______'ys'la = lo'ys'la
lo_______'ys'la = lo'ys'la

-- lo'yip'yp, lo_'yip'yp, lo__'yip'yp, lo___'yip'yp, lo____'yip'yp, lo_____'yip'yp, lo______'yip'yp, lo_______'yip'yp
 -- :: forall t a o o_ .
 -- Covariant Monoidal Functor (->) LM LM t =>
 -- Arrow a (t o) -> Arrow a (t o_) -> Arrow a (t (Product o o_))
-- lo'yp from__eft from_right = yp `compose` lo from__eft from_right

-- lo_'yip'yp = lo'yp
-- lo__'yip'yp = lo'yp
-- lo___'yip'yp = lo'yp
-- lo____'yip'yp = lo'yp
-- lo_____'yip'yp = lo'yp
-- lo______'yip'yp = lo'yp
-- lo_______'yip'yp = lo'yp

cn :: forall into a a_ o o_ .
 Cone Straight into into Product =>
 Functor Straight into into (U_I_II Product o) =>
 Functor Straight into into (U_I_II Product a_) =>
 Functor Straight into into (U_II_I Product a_) =>
 Wrapper into (U_I_II Product o a_) =>
 Wrapper into (U_I_II Product o o_) =>
 Wrapper into (U_II_I Product a_ o) =>
 Wrapper into (U_II_I Product a_ a) =>
 into a o -> into a_ o_ -> into (Product a a_) (Product o o_)
cn from__eft from_right = fio from_right `compose` foi from__eft

-- into a o -> into a o_ -> into a (Product into o o_)

-- cnz :: forall into e a a_ o o_ .
 -- Cone Straight into into (Object Straight into) =>
 -- Functor Straight into into (U_I_II (Product into) o) =>
 -- Functor Straight into into (U_I_II (Product into) a_) =>
 -- Functor Straight into into (U_II_I (Product into) a_) =>
 -- Wrapper into (U_I_II (Product into) o a_) =>
 -- Wrapper into (U_I_II (Product into) o o_) =>
 -- Wrapper into (U_II_I (Product into) a_ o) =>
 -- Wrapper into (U_II_I (Product into) a_ a) =>
 -- Castable Straight into e =>
 -- (Supertype e ~ (Product into a a_)) =>
 -- into a o -> into a_ o_ -> into e (Product into o o_)
-- cnz from__eft from_right = fio from_right `compose` foi from__eft `compose` _' @into

-- TODO: try to generalize
-- cn'yp, yi'cn'yp :: forall t a a_ o o_ .
 -- Mapping Straight Straight (->) (->) (Day Straight (->) (Product (->)) (Product (->)) t t o o_) t =>
 -- Arrow a (t o) -> Arrow a_ (t o_) -> Arrow (Product (->) a a_) (t (Product Arrow o o_))
-- cn'yp from__eft from_right = yp `compose` cn from__eft from_right

-- yi'cn'yp = cn'yp

-- TODO: try to generalize
-- cnz'yp, yi'cnz'yp :: forall e t a a_ o o_ .
--  Mapping Straight Straight (->) (->) (Day Straight (->) (Product (->)) (Product (->)) t t o o_) t =>
--  Castable Straight (->) e =>
--  (Supertype e ~ Product (->) a a_) =>
--  Arrow a (t o) -> Arrow a_ (t o_) -> Arrow e (t (Product Arrow o o_))
-- cnz'yp from__eft from_right = yp `compose` cn from__eft from_right `compose` he

-- yi'cnz'yp = cnz'yp

-- TODO: try to generalize
-- lu, lu_, lu__, lu___, lu____, lu_____, lu______, lu_______ :: forall o o_ .
--  Limit Straight (->) (->) =>
--  Covariant Functor (->) (->) (U_I_II (Product (->)) o) =>
--  Covariant Functor (->) (->) (U_II_I (Product (->)) (Product (->) () ())) =>
--  Castable Straight (->) (Both (Product (->)) (Product (->) () ())) =>
--  Castable Straight (->) (U_I_II (Product (->)) o o_) =>
--  Castable Opposite (->) (U_II_I (Product (->)) () ()) =>
--  Castable Opposite (->) (U_I_II (Product (->)) () ()) =>
--  Castable Straight (->) (Both (Product (->)) ()) =>
--  Castable Straight (->) (U_II_I (Product (->)) (Product (->) () ()) o) =>
--  Castable Opposite (->) (U_II_I (Product (->)) (Product (->) () ()) (Product (->) () ())) =>
--  Wrapper (->) (U_I_II (Product (->)) o (Product (->) () ())) =>
--  (forall e . Wrapper (->) (Identity e)) =>
--  Castable Opposite (->) (U_1_I (->) () o) =>
--  Castable Opposite (->) (U_1_I (->) () o_) =>
--  Castable Straight (->) (U_1_I (->) () (Product (->) o o_)) =>
--  Supertype (U_1_I (->) () o) ->
--  Supertype (U_1_I (->) () o_) ->
--  Supertype (U_1_I (->) () (Product (->) o o_))
-- lu from__eft from_right = -- he /
--  -- __ (map @Straight @Straight (wrapped (right @Straight (wrap @_ @(U_1_I (->) () o_) from_right)))) `compose`
--  -- i_ (map @Straight @Straight (wrapped (left @Straight (wrap @_ @(U_1_I (->) () o) from__eft)))) `compose`
--  -- wrapped (map @Straight @Straight @(->) @(->) @Identity @(Both (Product (->))) identity) `compose`
--  -- wrapped (map @Straight @Straight @(->) @(->) @Identity @(Both (Product (->))) identity)

--  __ (map @U_1_I @Straight (wrapped (right @Straight from_right))) `compose`
--  i_ (map @U_1_I @Straight (wrapped (left @Straight from__eft))) `compose`
 -- wrapped (map @U_1_I @Straight @(->) @(->) @Identity @(Both (Product (->))) identity) `compose`
 -- wrapped (map @U_1_I @Straight @(->) @(->) @Identity @(Both (Product (->))) identity)

lu, lu_, lu__, lu___, lu____, lu_____, lu______, lu_______ :: forall o o_ .
 Limit Straight (->) (->) =>
 Mapping Straight Straight (->) (->) Identity (U_I_I Product) =>
 Covariant Yoneda (->) (->) (U_I_II Product o) =>
 Covariant Yoneda (->) (->) (U_II_I Product ()) =>
 Wrapper (->) (U_I_I Product ()) =>
 Wrapper (->) (Identity ()) =>
 o -> o_ -> Product o o_
lu l r = wrapped (map @Straight @Straight @(->) @(->) @Identity @(U_I_I Product) identity) () `yui` l `yiu` r

lu_ = lu
lu__ = lu
lu___ = lu
lu____ = lu
lu_____ = lu
lu______ = lu
lu_______ = lu

-- ho'lu :: forall o o_ .
 -- Limit Straight (->) (->) =>
 -- Mapping Straight Straight (->) (->) Identity (U_I_I Product) =>
 -- Covariant Yoneda (->) (->) (U_I_II Product o) =>
 -- Covariant Yoneda (->) (->) (U_II_I Product ()) =>
 -- Wrapper (->) (U_I_I Product ()) =>
 -- Wrapper (->) (Identity ()) =>
 -- from e o -> from e o_ -> Product o o_
-- ho'lu l r = wrapped (map @Straight @Straight @(->) @(->) @Identity @(U_I_I Product) identity) () `yui` l `yiu` r

la, la_, la__, la___, la____, la_____, la______, la_______ :: forall from i a o o_ .
 Category from =>
 Limit Opposite from from =>
 Objective from (o `ML` o_) a =>
 Covariant Endo Semi Functor from (U_I_II Sum o) =>
 Covariant Endo Semi Functor from (U_II_I Sum i) =>
 (forall e_ e__ . Wrapper from (U_I_II Sum e_ e__)) =>
 (forall e_ e__ . Wrapper from (U_II_I Sum e_ e__)) =>
 (forall e_ . Wrapper from (U_I_I Sum e_)) =>
 (forall e_ . Wrapper from (Identity e_)) =>
 from o i -> from o_ i -> from a i
la l r = wrapped (map @Opposite @Opposite @from @from @Identity @(Both Sum) identity)
 `compose` foi @from @from l
 `compose` fio @from @from r
 `compose` objective @_ @(o `ML` o_)

la_ = la
la__ = la
la___ = la
la____ = la
la_____ = la
la______ = la
la_______ = la

-- `yp`: u (t e) (t e_) -> t (u_ e e_)
-- `hs`: from o i -> from o_ i -> from (o `ML` o_) i
-- `lo`: into a o -> into a o_ -> into a (o `LM` o_)
--     : u (from o i) (from o_ i) -> from (u_ o o_) i

-- TODO: to test
-- rwr'hs :: forall from into r o a a_ .
 -- Category from =>
 -- Limit Opposite from into =>
 -- Covariant Functor into into (U_I_II Sum a) =>
 -- Covariant Functor into into (U_II_I Sum (Sum (Supertype r) (Supertype r))) =>
 -- Castable Opposite into (Both Sum (Sum (Supertype r) (Supertype r))) =>
 -- Castable Opposite into (U_I_II Sum a a_) =>
 -- Castable Straight into (U_I_II Sum (Supertype r) (Supertype r)) =>
 -- Castable Straight into (U_II_I Sum (Supertype r) (Supertype r)) =>
 -- Castable Opposite into (Both Sum (Supertype r)) =>
 -- Castable Straight into (That Sum a (Sum (Supertype r) (Supertype r))) =>
 -- Castable Opposite into (U_II_I Sum (Sum (Supertype r) (Supertype r)) a) =>
 -- Castable Straight into (U_II_I Sum (Sum (Supertype r) (Supertype r)) (Sum (Supertype r) (Supertype r))) =>
 -- (Supertype o ~ Sum a a_) =>
 -- (forall e___ . Wrapper into (Identity e___)) =>
 -- Castable Opposite into r =>
 -- Castable Straight into o =>
 -- from a (Supertype r) -> from a_ (Supertype r) -> into o r
-- rwr'hs from__eft from_right = rwr /
 -- wrapped (map @Opposite @Opposite @from @into @Identity @(Both Sum) identity) `compose`
 -- wrapped (map @Opposite @Opposite @from @into @Identity @(Both Sum) identity) `compose`
 -- i_ (map @Straight @Straight (wrapped (left @Opposite from__eft))) `compose`
 -- __ (map @Straight @Straight (wrapped (right @Opposite from_right)))

-- TODO: try to generalize
yp :: forall u e e_ t .
 Covariant Monoidal Functor (->) u LM t =>
 u (t e) (t e_) -> t (e `LM` e_)
yp = day @Straight @(->) @t @u @LM identity identity

-- TODO: try to generalize
yp'yo, yp_'yo :: forall from e e_ r t .
 Covariant Monoidal Functor from LM LM t =>
 t e `LM` t e_ -> from (e `LM` e_) r -> t r
yp'yo x f = day @Straight @from @t @LM @LM identity f x

yp_'yo = yp'yo

-- TODO: try to generalize
yip :: forall u e e_ e__ t .
 Covariant Endo Semi Functor (->) (U_II_I u (t e e__)) =>
 Covariant Endo Semi Functor (->) (U_I_II u (U_I_II t e e_)) =>
 Covariant Monoidal Functor (->) u LM (U_I_II t e) =>
 u (t e e_) (t e e__) -> t e (e_ `LM` e__)
yip = unwrap @Arrow
 `compose` day @Straight @(->) @(U_I_II t e) @u @LM identity identity
 `compose` fio @Arrow wrap `compose` foi @Arrow wrap

-- TODO: try to generalize
yip'yo :: forall u e e_ e__ t r .
 Covariant Endo Semi Functor (->) (U_II_I u (t e e__)) =>
 Covariant Endo Semi Functor (->) (U_I_II u (U_I_II t e e_)) =>
 Covariant Monoidal Functor (->) u LM (U_I_II t e) =>
 u (t e e_) (t e e__) -> (->) (e_ `LM` e__) r -> t e r
yip'yo x f = unwrap @Arrow
 `compose` day @Straight @(->) @(U_I_II t e) @u @LM identity f
 `compose` fio @Arrow wrap `compose` foi @Arrow wrap
 `identity` x

-- TODO: try to generalize
yo'yp :: forall u e e_ t tt .
 Covariant Endo Semi Functor (->) t =>
 Covariant Monoidal Functor (->) u LM tt =>
 t (u (tt e) (tt e_)) -> t (tt (e `LM` e_))
yo'yp = fo (day @Straight @(->) @tt @u @LM identity identity)

-- TODO: try to generalize
yio'yp :: forall u e e_ e__ t tt .
 Covariant Endo Semi Functor (->) (U_I_II t e__) =>
 Covariant Monoidal Functor (->) u LM tt =>
 t e__ (u (tt e) (tt e_)) -> t e__ (tt (e `LM` e_))
yio'yp = fio (day @Straight @(->) @tt @u @LM identity identity)

-- TODO: try to generalize
ys :: forall u e e_ t .
 Covariant Monoidal Functor (->) u ML t =>
 u (t e) (t e_) -> t (e `ML` e_)
ys = day @Straight @(->) @t @u @ML identity identity

-- TODO: try to generalize
ys'yo :: forall from e e_ u r t .
 Covariant Monoidal Functor from u ML t =>
 u (t e) (t e_) -> from (e `ML` e_) r -> t r
ys'yo x f = day @Straight @from @t @u @ML identity f x

-- TODO: try to generalize
yis :: forall u e e_ e__ t .
 Covariant Endo Semi Functor (->) (U_II_I u (t e e__)) =>
 Covariant Endo Semi Functor (->) (U_I_II u (U_I_II t e e_)) =>
 Covariant Monoidal Functor (->) u ML (U_I_II t e) =>
 u (t e e_) (t e e__) -> t e (e_ `ML` e__)
yis = unwrap @Arrow
 `compose` day @Straight @(->) @(U_I_II t e) @u @ML identity identity
 `compose` fio @Arrow wrap `compose` foi @Arrow wrap

-- TODO: try to generalize
dw :: forall u e e_ t .
 Covariant Monoidal Functor (->) u MLM t =>
 u (t e) (t e_) -> t (ML e e_ `ML` LM e e_)
dw = day @Straight @(->) @t @u @MLM identity he

-- TODO: try to generalize
yp'yp :: forall u e e_ t tt .
 Covariant Monoidal Functor (->) u LM t =>
 Covariant Monoidal Functor (->) LM LM tt =>
 u (t (tt e)) (t (tt e_)) -> t (tt (e `LM` e_))
yp'yp = day @Straight @(->) @t @u @LM identity
 (day @Straight @(->) @tt @LM @LM identity identity)

-- TODO: try to generalize
yp'ys :: forall u e e_ t tt .
 Covariant Monoidal Functor (->) u LM t =>
 Covariant Monoidal Functor (->) LM ML tt =>
 u (t (tt e)) (t (tt e_)) -> t (tt (e `ML` e_))
yp'ys = day @Straight @(->) @t @u @LM identity
 (day @Straight @(->) @tt @LM @ML identity identity)

yip'yp :: forall u e e_ e__ t tt .
 Covariant Endo Semi Functor (->) (U_I_II t e) =>
 Covariant Endo Semi Functor (->) (U_I_II u (U_I_II t e (tt e_))) =>
 Covariant Endo Semi Functor (->) (U_II_I u (t e (tt e__))) =>
 Covariant Monoidal Functor (->) LM LM tt =>
 Covariant Monoidal Functor (->) u LM (U_I_II t e) =>
 u (t e (tt e_)) (t e (tt e__)) -> t e (tt (e_ `LM` e__))
yip'yp x = yip'yo x yp

yip'yip :: forall u e e_ e__ e___ t tt .
 Covariant Endo Semi Functor (->) (U_I_II t e) =>
 Covariant Endo Semi Functor (->) (U_I_II u (U_I_II t e (tt e_ e__))) =>
 Covariant Endo Semi Functor (->) (U_II_I u (t e (tt e_ e___))) =>
 Covariant Monoidal Functor (->) LM LM (U_I_II tt e_) =>
 Covariant Monoidal Functor (->) u LM (U_I_II t e) =>
 u (t e (tt e_ e__)) (t e (tt e_ e___)) -> t e (tt e_ (e__ `LM` e___))
yip'yip x = yip'yo x yip

yip'yis :: forall u e e_ e__ e___ t tt .
 Covariant Endo Semi Functor (->) (U_I_II t e) =>
 Covariant Endo Semi Functor (->) (U_I_II u (U_I_II t e (tt e_ e__))) =>
 Covariant Endo Semi Functor (->) (U_II_I u (t e (tt e_ e___))) =>
 Covariant Monoidal Functor (->) u LM (U_I_II t e) =>
 Covariant Monoidal Functor (->) LM ML (U_I_II tt e_) =>
 u (t e (tt e_ e__)) (t e (tt e_ e___)) -> t e (tt e_ (e__ `ML` e___))
yip'yis x = yip'yo x yis

-- TODO: try to generalize
yp'yok :: forall e e_ from into t tt l o .
 Covariant Monoidal Functor (->) LM LM t =>
 Covariant Endo Semi Functor into tt =>
 Covariant Endo Semi Functor into t =>
 Covariant Yoneda from into t =>
 Component Natural into into (T'TT'I t (L l tt)) t =>
 Castable Opposite into (Straight from (e `LM` e_) (L l tt o)) =>
 (forall e__ . Wrapper into (T'TT'I t (L l tt) e__)) =>
 t e `LM` t e_ -> into (from (e `LM` e_) (L l tt o)) (t o)
yp'yok = yok @from @into `compose` yp

-- TODO: try to generalize
yp'yokl :: forall e ee from into t tt l o .
 Component Natural from into (t `T'TT'I` L l tt) (TT'T'I t tt) =>
 Covariant Monoidal Functor (->) LM LM t =>
 Covariant Yoneda from into t =>
 Castable Opposite into (U_I_II from (e `LM` ee) (tt o)) =>
 (forall i . Wrapper into (T'TT'I t tt i)) =>
 (forall i . Wrapper into (TT'T'I t tt i)) =>
 (forall i . Wrapper into ((t `T'TT'I` L l tt) i)) =>
 (forall i ii . Wrapper into (U_I_II from i (L l tt ii))) =>
 t e `LM` t ee -> into (from (e `LM` ee) (L l tt o)) (tt (t o))
yp'yokl = yokl @from @into `compose` yp

-- TODO: try to generalize
yp'yp'yo :: forall from e e_ r t tt .
 Covariant Monoidal Functor (->) LM LM t =>
 Covariant Monoidal Functor from LM LM tt =>
 t (tt e) `LM` t (tt e_) -> from (e `LM` e_) r -> t (tt r)
yp'yp'yo x f = day @Straight @(->) @t @LM @LM identity
 (day @Straight @from @tt @LM @LM identity f) x

-- w'rw :: forall into a o
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

-- yi__, yi___, yi____, yi_____, yi______ :: forall into a .
 -- Precategory into =>
 -- Castable Straight into a =>
 -- Castable Straight into (Supertype a) =>
 -- into a (Supertype (Supertype a))
-- yi__ = _' @into `compose` _' @into

-- yi___ = yi__
-- yi____ = yi__
-- yi_____ = yi__
-- yi______ = yi__

-- yi___, yi____, yi_____, yi______, yi_______ :: forall into a .
 -- Precategory into =>
 -- Castable Straight into a =>
 -- Castable Straight into (Supertype a) =>
 -- Castable Straight into (Supertype (Supertype a)) =>
 -- into a (Supertype (Supertype (Supertype a)))
-- yi___ = _' @into `compose` _' @into `compose` _' @into

-- yi____ = yi___
-- yi_____ = yi___
-- yi______ = yi___
-- yi_______ = yi___

-- TODO: it's wrong, we ne_d to rewrite it
-- he'he'he'ho :: forall a e o o_ .
--  Castable Straight (->) a =>
--  Castable Straight (->) (Supertype a) =>
--  Castable Straight (->) (Supertype (Supertype a)) =>
--  ((e `ARR` o) ~ Supertype (Supertype (Supertype a))) =>
--  a `ARR` e `ARR` (o `ARR` o_) `ARR` o_
-- he'he'he'ho x e f = f (_' (_' (_' x)) e)

-- TODO: define `rw'o`
-- TODO: define `rw'rw'o`
-- TODO: define `rw'ha`
-- TODO: define `rw'rw'ha`
-- TODO: define `rw'rw'rw'ha`

ho'yok, ho_'yok, ho__'yok, ho___'yok, ho____'yok, ho_____'yok, ho______'yok, ho_______'yok, ho________'yok :: forall from u t tt l a o e .
 Covariant Endo Semi Functor from tt =>
 Covariant Endo Semi Functor from t =>
 Mapping Straight Straight from from (t `T'TT'I` L l tt) t =>
 Covariant Yoneda from (->) (Straight u e) =>
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

ho'yuk, ho_'yuk, ho__'yuk, ho___'yuk, ho____'yuk, ho_____'yuk, ho______'yuk, ho_______'yuk, ho________'yuk :: forall from t tt a o e .
 Covariant Endo Semi Functor from tt =>
 Covariant Endo Semi Functor from t =>
 Constant Semi Functor from from t =>
 Component Natural from from (T'TT'I t tt) t =>
 Component Natural from (->) Identity (U_I_II from a) =>
 Covariant Yoneda from (->) (Straight from e) =>
 Wrapper from (T'TT'I t t o) =>
 Wrapper from (Identity (tt o)) =>
 Wrapper (->) (U_1_I from a (tt o)) =>
 (forall e_ . Wrapper from (T'TT'I t tt e_)) =>
 from e (t a) -> tt o -> from e (t o)
ho'yuk x = fai (fuk @from @t @tt) (ho @from x)
ho_'yuk x = fai (fuk @from @t @tt) (ho @from x)
ho__'yuk x = fai (fuk @from @t @tt) (ho @from x)
ho___'yuk x = fai (fuk @from @t @tt) (ho @from x)
ho____'yuk x = fai (fuk @from @t @tt) (ho @from x)
ho_____'yuk x = fai (fuk @from @t @tt) (ho @from x)
ho______'yuk x = fai (fuk @from @t @tt) (ho @from x)
ho_______'yuk x = fai (fuk @from @t @tt) (ho @from x)
ho________'yuk x = fai (fuk @from @t @tt) (ho @from x)

ha'yok :: forall from u t tt l a o e .
 Covariant Functor (->) (->) tt =>
 Covariant Functor from (->) t =>
 Covariant Functor from (->) tt =>
 Covariant Functor from from tt =>
 Covariant Functor from from t =>
 Mapping Straight Straight from from (t `T'TT'I` L l tt) t =>
 Contravariant Yoneda from (->) (U_II_I (->) (tt o)) =>
 Contravariant Yoneda from (->) (U_II_I u e) =>
 (forall ee . Wrapper from ((t `T'TT'I` L l tt) ee)) =>
 (forall ee . Wrapper from ((t `T'TT'I` tt) ee)) =>
 (forall ee . Wrapper from (L l tt ee)) =>
 u (t o) e -> from a (L l tt o) -> u (t a) e
ha'yok x = fai fok (ha @from x)

-- TODO: try to gereralize
yok'ho :: forall from t tt label a o e .
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
 Contravariant Yoneda from (->) (Opposite from (Labeled label tt o)) =>
 Mapping Straight Straight from from (T'TT'I t (Labeled label tt)) t =>
 (forall ee . Wrapper from ((t `T'TT'I` Labeled label tt) ee)) =>
 Wrapper from (U_II_I from e (Labeled label tt o)) =>
 Wrapper from (U_I_II from e (Labeled label tt o)) =>
 (forall ee . Wrapper from (Labeled label tt ee)) =>
 Wrapper from (U_II_I from o a) =>
 Wrapper from (U_II_I from o e) =>
 Wrapper from (U_I_II from e a) =>
 t e -> from a (Labeled label tt o) -> from (from e a) (t o)
yok'ho x f = yok x `compose` fio f

-- TODO: try to gereralize
yok'ha :: forall into t tt label a o e .
 Category into =>
 Covariant Yoneda into into t =>
 Covariant Functor into into t =>
 Covariant Functor into into tt =>
 Contravariant Functor into into (U_II_I into (Labeled label tt o)) =>
 Contravariant Yoneda into (->) (U_II_I into (Labeled label tt o)) =>
 Mapping Straight Straight into into (T'TT'I t (Labeled label tt)) t =>
 (forall ee . Wrapper into ((t `T'TT'I` Labeled label tt) ee)) =>
 (forall ee . Wrapper into (Labeled label tt ee)) =>
 Wrapper into (U_I_II into e (Labeled label tt o)) =>
 Wrapper into (U_II_I into (Labeled label tt o) e) =>
 Wrapper into (U_II_I into (Labeled label tt o) a) =>
 t e -> into e a -> into (into a (Labeled label tt o)) (t o)
yok'ha x f = yok @into @into x `compose` fai @into f

-- yok'hu :: forall from t tt a o e .
  -- Precategory from =>
  -- Covariant Yoneda from from t =>
  -- Mapping Straight Straight from from (U_I_II from e) (U_I_II from e) =>
  -- Constant Semi Functor from from (U_I_II from e) =>
  -- Covariant Semi Functor from from t =>
  -- Covariant Semi Functor (->) from t =>
  -- Covariant Semi Functor from (->) tt =>
  -- Covariant Semi Functor (->) from tt =>
  -- Mapping Straight Straight (->) from (T'TT'I t tt) t =>
  -- (forall e_ . Wrapper from ((t `T'TT'I` tt) e_)) =>
  -- Castable Opposite from (T'TT'I t tt o) =>
  -- Wrapper from (U_I_II from e (tt o)) =>
  -- Castable Opposite from (U_I_II from e a) =>
  -- Castable Opposite from (U_1_I from a (tt o)) =>
  -- Castable Opposite (->) (U_1_I from a (tt o)) =>
  -- t e -> Supertype (U_1_I from a (tt o)) -> from (from e a) (t o)
-- yok'hu x f = yok @_ @_ @tt x `compose` fiu @from f

-- yokl__ :: forall from u t tt a o e .
 -- Category from =>
 -- -- Covariant Endo Semi Functor from tt =>
 -- Covariant Functor from from (Straight u e) =>
 -- Covariant Functor (->) u t =>
 -- Covariant Functor u u t =>
 -- -- Mapping Straight Straight from from (T'TT'I t tt) t =>
 -- Covariant Yoneda from u t =>
 -- Covariant Yoneda u from (Straight u e) =>
 -- Covariant Yoneda from from (Opposite u (t o)) =>
 -- -- Covariant Yoneda from from t =>
 -- -- (forall e_ . Wrapper from (T'TT'I t tt e_)) =>
 -- -- t (from a o) -> from (u e a) (t o)
 -- t (u e a) -> u (from a o) (t o)
-- yokl__ x = fai fio (yokl @from @u x)

ho'yokl, ho_'yokl, ho__'yokl, ho___'yokl, ho____'yokl, ho_____'yokl, ho______'yokl, ho_______'yokl, ho________'yokl :: forall from u t tt l a o e .
 Covariant Semi Functor from (->) (Straight u e) =>
 Covariant Endo Semi Functor from tt =>
 Covariant Endo Semi Functor from t =>
 Mapping Straight Straight from from (t `T'TT'I` L l tt) (t `TT'T'I` tt) =>
 Covariant Yoneda from (->) (Straight u e) =>
 (forall ee . Wrapper from ((t `T'TT'I` L l tt) ee)) =>
 (forall ee . Wrapper from ((t `T'TT'I` tt) ee)) =>
 (forall ee . Wrapper from ((t `TT'T'I` tt) ee)) =>
 (forall ee . Wrapper from (L l tt ee)) =>
 u e (t a) -> from a (L l tt o) -> u e (tt (t o))
ho'yokl x = fai fokl (ho @from x)

ho_'yokl = ho'yokl
ho__'yokl = ho'yokl
ho___'yokl = ho'yokl
ho____'yokl = ho'yokl
ho_____'yokl = ho'yokl
ho______'yokl = ho'yokl
ho_______'yokl = ho'yokl
ho________'yokl = ho'yokl

-- ha'yuk :: forall from t tt a o e .
--  Covariant Functor (->) (->) tt =>
--  Covariant Functor from from t =>
--  Covariant Functor from from tt =>
--  Contravariant Yoneda from (->) (U_II_I from (tt o)) =>
--  Mapping Straight Straight from from (T'TT'I tt t) tt =>
--  Constant Semi Functor from from tt =>
--  Castable Opposite from (T'TT'I tt t o) =>
--  (forall e_ . Wrapper from (T'TT'I tt t e_)) =>
--  Castable Opposite from (T'TT'I tt tt o) =>
--  Castable Opposite (->) (U_1_I from a (t o)) =>
--  Supertype (U_1_I from a (t o)) -> from e (tt a) -> from e (tt o)
-- ha'yuk = ha `compose` fuk @from @tt @t

-- fr'yp :: forall from t i o o_ .
 -- Category from =>
 -- Limit Straight from from =>
 -- Covariant Functor (->) (->) (U_I_II (LM) o) =>
 -- Covariant Functor from (->) (U_II_I (LM) (LM i i)) =>
 -- Covariant Monoidal Functor (->) LM LM t =>
 -- Castable Straight (->) (U_I_I LM (LM i i)) =>
 -- Castable Straight (->) (U_I_II LM o o_) =>
 -- Castable Opposite from (U_II_I LM i i) =>
 -- Castable Opposite (->) (U_I_II LM i i) =>
 -- Castable Straight (->) (U_I_I LM i) =>
 -- Castable Straight (->) (U_II_I LM (LM i i) o) =>
 -- Castable Opposite (->) (U_II_I LM (LM i i) (LM i i)) =>
 -- Wrapper (->) (U_I_II (LM) o (LM i i)) =>
 -- (forall e . Wrapper from (Identity e)) =>
 -- from i (t o) -> from i (t o_) -> i -> t (LM o o_)
-- fr'yp from__eft from_right = yp `compose`
 -- __ (map @Straight @Straight @from (wrapped (right @Straight from_right))) `compose`
 -- i_ (map @Straight @Straight @from (wrapped (left @Straight from__eft))) `compose`
 -- wrapped (map @Straight @Straight @from @(->) @Identity @(U_I_I LM) identity) `compose`
 -- wrapped (map @Straight @Straight @from @(->) @Identity @(U_I_I LM) identity)

-- TODO: generalize
lu'yp, lu_'yp, lu__'yp, lu___'yp, lu____'yp, lu_____'yp, lu______'yp, lu_______'yp :: forall o o_ t .
 Covariant Monoidal Functor (->) LM LM t =>
 Covariant Yoneda (->) (->) (U_I_II Product (t o)) =>
 Covariant Yoneda (->) (->) (U_II_I Product ()) =>
 t o -> t o_ -> t (o `LM` o_)
lu'yp from__eft from_right = yp (lu from__eft from_right)

lu_'yp = lu'yp
lu__'yp = lu'yp
lu___'yp = lu'yp
lu____'yp = lu'yp
lu_____'yp = lu'yp
lu______'yp = lu'yp
lu_______'yp = lu'yp

lu'yip, lu_'yip, lu__'yip, lu___'yip, lu____'yip, lu_____'yip, lu______'yip, lu_______'yip
 :: forall e o o_ t .
 Covariant Monoidal Functor (->) LM LM (U_I_II t e) =>
 Covariant Yoneda (->) (->) (U_I_II Product (t e o)) =>
 Covariant Yoneda (->) (->) (U_II_I Product ()) =>
 t e o -> t e o_ -> t e (o `LM` o_)
lu'yip from__eft from_right = yip (lu from__eft from_right)

lu_'yip = lu'yip
lu__'yip = lu'yip
lu___'yip = lu'yip
lu____'yip = lu'yip
lu_____'yip = lu'yip
lu______'yip = lu'yip
lu_______'yip = lu'yip

lu'ys, lu_'ys, lu__'ys, lu___'ys, lu____'ys, lu_____'ys, lu______'ys, lu_______'ys
 :: forall o o_ t .
 Covariant Monoidal Functor (->) LM ML t =>
 Covariant Yoneda (->) (->) (U_I_II LM (t o)) =>
 Covariant Yoneda (->) (->) (U_II_I LM ()) =>
 t o -> t o_ -> t (o `ML` o_)
lu'ys from__eft from_right = ys (lu from__eft from_right)

lu_'ys = lu'ys
lu__'ys = lu'ys
lu___'ys = lu'ys
lu____'ys = lu'ys
lu_____'ys = lu'ys
lu______'ys = lu'ys
lu_______'ys = lu'ys

lu'yis, lu_'yis, lu__'yis, lu___'yis, lu____'yis, lu_____'yis, lu______'yis, lu_______'yis
 :: forall e o o_ t .
 Covariant Monoidal Functor (->) LM ML (U_I_II t e) =>
 Covariant Yoneda (->) (->) (U_I_II LM (t e o)) =>
 Covariant Yoneda (->) (->) (U_II_I LM ()) =>
 t e o -> t e o_ -> t e (o `ML` o_)
lu'yis from__eft from_right = yis (lu from__eft from_right)

lu_'yis = lu'yis
lu__'yis = lu'yis
lu___'yis = lu'yis
lu____'yis = lu'yis
lu_____'yis = lu'yis
lu______'yis = lu'yis
lu_______'yis = lu'yis

lu'yp'yp :: forall o o_ t tt .
 Covariant Monoidal Functor (->) LM LM t =>
 Covariant Monoidal Functor (->) LM LM tt =>
 -- Mapping Straight Straight into (->) Identity (U_I_I (Product into)) =>
 Covariant Yoneda (->) (->) (U_I_II Product (t (tt o))) =>
 Covariant Yoneda (->) (->) (U_II_I Product ()) =>
 t (tt o) -> t (tt o_) -> t (tt (o `LM` o_))
lu'yp'yp from__eft from_right = yp'yp @LM (lu from__eft from_right)

lu'yp'ys
 :: forall t tt o o_ .
 Covariant Monoidal Functor (->) LM LM t =>
 Covariant Monoidal Functor (->) LM ML tt =>
 Covariant Endo Semi Functor (->) t =>
 Covariant Yoneda (->) (->) (U_II_I Product ()) =>
 Covariant Yoneda (->) (->) (U_I_II Product (t (tt o))) =>
 t (tt o) -> t (tt o_) -> t (tt (o `ML` o_))
lu'yp'ys from__eft from_right = yp'ys (lu from__eft from_right)

lu'yip'yp
 :: forall t tt o o_ e .
 Covariant Monoidal Functor (->) LM LM tt =>
 Covariant Monoidal Functor (->) LM LM (U_I_II t e) =>
 Covariant Endo Semi Functor (->) (U_I_II t e) =>
 Covariant Yoneda (->) (->) (U_II_I Product ()) =>
 Covariant Yoneda (->) (->) (U_I_II Product (t e (tt o))) =>
 t e (tt o) -> t e (tt o_) -> t e (tt (o `LM` o_))
lu'yip'yp from__eft from_right = yip'yp (lu from__eft from_right)

lu'yip'yip
 :: forall t tt o o_ e e_ .
 Covariant Monoidal Functor (->) LM LM (U_I_II tt e_) =>
 Covariant Monoidal Functor (->) LM LM (U_I_II t e) =>
 Covariant Endo Semi Functor (->) (U_I_II t e) =>
 Covariant Yoneda (->) (->) (U_II_I Product ()) =>
 Covariant Yoneda (->) (->) (U_I_II Product (t e (tt e_ o))) =>
 t e (tt e_ o) -> t e (tt e_ o_) -> t e (tt e_ (o `LM` o_))
lu'yip'yip from__eft from_right = yip'yip (lu from__eft from_right)

lu'yip'yis
 :: forall t tt o o_ e e_ .
 Covariant Monoidal Functor (->) LM LM (U_I_II t e) =>
 Covariant Monoidal Functor (->) LM ML (U_I_II tt e_) =>
 Covariant Endo Semi Functor (->) (U_I_II t e) =>
 Covariant Yoneda (->) (->) (U_II_I Product ()) =>
 Covariant Yoneda (->) (->) (U_I_II Product (t e (tt e_ o))) =>
 t e (tt e_ o) -> t e (tt e_ o_) -> t e (tt e_ (o `ML` o_))
lu'yip'yis from__eft from_right = yip'yis (lu from__eft from_right)

jt :: forall into f g e .
 Component Natural (->) into (f `T'TT'I` g) (f `JNT` g) =>
 Castable Opposite into ((f `T'TT'I` g) e) =>
 into (f (g e)) ((f `JNT` g) e)
jt = component @Straight @(->) @into @(f `T'TT'I` g) @(f `JNT` g) @e
 `compose` wrap @into @((f `T'TT'I` g) e)

-- TODO: generalize
yp'yp'jt :: forall e e_ t tt .
 Component Natural (->) (->) (t `T'TT'I` tt) (t `JNT` tt) =>
 Covariant Monoidal Functor (->) LM LM t =>
 Covariant Monoidal Functor (->) LM LM tt =>
 t (tt e) `LM` t (tt e_) -> (t `JNT` tt) (e `LM` e_)
yp'yp'jt = jt `compose` day @Straight @(->) @t @LM @LM identity
 (day @Straight @(->) @tt @LM @LM identity identity)

-- TODO: generalize
-- yp'yp'jt'yok :: forall from into e e_ t tt ttt o .
 -- Covariant Yoneda from into t =>
 -- Covariant Semi Functor into into ttt =>
 -- Covariant Yoneda from into (t `JNT` tt) =>
 -- Component Natural (->) (->) (t `T'TT'I` tt) (t `JNT` tt) =>
 -- Component Natural (->) into (T'TT'I (t `JNT` tt) ttt) (t `JNT` tt) =>
 -- Covariant Monoidal Functor (->) LM LM t =>
 -- Covariant Monoidal Functor (->) LM LM tt =>
 -- Castable Opposite into (Straight from (e `LM` e_) (ttt o)) =>
 -- (forall e . Wrapper into (T'TT'I (JNT t tt) ttt e)) =>
 -- t (tt e) `LM` t (tt e_) -> into (from (e `LM` e_) (ttt o)) ((t `JNT` tt) o)
-- yp'yp'jt'yok = yok @from @into `compose` yp'yp'jt

-- TODO: generalize
-- rwr'foi :: forall into w o u e e_ .
 -- Covariant Endo Semi Functor into (U_II_I u o) =>
 -- Castable Straight into (U_II_I u o e_) =>
 -- Castable Opposite into (U_II_I u o e) =>
 -- Castable Opposite into (w u e_ o) =>
 -- Castable Straight into (w u e o) =>
 -- (Supertype (w u e o) ~ u e o) =>
 -- (Supertype (w u e_ o) ~ u e_ o) =>
 -- into e e_ -> into (w u e o) (w u e_ o)
-- rwr'foi = rwr `compose` i_ `compose` fo

-- TODO: generalize
-- rwr'fio :: forall into w o u e e_ .
 -- Covariant Endo Semi Functor into (U_I_II u o) =>
 -- Castable Straight into (U_I_II u o e_) =>
 -- Castable Opposite into (U_I_II u o e) =>
 -- Castable Opposite into (w u o e_) =>
 -- Castable Straight into (w u o e) =>
 -- (Supertype (w u o e) ~ u o e) =>
 -- (Supertype (w u o e_) ~ u o e_) =>
 -- into e e_ -> into (w u o e) (w u o e_)
-- rwr'fio = rwr `compose` __ `compose` fo

-- TODO: try to simplify
-- rwr'yoi :: forall from into w o u e e_ .
 -- Precategory into =>
 -- Covariant Yoneda from into (U_II_I u o) =>
 -- Castable Opposite into (w u e_ o) =>
 -- Castable Straight (->) (w u e o) =>
 -- Castable Straight into (U_II_I u o e_) =>
 -- Castable Opposite into (U_I_II from e e_) =>
 -- (Supertype (w u e o) ~ u e o) =>
 -- (Supertype (w u e_ o) ~ u e_ o) =>
 -- w u e o -> into (from e e_) (w u e_ o)
-- rwr'yoi x = wrap @into `compose` yoi (unwrap x)

-- -- TODO: generalize
-- o_rwr_''yoi :: forall from into w a o u e e_ .
--  Precategory into =>
--  Covariant Endo Semi Functor into (U_II_I u o) =>
--  Covariant Yoneda into (->) (U_I_II from a) =>
--  Castable Straight into (w u e o) =>
--  Castable Opposite into (w u e_ o) =>
--  Castable Straight into (U_II_I u o e_) =>
--  Castable Opposite into (U_II_I u o e) =>
--  (Supertype (w u e o) ~ u e o) =>
--  (Supertype (w u e_ o) ~ u e_ o) =>
--  from a (w u e o) -> into e e_ -> from a (w u e_ o)
-- o_rwr_yoi x f = x `ho` rwr_foi @into @w @o @u @e @e_ f

-- -- TODO: generalize
-- o_rwr_yio :: forall from into w a o u e e_ .
--  Precategory into =>
--  Covariant Endo Semi Functor into (U_I_II u o) =>
--  Covariant Yoneda into (->) (U_I_II from a) =>
--  Castable Straight into (w u o e) =>
--  Castable Opposite into (w u o e_) =>
--  Castable Straight into (U_I_II u o e_) =>
--  Castable Opposite into (U_I_II u o e) =>
--  (Supertype (w u o e) ~ u o e) =>
--  (Supertype (w u o e_) ~ u o e_) =>
--  from a (w u o e) -> into e e_ -> from a (w u o e_)
-- o_rwr_yio x f = x `ho` rwr_fio @into @w @o @u @e @e_ f

-- yokl_rwr_yoi :: forall into w t o u e e_ .
--  Covariant Yoneda into (->) t =>
--  Covariant Endo Semi Functor (->) t =>
--  Covariant Endo Semi Functor (->) (w u e_) =>
--  Covariant Endo Semi Functor into (U_II_I u o) =>
--  Component Natural (->) (->) (T'TT'I t (w u e_)) t =>
--  (Supertype (w u e o) ~ u e o) =>
--  (Supertype (w u e_ o) ~ u e_ o) =>
--  Castable Opposite (->) (into () e_) =>
--  Castable Opposite into (U_II_I u o e) =>
--  Castable Opposite into (w u e_ o) =>
--  Castable Straight into (U_II_I u o e_) =>
--  Castable Straight into (w u e o) =>
--  t (w u e o) -> into e e_ -> t o
-- yokl_rwr_yoi x f = yokl @into @_ @(w u e_) @t x
--  (rwr_foi @into @w @o @u @e @e_ f)

-- rwr_yui :: forall into w o u e e_ .
--  Covariant Endo Semi Functor into (U_II_I u o) =>
--  Constant Semi Functor into into (U_II_I u o) (U_II_I u o) =>
--  Castable Straight into (U_II_I u o e_) =>
--  Castable Opposite into (U_II_I u o e) =>
--  Castable Opposite into (w u e_ o) =>
--  Castable Straight into (w u e o) =>
--  Castable Opposite (->) (into () e_) =>
--  (Supertype (w u e o) ~ u e o) =>
--  (Supertype (w u e_ o) ~ u e_ o) =>
--  Supertype (into () e_) -> into (w u e o) (w u e_ o)
-- rwr_yui = rwr `compose` i_ `compose` fu

-- TODO: find a way to generalize
-- yokl_rwr_yui :: forall w t o u e e_ .
--  Covariant Yoneda (->) (->) t =>
--  Covariant Endo Semi Functor (->) t =>
--  Covariant Endo Semi Functor (->) (w u e_) =>
--  Covariant Endo Semi Functor (->) (U_II_I u o) =>
--  Constant Semi Functor (->) (->) (U_II_I u o) (U_II_I u o) =>
--  Component Natural (->) (->) (T'TT'I t (w u e_)) t =>
--  (Supertype (w u e o) ~ u e o) =>
--  (Supertype (w u e_ o) ~ u e_ o) =>
--  Castable Opposite (->) ((->) () e_) =>
--  Castable Opposite (->) (U_II_I u o e) =>
--  Castable Opposite (->) (w u e_ o) =>
--  Castable Straight (->) (U_II_I u o e_) =>
--  Castable Straight (->) (w u e o) =>
--  t (w u e o) -> Supertype (() -> e_) -> t o
-- yokl_rwr_yui x f = yokl @(->) @_ @(w u e_) @t x
--  (rwr_yui @(->) @w @o @u @e @e_ f)

-- TODO: effects are executed in reverse order, we can use it
-- to alter execution order, in Scrolling List for example
fc :: forall into t a o .
 Covariant Endo Semi Functor (->) t =>
 Covariant Endo Semi Functor (->) (U_I_II into a) =>
 Adjoint Functor (->) (->) (U_I_II LM (t a)) (U_I_II into (t a)) =>
 Adjoint Functor (->) (->) (U_I_II LM a) (U_I_II into a) =>
 Adjoint Functor (->) (->) (U_I_II LM (t a `LM` t (into a o))) (U_I_II (->) (t a `LM` t (into a o))) =>
 Monoidal Straight Functor into LM LM t =>
 t (into a o) -> into (t a) (t o)
fc = unwrap @(->) @(U_I_II into (t a) _)
 `compose` (fo @(->) @(->) `compose` fo @(->) @(->))
 (fd @(->) @(->) (wrap @_ @(U_I_II _ _ _)) `compose` wrap @_ @(U_I_II _ _ _))
 `compose` fj @(->) @(->) @(U_I_II LM (t a)) @(U_I_II into _)
 (monoidal_ @Straight @into @(->) @t @LM @LM identity (wrap identity)
 `compose` unwrap @(->) @(U_I_II LM (t a) (t (into a o))))

-- cc :: forall t e e_ .
--  Adjoint Functor (->) (->) (U_I_II LM (t e `LM` t e_)) (U_I_II (->) (t e `LM` t e_)) =>
--  Monoidal Straight Functor (->) LM LM t =>
--  t e -> t e_ -> t (e `LM` e_)
-- cc e e_ = monoidal_
--  @Straight @(->) @(->) @t @LM @LM identity
--  (wrap identity)
--  (e `lu` e_)

q, q_, q__, q___, q____, q_____, q______, q_______, q________ ::
 forall into e .
 Setoid into e =>
 into (e `LM` e) (e `LM` e `ML` e)
q = equality

q_ = q
q__ = q
q___ = q
q____ = q
q_____ = q
q______ = q
q_______ = q
q________ = q
