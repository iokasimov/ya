{-# LANGUAGE AllowAmbiguousTypes #-}
module Ya.Operators.Handcraft where

import Ya.Algebra.Abstract
import Ya.Algebra.Definition
import Ya.Algebra.Effectful
import Ya.Algebra.Instances ()

import Ya.Operators.Mappings

infixl 9 `ho`, `ho'yioi`, `ho'yu`, `ho'yui`, `ho'yok`, `ho'yuk`, `ho'yokl`, `ho'yukl` -- , `ho'yokl'yokl`, `ho'yokl'yukl`, `ho'yoikl` --, `ho'yoo`
 , `ho'st`
 , `ho'st'st`
 -- , `ho'st'st'st`
 -- , `ho'st'st'st'st`
 -- , `ho'hd`
 -- , `ho'hd'hd`
 -- , `ho'hu`
infixl 8 `ho_`, `ho_'yu`, `ho_'yok`, `ho_'yuk`, `ho_'yokl`, `ho_'yukl` --, `ho_'yokl'yokl`, `ho_'yokl'yukl`, `ho_'yoikl`, `ho_'yoo`,
 , `ho_'st`
 , `ho_'st'st`
 -- , `ho_'st'st'st`
 -- , `ho_'st'st'st'st`
 -- , `ho_'hd`
infixl 7 `ho__`, `ho__'yu`, `ho__'yok`, `ho__'yuk`, `ho__'yokl`, `ho__'yukl` --, `ho__'yokl'yokl`, `ho__'yokl'yukl`, `ho__'yoikl` `ho__'yoo`,
 , `ho__'st`
 , `ho__'st'st`
 -- , `ho__'st'st'st`
 -- , `ho__'st'st'st'st`
 -- , `ho__'hd`
infixl 6 `ho___`, `ho___'yu`, `ho___'yok`, `ho___'yuk`, `ho___'yokl`, `ho___'yukl` --, `ho___'yokl'yokl`, `ho___'yokl'yukl`, `ho___'yoikl`
 , `ho___'st`
 , `ho___'st'st`
 -- , `ho___'st'st'st`
 -- , `ho___'st'st'st'st`
 -- , `ho___'hd`
infixl 5 `ho____`, `ho____'yu`, `ho____'yok`, `ho____'yuk`, `ho____'yokl`, `ho____'yukl` --, `ho____'yokl'yokl`, `ho____'yokl'yukl`, `ho____'yoikl`
 , `ho____'st`
 , `ho____'st'st`
 -- , `ho____'st'st'st`
 -- , `ho____'st'st'st'st`
infixl 4 `ho_____`, `ho_____'yu`, `ho_____'yok`, `ho_____'yuk`, `ho_____'yokl`, `ho_____'yukl` --, `ho_____'yokl'yokl`, `ho_____'yokl'yukl`, `ho_____'yoikl`
 , `ho_____'st`
 , `ho_____'st'st`
 -- , `ho_____'st'st'st`
 -- , `ho_____'st'st'st'st`
 -- , `ho____'hd`
infixl 3 `ho______`, `ho______'st` -- , `ho______'yok`, `ho______'yuk`, `ho______'yokl`, `ho______'yokl'yokl`, `ho______'yokl'yukl`, `ho______'yukl`, `ho______'yoikl`
infixl 2 `ho_______`  -- `ho_______'yoo`, `ho_______'yok`, `ho_______'yuk`, `ho_______'yokl`, `ho_______'yokl'yokl`, `ho_______'yokl'yukl`, `ho_______'yukl`, `ho_______'yoikl`
 , `ho_______'st`
 , `ho_______'st'st`
 -- , `ho_______'st'st'st`
 -- , `ho_______'st'st'st'st`
 -- , `ho_____'hd`
infixl 1 `ho________` -- , `ho________'yok`, `ho________'yuk`, `ho________'yokl`, `ho________'yukl` , `ho________'yokl'yokl`, `ho________'yokl'yukl`, `ho________'yoikl`
 , `ho________'st`
 , `ho________'st'st`
 -- , `ho________'st'st'st`
 -- , `ho________'st'st'st'st`
 -- , `ho______'hd`
 -- , `ho________'yo`
 -- , `ho________'yoi`

infixl 9 `ha`, `ha'hu`
 , `ha'yok`
 -- , `ha'yuk`
 -- , `ha'kyo`
 -- , `ha'kyok`
 , `ha'yokl`
 -- , `ha'yukl`
 , `ha'st`
 -- , `st'ha`
 -- , `ha'hd`
 -- , `ha'hd'hd`
infixl 8 `ha_`
 , `ha_'st`
 , `ha_'hu`
 , `ha_'yok`
 -- , `ha_'yuk`
 -- , `ha_'kyo`
 -- , `ha_'kyok`
 , `ha_'yokl`
 -- , `ha_'yukl`
infixl 7 `ha__`
 , `ha__'st`
 , `ha__'hu`
 , `ha__'yok`
 -- , `ha__'yuk`
 -- , `ha__'kyo`
 -- , `ha__'kyok`
 , `ha__'yokl`
 -- , `ha__'yukl`
infixl 6 `ha___`
 , `ha___'st`
 , `ha___'hu`
 , `ha___'yok`
 -- , `ha___'yuk`
 -- , `ha___'kyo`
 -- , `ha___'kyok`
 , `ha___'yokl`
 -- , `ha___'yukl`
infixl 5 `ha____`
 , `ha____'st`
 , `ha____'hu`
 , `ha____'yok`
 -- , `ha____'yuk`
 -- , `ha____'kyo`
 -- , `ha____'kyok`
 , `ha____'yokl`
 -- , `ha____'yukl`
infixl 4 `ha_____`
 , `ha_____'st`
 , `ha_____'hu`
 , `ha_____'yok`
 -- , `ha_____'yuk`
 -- , `ha_____'kyo`
 -- , `ha_____'kyok`
 , `ha_____'yokl`
 -- , `ha_____'yukl`
infixl 3 `ha______`
 , `ha______'st`
 , `ha______'hu`
 , `ha______'yok`
 -- , `ha______'yuk`
 -- , `ha______'kyo`
 -- , `ha______'kyok`
 , `ha______'yokl`
 -- , `ha______'yukl`
infixl 2 `ha_______`
 , `ha_______'st`
 , `ha_______'hu`
 , `ha_______'yok`
 -- , `ha_______'yuk`
 -- , `ha_______'kyo`
 -- , `ha_______'kyok`
 , `ha_______'yokl`
 -- , `ha_______'yukl`
infixl 1 `ha________`
 , `ha________'st`
 , `ha________'hu`
 -- , `ha________'yok`
 -- , `ha________'yuk`
 , `ha________'yokl`
 -- , `ha________'yukl`

infixl 9 `hu`, `hu'st` --, `st'hu`
infixl 8 `hu_`, `hu_'st` --, `st'hu_`
infixl 7 `hu__`, `hu__'st` --, `st'hu__`
infixl 6 `hu___`, `hu___'st` --, `st'hu___`
infixl 5 `hu____`, `hu____'st` --, `st'hu____`
infixl 4 `hu_____`, `hu_____'st` --, `st'hu_____`
infixl 3 `hu______`, `hu______'st` -- , `st'hu______`
infixl 2 `hu_______`, `hu_______'st` --, `st'hu_______`
infixl 1 `hu________`, `hu________'st` --, `st'hu________`

--, `st'st'ho`, `st'st'st'ho`

-- infixl 9 `st'ho`, `st'ho'st`
-- infixl 8 `he_'ho`, `he_'ho'st`
-- infixl 7 `he__'ho`, `he__'ho'st`
-- infixl 6 `he___'ho`, `he___'ho'st`
-- infixl 5 `he____'ho`, `he____'ho'st`
-- infixl 4 `he_____'ho`, `he_____'ho'st`
-- infixl 3 `he______'ho`, `he______'ho'st`
-- infixl 2 `he_______'ho`, `he_______'ho'st`
-- infixl 1 `he________'ho`, `he________'ho'st`

infixl 9 `hc`, `hc'st`
infixl 8 `hc_`, `hc_'st`, `hdj`
infixl 7 `hc__`, `hc__'st`, `hdj_`
infixl 6 `hc___`, `hc___'st`, `hdj__`
infixl 5 `hc____`, `hc____'st`, `hdj___`
infixl 4 `hc_____`, `hc_____'st`, `hdj____`
infixl 3 `hc______`
infixl 2 `hc_______`
infixl 1 `hc________`

infixl 8 `hop`, `hop'hjd`, `hop'yp`, `hop'yp'yo'q`, `hop'ys`, `hop'ys'has`, `hop'q`, `hjd'ys'has`
infixl 7 `hop_`, `hop_'yp`, `hop_'yp'yo'q`, `hop_'ys`, `hop_'ys'has`, `hop_'q`, `hjd_'ys'has`
infixl 6 `hop__`, `hop__'yp`, `hop__'yp'yo'q`, `hop__'ys`, `hop__'ys'has`, `hop__'q`, `hjd__'ys'has`
infixl 5 `lo___`, `lo___'yp`, `lo___'yp'yo'q`, `lo___'ys`, `lo___'ys'has`, `lo___'q`, `hjd___'ys'has`
infixl 4 `lo____`, `lo____'yp`, `lo____'yp'yo'q`, `lo____'ys`, `lo____'ys'has`, `lo____'q`, `hjd____'ys'has`
infixl 3 `lo_____`, `lo_____'yp`, `lo_____'yp'yo'q`, `lo_____'ys`, `lo_____'ys'has`, `lo_____'q`, `hjd_____'ys'has`
infixl 2 `lo______`, `lo______'yp`, `lo______'yp'yo'q`, `lo______'ys`, `lo______'ys'has`, `lo______'q`, `hjd______'ys'has`
infixl 1 `lo_______`, `lo_______'yp`, `lo_______'yp'yo'q`, `lo_______'ys`, `lo_______'ys'has`, `lo_______'q`,  `hjd_______'ys'has`

infixl 8 `has`
infixl 7 `has_`
infixl 6 `has__`
infixl 5 `has___`
infixl 4 `has____`
infixl 3 `has_____`
infixl 2 `has______`
infixl 1 `has_______`

infixl 8 `hjd`, `hjd'yp`, `hjd'yp'yo'q`, `hjd'ys`, `hjd'yp'yp`, `hjd'yw`, `hjd'q`, `hjd's`
infixl 7 `hjd_`, `hjd_'yp`, `hjd_'yp'yo'q`, `hjd_'ys`, `hjd_'yw`, `hjd_'q`, `hjd_'s`
infixl 6 `hjd__`, `hjd__'yp`, `hjd__'yp'yo'q`, `hjd__'ys`, `hjd__'yw`, `hjd__'q`, `hjd__'s`
infixl 5 `hjd___`, `hjd___'yp`, `hjd___'yp'yo'q`, `hjd___'ys`, `hjd___'yw`, `hjd___'q`, `hjd___'s`
infixl 4 `hjd____`, `hjd____'yp`, `hjd____'yp'yo'q`, `hjd____'ys`, `hjd____'yw`, `hjd____'q`, `hjd____'s`

infixl 8 `yv`
infixl 7 `yv_`
infixl 6 `yv__`
infixl 5 `yv___`
infixl 4 `yv____`
infixl 3 `yv_____`
infixl 2 `yv______`
infixl 1 `yv_______`

infixl 8 `yo`, `yo'yp`, `yo'yoo`, `yo'yuu` --, `yo'yok`
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

-- infixl 6 `kyok`

infixl 5 `kyokl`

-- infixl 6 `yiok`

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

infixl 5 `yiokl` --, `yiokl'yokl`
-- infixl 5 `yoikl`, `yoikl'yokl`

infixl 8 `ya`

infixl 8 `yu`
infixl 7 `yu_`
infixl 6 `yu__`
infixl 5 `yu___`
infixl 4 `yu____`
infixl 3 `yu_____`
infixl 2 `yu______`
infixl 1 `yu_______`

infixl 8 `yp`, `yp'yo`, `yp'yo'hd`, `yp'yu`, `yp'yp`, `yp'yp'yo`, `yp'ys` --, `yp'yok`, `yp'yokl` --, `yp'yp'jt`, `yp'yp'jt'yok`
infixl 7 `yp_'yo`-- , `yip`, `yip'yo`, `yip'yp`, `yip'yip`, `yip'yis`

infixl 8 `ys`, `ys'yo`, `ys'yu`
-- infixl 7 `yis`

infixl 8 `yw`, `yw'yo`, `yw'yokl`

infixl 7 `yoi`

infixl 7 `yai` --, `yai'yukl`

infixl 7 `yui` --, `yui'st`

infixl 7 `yio`, `yio'yp` -- , `yio'yokl`, `yio'yukl`, `yio'yokl'yokl`, `yio'yokl'yukl`, `yio'yoikl`

infixl 7 `yiu`, `yiu'st` --, `st'yiu`

-- infixl 6 `yioi`

infixl 9 `q`
infixl 8 `q_`
infixl 7 `q__`
infixl 6 `q___`
infixl 5 `q____`
infixl 4 `q_____`
infixl 3 `q______`
infixl 2 `q_______`
infixl 1 `q________`

infixl 7 `yor`
infixl 7 `ryo`

infixl 6 `yior`, `yoir`, `yoor`

-- TODO: don't oversimplify - designate a functor
-- yv, yv_, yv__, yv___, yv____, yv_____, yv______, yv_______
--  :: forall source target t a o .
--  Precategory target =>
--  Covariant Yoneda Functor source target I =>
--  Elicitable T'II'I target (T'I'II source a o) =>
--  Elicitable T'I'II target (I o) =>
--  target a (target (source a o) o)
-- yv x = super `compose` yoneda @T'I'II @Functor (Identity x) `compose` wrap

-- yv, yv_, yv__, yv___, yv____, yv_____, yv______, yv_______ :: forall t a o .
--  t a `AR______` t a `AR__` o `AR_____` o
-- yv x f = f x

-- yv_ = yv
-- yv__ = yv
-- yv___ = yv
-- yv____ = yv
-- yv_____ = yv
-- yv______ = yv
-- yv_______ = yv

yv, yv_, yv__, yv___, yv____, yv_____, yv______, yv_______
 :: forall source target t a o .
 Covariant Yoneda Functor source target I =>
 (forall e . Covariant Endo Semi Functor target (T'I'II target e)) =>
 (forall e . Contravariant Endo Semi Functor target (T'II'I target e)) =>
 (forall e ee . Wrapper target (T'I'II source e ee)) =>
 (forall e ee . Wrapper target (T'I'II target e ee)) =>
 (forall e ee . Wrapper target (T'II'I target ee e)) =>
 (forall e . Wrapper target (I e)) =>
 target a (target (source a o) o)
yv = fai @target wrap
 `compose` fio @target super
 `compose` yoneda @T'I'II @Functor
 `compose` wrap @target @(I a)

yv_ = yv
yv__ = yv
yv___ = yv
yv____ = yv
yv_____ = yv
yv______ = yv
yv_______ = yv

yo, yo_, yo__, yo___, yo____, yo_____, yo______, yo_______, yi'yo
 :: forall source target t a o .
 Precategory target =>
 (forall e . Contravariant Endo Semi Functor target (T'II'I target e)) =>
 Covariant Yoneda Functor source target t =>
 (forall e ee . Wrapper target (T'I'II source e ee)) =>
 (forall e ee . Wrapper target (T'II'I target e ee)) =>
 target (t a) (target (source a o) (t o))
yo = fai @target wrap `compose` yoneda @T'I'II @Functor

 -- target (t a) (target (source o a) (t o))
-- ya = fai @target wrap `compose` yoneda @T'II'I @Functor

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
 (forall e ee . Wrapper target (T'II'I target e ee)) =>
 (forall e . Contravariant Semi Functor (AR) target (T'II'I target e)) =>
  (forall e . Contravariant Endo Semi Functor target (T'II'I target e)) =>
 target (t (tt a a)) (target (source a o) (t (tt o o)))
yo'yoo = fai (foo @source @source @tt) `compose` yo @source @target

yo'yuu :: forall target t tt a aa o .
 Precategory target =>
 Covariant Yoneda Functor target target (T'I t) =>
 Covariant Functor target target (T'I'II tt a) =>
 Covariant Functor target target (T'II'I tt o) =>
 (forall e . Contravariant Endo Semi Functor target (T'II'I target e)) =>
 (forall e . Contravariant Semi Functor (AR) target (T'II'I target e)) =>
 (forall e ee . Wrapper target (T'I'II tt e ee)) =>
 (forall e ee . Wrapper target (T'II'I tt e ee)) =>
 (forall e ee . Wrapper target (T'I'II target e ee)) =>
 (forall e ee . Wrapper target (T'II'I target e ee)) =>
 (forall e . Wrapper (AR) (target Unit e)) =>
 Terminal target =>
 Contravariant Functor (AR) (AR) (T'II'I target (t (tt o o))) =>
 target (t (tt a aa)) (target (Supertype (target Unit o)) (t (tt o o)))
yo'yuu = fai (fuu @target @target @tt) `compose` yo @target @target

yoo :: forall source target t a o .
 Precategory target =>
 (forall e . Covariant Endo Semi Functor target (T'I'II target e)) =>
 (forall e . Contravariant Endo Semi Functor target (T'II'I target e)) =>
 Covariant Yoneda Functor source target (T'I'I t) =>
 (forall e . Wrapper target (T'I'I t e)) =>
 (forall e ee . Wrapper target (T'I'II source e ee)) =>
 (forall e ee . Wrapper target (T'I'II target e ee)) =>
 (forall e ee . Wrapper target (T'II'I target e ee)) =>
 target (t a a) (target (source a o) (t o o))
yoo = fio @target super `compose` yo @source @target @(T'I'I t) `compose` wrap

yoi
 :: forall source target t i a o .
 Precategory target =>
 (forall e . Covariant Endo Semi Functor target (T'I'II target e)) =>
 (forall e . Contravariant Endo Semi Functor target (T'II'I target e)) =>
 Covariant Yoneda Functor source target (T'II'I t i) =>
 (forall e ee . Wrapper target (T'I'II source e ee)) =>
 (forall e . Wrapper target (T'II'I t i e)) =>
 (forall e ee . Wrapper target (T'I'II target e ee)) =>
 (forall e ee . Wrapper target (T'II'I target e ee)) =>
 target (t a i) (target (source a o) (t o i))
yoi = fio @target super `compose` yo @source @target @(T'II'I t i) `compose` wrap

-- TODO: add Hom functor aliases here
yio, ho, ho_, ho__, ho___, ho____, ho_____, ho______, ho_______, ho________
 :: forall source target t i a o .
 Precategory target =>
 (forall e . Covariant Endo Semi Functor target (T'I'II target e)) =>
 (forall e . Contravariant Endo Semi Functor target (T'II'I target e)) =>
 Covariant Yoneda Functor source target (T'I'II t i) =>
 (forall e ee . Wrapper target (T'I'II source e ee)) =>
 (forall e ee . Wrapper target (T'I'II target e ee)) =>
 (forall e ee . Wrapper target (T'II'I target e ee)) =>
 (forall e . Wrapper target (T'I'II t i e)) =>
 target (t i a) (target (source a o) (t i o))
yio = fio @target super `compose` yo @source @target @(T'I'II t i) `compose` wrap

ho = yio
ho_ = yio
ho__ = yio
ho___ = yio
ho____ = yio
ho_____ = yio
ho______ = yio
ho_______ = yio
ho________ = yio

yio'st, ho'st, ho_'st, ho__'st, ho___'st, ho____'st, ho_____'st, ho______'st, ho_______'st, ho________'st
 :: forall source target t i a o .
 (forall e . Covariant Endo Semi Functor target (T'I'II target e)) =>
 (forall e . Contravariant Endo Semi Functor target (T'II'I target e)) =>
 Covariant Yoneda Functor source target (T'I'II t i) =>
 Contravariant Semi Functor source target (T'II'I source o) =>
 Covariant Semi Functor source target (T'I'II source o) =>
 Wrapper source a =>
 (forall e ee . Wrapper target (T'II'I target e ee)) =>
 (forall e ee . Wrapper target (T'I'II target e ee)) =>
 (forall e ee . Wrapper target (T'I'II source e ee)) =>
 (forall e ee . Wrapper target (T'II'I source e ee)) =>
 (forall e ee . Wrapper target (T'I'II t e ee)) =>
 target (t i a) (target (source (Supertype a) o) (t i o))
yio'st = fai @target (fai @source super) `compose` yio @source @target @t

ho'st = yio'st
ho_'st = yio'st
ho__'st = yio'st
ho___'st = yio'st
ho____'st = yio'st
ho_____'st = yio'st
ho______'st = yio'st
ho_______'st = yio'st
ho________'st = yio'st

-- yioi :: forall source target w e eee a o .
--  Precategory target =>
--  Covariant Yoneda Functor source target (W_III_I_II w eee e) =>
--  Wrapper target (T'I'II source a o) =>
--  Elicitable T'I'II target (W_III_I_II w eee e o) =>
--  w e a eee -> target (source a o) (w e o eee)
-- yioi x = compose super (yoneda @T'I'II @source @target @(W_III_I_II _ _ _) (wrap x))

yu, yu_, yu__, yu___, yu____, yu_____, yu______, yu_______ :: forall target t a o .
 Covariant Yoneda Functor target target t =>
 (forall e . Contravariant Functor target target (T'II'I target e)) =>
 -- Mapping T'I'II T'I'II target target I (T'I'II target a) =>
 Covariant Endo Transformation Functor target I (T'I'II target a) =>
 (forall e ee . Wrapper target (T'I'II target e ee)) =>
 (forall e ee . Wrapper target (T'II'I target e ee)) =>
 (forall e . Wrapper target (I e)) =>
 target (t a) (target o (t o))
yu = fai @target (wrap `compose` constant) `compose` yoneda @T'I'II @Functor @target @target

yu_ = yu
yu__ = yu
yu___ = yu
yu____ = yu
yu_____ = yu
yu______ = yu
yu_______ = yu

yui :: forall target t i a o .
 Terminal target =>
 Category target =>
 Covariant Yoneda Functor target target (T'II'I t i) =>
 Covariant Functor target target (T'I'II target a) =>
 Covariant Endo Transformation Functor target I (T'I'II target Unit) =>
 (forall e . Covariant Endo Semi Functor target (T'I'II target e)) =>
 (forall e . Contravariant Functor target target (T'II'I target e)) =>
 (forall e ee . Wrapper target (T'II'I target e ee)) =>
 (forall e ee . Wrapper target (T'I'II target e ee)) =>
 (forall e . Wrapper target (T'II'I t i e)) =>
 (Supertype (target Unit o) ~ o) =>
 (forall e . Wrapper target (target Unit e)) =>
 (forall e . Wrapper target (I e)) =>
 target (t a i) (target (Supertype (target Unit o)) (t o i))
yui = fai @target (fai @target terminal `compose` constant) `compose` yoi @target

yiu, hu, hu_, hu__, hu___, hu____, hu_____, hu______, hu_______, hu________
 :: forall target t i a o .
 Terminal target =>
 Category target =>
 (forall e . Covariant Endo Semi Functor target (T'I'II target e)) =>
 (forall e . Contravariant Functor target target (T'II'I target e)) =>
 Covariant Yoneda Functor target target (T'I'II t i) =>
 Covariant Functor target target (T'I'II target a) =>
 Contravariant Functor target target (T'II'I target o) =>
 Covariant Endo Transformation Functor target I (T'I'II target Unit) =>
 (forall e . Wrapper target (T'I'II t i e)) =>
 (forall e ee . Wrapper target (T'I'II target e ee)) =>
 (forall e ee . Wrapper target (T'II'I target e ee)) =>
 (forall e . Wrapper target (I e)) =>
 (Supertype (target Unit o) ~ o) =>
 (forall e . Wrapper target (target Unit e)) =>
 target (t i a) (target (Supertype (target Unit o)) (t i o))
yiu = fai @target (fai @target terminal `compose` constant) `compose` yio @target

hu = yiu
hu_ = yiu
hu__ = yiu
hu___ = yiu
hu____ = yiu
hu_____ = yiu
hu______ = yiu
hu_______ = yiu
hu________ = yiu

yiu'st --, hu'st, hu_'st, hu__'st, hu___'st, hu____'st, hu_____'st, hu______'st, hu_______'st, hu________'st
 :: forall target t i a o .
 Terminal target =>
 Category target =>
 (forall e . Covariant Endo Semi Functor target (T'I'II target e)) =>
 (forall e . Contravariant Endo Semi Functor target (T'II'I target e)) =>
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
 target (t i a) (target (Supertype (target Unit o)) (t i (Supertype o)))
yiu'st = fai @target (fio (super @target @o) `compose` fai @target terminal `compose` wrap) `compose` yio @target

hu'st
 :: forall target t i a o .
 Terminal target =>
 Category target =>
 (forall e . Covariant Endo Semi Functor target (T'I'II target e)) =>
 (forall e . Contravariant Endo Semi Functor target (T'II'I target e)) =>
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
 target (t i a) (target (Supertype (target Unit o)) (t i (Supertype o)))
hu'st = fai @target (fio (super @target @o) `compose` fai @target terminal `compose` wrap) `compose` yio @target

hu_'st
 :: forall target t i a o .
 Terminal target =>
 Category target =>
 (forall e . Covariant Endo Semi Functor target (T'I'II target e)) =>
 (forall e . Contravariant Endo Semi Functor target (T'II'I target e)) =>
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
 target (t i a) (target (Supertype (target Unit o)) (t i (Supertype o)))
hu_'st = fai @target (fio (super @target @o) `compose` fai @target terminal `compose` wrap) `compose` yio @target

hu__'st
 :: forall target t i a o .
 Terminal target =>
 Category target =>
 (forall e . Covariant Endo Semi Functor target (T'I'II target e)) =>
 (forall e . Contravariant Endo Semi Functor target (T'II'I target e)) =>
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
 target (t i a) (target (Supertype (target Unit o)) (t i (Supertype o)))
hu__'st = fai @target (fio (super @target @o) `compose` fai @target terminal `compose` wrap) `compose` yio @target

hu___'st
 :: forall target t i a o .
 Terminal target =>
 Category target =>
 (forall e . Covariant Endo Semi Functor target (T'I'II target e)) =>
 (forall e . Contravariant Endo Semi Functor target (T'II'I target e)) =>
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
 target (t i a) (target (Supertype (target Unit o)) (t i (Supertype o)))
hu___'st = fai @target (fio (super @target @o) `compose` fai @target terminal `compose` wrap) `compose` yio @target

hu____'st
 :: forall target t i a o .
 Terminal target =>
 Category target =>
 (forall e . Covariant Endo Semi Functor target (T'I'II target e)) =>
 (forall e . Contravariant Endo Semi Functor target (T'II'I target e)) =>
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
 target (t i a) (target (Supertype (target Unit o)) (t i (Supertype o)))
hu____'st = fai @target (fio (super @target @o) `compose` fai @target terminal `compose` wrap) `compose` yio @target

hu_____'st
 :: forall target t i a o .
 Terminal target =>
 Category target =>
 (forall e . Covariant Endo Semi Functor target (T'I'II target e)) =>
 (forall e . Contravariant Endo Semi Functor target (T'II'I target e)) =>
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
 target (t i a) (target (Supertype (target Unit o)) (t i (Supertype o)))
hu_____'st = fai @target (fio (super @target @o) `compose` fai @target terminal `compose` wrap) `compose` yio @target

hu______'st
 :: forall target t i a o .
 Terminal target =>
 Category target =>
 (forall e . Covariant Endo Semi Functor target (T'I'II target e)) =>
 (forall e . Contravariant Endo Semi Functor target (T'II'I target e)) =>
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
 target (t i a) (target (Supertype (target Unit o)) (t i (Supertype o)))
hu______'st = fai @target (fio (super @target @o) `compose` fai @target terminal `compose` wrap) `compose` yio @target

hu_______'st
 :: forall target t i a o .
 Terminal target =>
 Category target =>
 (forall e . Covariant Endo Semi Functor target (T'I'II target e)) =>
 (forall e . Contravariant Endo Semi Functor target (T'II'I target e)) =>
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
 target (t i a) (target (Supertype (target Unit o)) (t i (Supertype o)))
hu_______'st = fai @target (fio (super @target @o) `compose` fai @target terminal `compose` wrap) `compose` yio @target

hu________'st
 :: forall target t i a o .
 Terminal target =>
 Category target =>
 (forall e . Covariant Endo Semi Functor target (T'I'II target e)) =>
 (forall e . Contravariant Endo Semi Functor target (T'II'I target e)) =>
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
 target (t i a) (target (Supertype (target Unit o)) (t i (Supertype o)))
hu________'st = fai @target (fio (super @target @o) `compose` fai @target terminal `compose` wrap) `compose` yio @target

-- st'yiu, st'hu, st'hu_, st'hu__, st'hu___, st'hu____, st'hu_____, st'hu______, st'hu_______, st'hu________
--  :: forall target t i a o .
--  Terminal target =>
--  Category target =>
--  Covariant Yoneda Functor target target (T'I'II t i) =>
--  Contravariant Functor target (AR) (T'II'I t a) =>
--  Covariant Functor target target (T'I'II target a) =>
--  Contravariant Functor target target (T'II'I target o) =>
--  Wrapper target (target Unit o) =>
--  Wrapper target (Supertype (target Unit o)) =>
--  (forall e ee . Wrapper target (T'I'II target e ee)) =>
--  (forall e ee . Wrapper target (T'II'I target e ee)) =>
--  (forall e . Wrapper target (T'II'I target e Unit)) =>
--  (forall e . Wrapper target (T'I'II t i e)) =>
--  Wrapper target i =>
--  t (Supertype i) a -> target (Supertype (target Unit o)) (t i o)
-- st'yiu x = yio @target (fai @target super x) `compose` fai @target terminal `compose` wrap

-- st'hu = st'yiu
-- st'hu_ = st'yiu
-- st'hu__ = st'yiu
-- st'hu___ = st'yiu
-- st'hu____ = st'yiu
-- st'hu_____ = st'yiu
-- st'hu______ = st'yiu
-- st'hu_______ = st'yiu
-- st'hu________ = st'yiu

ya :: forall source target t a o .
 (forall e . Contravariant Endo Semi Functor target (T'II'I target e)) =>
 Contravariant Yoneda Functor source target t =>
 (forall e ee . Wrapper target (T'II'I source e ee)) =>
 (forall e ee . Wrapper target (T'II'I target e ee)) =>
 target (t a) (target (source o a) (t o))
ya = fai @target wrap `compose` yoneda @T'II'I @Functor

yai, ha, ha_, ha__, ha___, ha____, ha_____, ha______, ha_______, ha________ :: forall source target t i a o .
 (forall e . Covariant Endo Semi Functor target (T'I'II target e)) =>
 (forall e . Contravariant Endo Semi Functor target (T'II'I target e)) =>
 Contravariant Yoneda Functor source target (T'II'I t i) =>
 (forall e ee . Wrapper target (T'II'I source e ee)) =>
 (forall e ee . Wrapper target (T'I'II target e ee)) =>
 (forall e ee . Wrapper target (T'II'I target e ee)) =>
 (forall e ee . Wrapper target (T'II'I t e ee)) =>
 target (t a i) (target (source o a) (t o i))
yai = fio @target super `compose` ya @source @target @(T'II'I t i) `compose` wrap

ha = yai
ha_ = yai
ha__ = yai
ha___ = yai
ha____ = yai
ha_____ = yai
ha______ = yai
ha_______ = yai
ha________ = yai

-- yai'yij :: forall source target t tt ttt i ii iii a o .
--  Precategory target =>
--  Contravariant Functor source (AR) (T'II'I target (t o i)) =>
--  Adjoint Functor source source (T'II'I tt ii) (T'I'II ttt iii) =>
--  Covariant Functor source (AR) (T'I'II target (source (tt ii (t o i)) a)) =>
--  Contravariant Yoneda Functor source target (T'II'I t i) =>
--  Contravariant Endo Semi Functor (AR) (T'II'I target (t o i)) =>
--  (forall e ee . Wrapper target (T'II'I source e ee)) =>
--  (forall e . Wrapper source (I e)) =>
--  (forall e . Wrapper target (T'II'I t i e)) =>
--  (forall e . Wrapper source (T'II'I tt ii e)) =>
--  (forall e . Wrapper source (T'I'II ttt iii e)) =>
--  (forall e . Wrapper source (T'TT'I (T'I'II ttt iii) (T'II'I tt ii) e)) =>
--  t (ttt iii a) i -> target (source (tt o ii) a) (t o i)
-- yai'yij = fai fij `compose` yai @source @target

-- t (ii `AR` a) i -> target ((o `P` ii) `AR` a) (t o i)

-- yai'ydi, ha'hd :: forall source target t tt ttt i ii iii a o .
--  Precategory target =>
--  Contravariant Functor source (AR) (T'II'I target (t o i)) =>
--  Adjoint Functor source source (T'II'I tt ii) (T'I'II ttt iii) =>
--  Covariant Functor source (AR) (T'I'II target (source (tt ii (t o i)) a)) =>
--  Covariant Endo Semi Functor source (T'I'II tt ii) =>
--  Contravariant Yoneda Functor source target (T'II'I t i) =>
--  Contravariant Endo Semi Functor (AR) (T'II'I target (t (tt o ii) i)) =>
--  (forall e ee . Wrapper target (T'II'I source e ee)) =>
--  (forall e . Wrapper source (I e)) =>
--  (forall e . Wrapper target (T'II'I t i e)) =>
--  (forall e . Wrapper source (T'II'I tt ii e)) =>
--  (forall e . Wrapper source (T'I'II ttt iii e)) =>
--  (forall e . Wrapper source (T'TT'I (T'II'I tt ii) (T'I'II ttt iii) e)) =>
--  t a i -> target (source o (ttt iii a)) (t (tt o ii) i)
-- yai'ydi x = fai (fdi @source) (yai @source @target x)

-- t a i `AR__` target (o `AR_` (ii `AR_` a)) (t (o `P` ii) i)

-- ha'hd = yai'ydi

-- yai'ydi'ydi, ha'hd'hd :: forall source target t tt ttt tttt ttttt i ii iii iiii iiiii a o .
--  Precategory target =>
--  Contravariant Functor source (AR) (T'II'I target (t o i)) =>
--  Adjoint Functor source source (T'II'I tt ii) (T'I'II ttt iii) =>
--  Adjoint Functor source source (T'II'I tttt iiii) (T'I'II ttttt iiiii) =>
--  Covariant Functor source (AR) (T'I'II target (source (tt ii (t o i)) a)) =>
--  Covariant Endo Semi Functor source (T'I'II tt ii) =>
--  Covariant Endo Semi Functor source (T'II'I ttt iii) =>
--  Covariant Endo Semi Functor source (T'II'I tttt iiii) =>
--  Covariant Endo Semi Functor source (T'I'II ttttt iiiii) =>
--  Contravariant Yoneda Functor source target (T'II'I t i) =>
--  Contravariant Endo Semi Functor (AR) (T'II'I target (t (tttt (tt o ii) iiii) i)) =>
--  (forall e ee . Wrapper target (T'II'I source e ee)) =>
--  (forall e . Wrapper source (I e)) =>
--  (forall e . Wrapper target (T'II'I t i e)) =>
--  (forall e . Wrapper source (T'II'I tt ii e)) =>
--  (forall e . Wrapper source (T'I'II ttt iii e)) =>
--  (forall e . Wrapper source (T'II'I tttt iiii e)) =>
--  (forall e . Wrapper source (T'I'II ttttt iiiii e)) =>
--  (forall e . Wrapper source (T'TT'I (T'II'I tt ii) (T'I'II ttt iii) e)) =>
--  (forall e . Wrapper source (T'TT'I (T'II'I tttt iiii) (T'I'II ttttt iiiii) e)) =>
--  t a i -> target (source o (ttt iii (ttttt iiiii a))) (t (tttt (tt o ii) iiii) i)
-- yai'ydi'ydi x = fai (fdi @source `compose` fdi @source) (yai @source @target x)

-- ha'hd'hd = yai'ydi'ydi

-- yio'ydi, ho'hd, ho_'hd, ho__'hd, ho___'hd, ho____'hd, ho_____'hd, ho______'hd, ho_______'hd, ho________'hd
--  :: forall source target t tt ttt i ii iii a o .
--  Precategory target =>
--  Contravariant Endo Semi Functor (AR) (T'II'I target (t o i)) =>
--  Adjoint Functor source source (T'II'I tt ii) (T'I'II ttt iii) =>
--  Covariant Functor source (AR) (T'I'II target (source (ttt iii (t o i)) a)) =>
--  Covariant Yoneda Functor source target (T'I'II t i) =>
--  Covariant Endo Semi Functor source (T'II'I tt ii) =>
--  Covariant Endo Semi Functor source (T'I'II ttt iii) =>
--  Contravariant Endo Semi Functor (AR) (T'II'I target (t i o)) =>
--  (forall e ee . Wrapper target (T'I'II source e ee)) =>
--  (forall e . Wrapper source (I e)) =>
--  (forall e . Wrapper target (T'I'II t i e)) =>
--  (forall e . Wrapper source (T'I'II ttt iii e)) =>
--  (forall e . Wrapper source (T'II'I tt ii e)) =>
--  (forall e . Wrapper source (T'TT'I (T'II'I tt ii) (T'I'II ttt iii) e)) =>
--  t i (tt a ii) -> target (source a (ttt iii o)) (t i o)
-- yio'ydi x = fai fdi (yio @source @target x)

-- ho'hd = yio'ydi
-- ho_'hd = yio'ydi
-- ho__'hd = yio'ydi
-- ho___'hd = yio'ydi
-- ho____'hd = yio'ydi
-- ho_____'hd = yio'ydi
-- ho______'hd = yio'ydi
-- ho_______'hd = yio'ydi
-- ho________'hd = yio'ydi

-- yio'ydi'ydi, ho'hd'hd :: forall source target t tt ttt tttt ttttt i ii iii iiii iiiii a o .
--  Precategory target =>
--  Contravariant Endo Semi Functor (AR) (T'II'I target (t o i)) =>
--  Adjoint Functor source source (T'II'I tt ii) (T'I'II ttt iii) =>
--  Adjoint Functor source source (T'II'I tttt iiii) (T'I'II ttttt iiiii) =>
--  Covariant Functor source (AR) (T'I'II target (source (ttt iii (t o i)) a)) =>
--  Covariant Yoneda Functor source target (T'I'II t i) =>
--  Covariant Endo Semi Functor source (T'II'I tt ii) =>
--  Covariant Endo Semi Functor source (T'I'II ttt iii) =>
--  Covariant Endo Semi Functor source (T'II'I tttt iii) =>
--  Contravariant Endo Semi Functor (AR) (T'II'I target (t i o)) =>
--  (forall e ee . Wrapper target (T'I'II source e ee)) =>
--  (forall e . Wrapper source (I e)) =>
--  (forall e . Wrapper target (T'I'II t i e)) =>
--  (forall e . Wrapper source (T'I'II ttt iii e)) =>
--  (forall e . Wrapper source (T'II'I tt ii e)) =>
--  (forall e . Wrapper source (T'II'I tttt iiii e)) =>
--  (forall e . Wrapper source (T'I'II ttttt iiiii e)) =>
--  (forall e . Wrapper source (T'TT'I (T'II'I tt ii) (T'I'II ttt iii) e)) =>
--  (forall e . Wrapper source (T'TT'I (T'II'I tttt iiii) (T'I'II ttttt iiiii) e)) => 
--  t i (tt (tttt a iiii) ii) -> target (source a (ttttt iiiii (ttt iii o))) (t i o)
-- yio'ydi'ydi x = fai (fdi @source `compose` fdi @source) (yio @source @target x)

-- ho'hd'hd = yio'ydi'ydi

-- yio'yij, ho'hj :: forall source target t tt ttt i ii iii a o .
--  Precategory target =>
--  Contravariant Endo Semi Functor (AR) (T'II'I target (t o i)) =>
--  Adjoint Functor source source (T'II'I tt ii) (T'I'II ttt iii) =>
--  Covariant Functor source (AR) (T'I'II target (source (ttt iii (t o i)) a)) =>
--  Covariant Yoneda Functor source target (T'I'II t i) =>
--  Covariant Endo Semi Functor source (T'II'I tt ii) =>
--  Covariant Endo Semi Functor source (T'I'II ttt iii) =>
--  Contravariant Endo Semi Functor (AR) (T'II'I target (t i (ttt iii o))) =>
--  (forall e ee . Wrapper target (T'I'II source e ee)) =>
--  (forall e . Wrapper source (I e)) =>
--  (forall e . Wrapper target (T'I'II t i e)) =>
--  (forall e . Wrapper source (T'I'II ttt iii e)) =>
--  (forall e . Wrapper source (T'II'I tt ii e)) =>
--  (forall e . Wrapper source (T'TT'I (T'I'II ttt iii) (T'II'I tt ii) e)) =>
--  t i a -> target (source (tt a ii) o) (t i (ttt iii o))
-- yio'yij x = fai fij (yio @source @target x)

-- -- t i a -> target (source (a `P` ii) o) (t i (ii `AR` o))


-- ho'hj = yio'yij

-- yio'yij'yij, ho'hj'hj :: forall source target t tt ttt tttt ttttt i ii iii iiii iiiii a o .
--  Precategory target =>
--  Contravariant Endo Semi Functor (AR) (T'II'I target (t o i)) =>
--  Adjoint Functor source source (T'II'I tt ii) (T'I'II ttt iii) =>
--  Adjoint Functor source source (T'II'I tttt iiii) (T'I'II ttttt iiiii) =>
--  Covariant Functor source (AR) (T'I'II target (source (ttt iii (t o i)) a)) =>
--  Covariant Yoneda Functor source target (T'I'II t i) =>
--  Covariant Endo Semi Functor source (T'II'I tt ii) =>
--  Covariant Endo Semi Functor source (T'I'II ttt iii) =>
--  Contravariant Endo Semi Functor (AR) (T'II'I target (t i (ttttt iiiii (ttt iii o)))) =>
--  (forall e ee . Wrapper target (T'I'II source e ee)) =>
--  (forall e . Wrapper source (I e)) =>
--  (forall e . Wrapper target (T'I'II t i e)) =>
--  (forall e . Wrapper source (T'II'I tt ii e)) =>
--  (forall e . Wrapper source (T'I'II ttt iii e)) =>
--  (forall e . Wrapper source (T'II'I tttt iiii e)) =>
--  (forall e . Wrapper source (T'I'II ttttt iiiii e)) =>
--  (forall e . Wrapper source (T'TT'I (T'I'II ttt iii) (T'II'I tt ii) e)) =>
--  (forall e . Wrapper source (T'TT'I (T'I'II ttttt iiiii) (T'II'I tttt iiii) e)) =>
--  t i a -> target (source (tt (tttt a iiii) ii) o) (t i (ttttt iiiii (ttt iii o)))
-- yio'yij'yij = fai (fij @source `compose` fij @source) `compose` yio @source @target

-- ho'hj'hj = yio'yij'yij

yia :: forall source target t i a o .
 Precategory target =>
 (forall e . Contravariant Endo Semi Functor target (T'II'I target e)) =>
 (forall e . Covariant Endo Semi Functor target (T'I'II target e)) =>
 Contravariant Yoneda Functor source target (T'I'II t i) =>
 (forall e ee . Wrapper target (T'II'I source e ee)) =>
 (forall e ee . Wrapper target (T'II'I target e ee)) =>
 (forall e ee . Wrapper target (T'I'II target e ee)) =>
 (forall e ee . Wrapper target (T'I'II t e ee)) =>
 target (t i a) (target (source o a) (t i o))
yia = fio @target super `compose` ya @source @target @(T'I'II t i) `compose` wrap

yok, yok_, yok__, yok___, yok____, yok_____, yok______
 :: forall source target t tt ll a o .
 Covariant Endo Transformation Functor target (t `T'TT'I` tt `L` tt `T` ll) t =>
 Covariant Yoneda Functor source target t =>
 (forall e . Covariant Endo Semi Functor target (T'I'II target e)) =>
 (forall e . Contravariant Endo Semi Functor target (T'II'I target e)) =>
 (forall e ee . Wrapper target (T'I'II source e ee)) =>
 (forall e . Wrapper target (t `T'TT'I` tt `L` tt `T` ll `T'I_` e)) =>
 (forall e ee . Wrapper target (T'I'II target e ee)) =>
 (forall e ee . Wrapper target (T'II'I target e ee)) =>
 target (t a) (target (source a (tt `L` tt `T` ll `T` o)) (t o))
yok = fio (component @target @(T'TT'I t (tt `L` tt `T` ll)) `compose` wrap @target @(T'TT'I t (tt `L` tt `T` ll) _))
 `compose` yo

yok_ = yok
yok__ = yok
yok___ = yok
yok____ = yok
yok_____ = yok
yok______ = yok

-- yok'st, yok_'st, yok__'st, yok___'st, yok____'st, yok_____'st, yok______'st
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
-- yok'st x = yok @source @target x `compose` fai @source super

-- yok_'st = yok'st
-- yok__'st = yok'st
-- yok___'st = yok'st
-- yok____'st = yok'st
-- yok_____'st = yok'st
-- yok______'st = yok'st

-- yok'st'st, yok_'st'st, yok__'st'st, yok___'st'st, yok____'st'st, yok_____'st'st, yok______'st'st
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
-- yok'st'st x = yok @source @target x `compose` fai @source super'st

-- yok_'st'st = yok'st'st
-- yok__'st'st = yok'st'st
-- yok___'st'st = yok'st'st
-- yok____'st'st = yok'st'st
-- yok_____'st'st = yok'st'st
-- yok______'st'st = yok'st'st

yuk, yuk_, yuk__, yuk___, yuk____, yuk_____, yuk______, yi'yuk
 :: forall target tt t ll a o .
 (forall e . Contravariant Endo Semi Functor target (T'II'I target e)) =>
 (forall e . Covariant Endo Semi Functor target (T'I'II target e)) =>
 Covariant Yoneda Functor target target t =>
 Covariant Endo Transformation Functor target (T'TT'I t (tt `L` tt `T` ll)) t =>
 Covariant Endo Transformation Functor target I (T'I'II target a) =>
 (forall e . Wrapper target ((t `T'TT'I` tt `L` tt `T` ll) e)) =>
 (forall e ee . Wrapper target (T'I'II target e ee)) =>
 (forall e ee . Wrapper target (T'II'I target e ee)) =>
 (forall e . Wrapper target (I e)) =>
 target (t a) (target (tt `L` tt `T` ll `T` o) (t o))
yuk = fio (component @target @(T'TT'I t (tt `L` tt `T` ll)) `compose` wrap @target @(T'TT'I t (tt `L` tt `T` ll) _)) `compose` yu

yuk_ = yuk @target @tt
yuk__ = yuk @target @tt
yuk___ = yuk @target @tt
yuk____ = yuk @target @tt
yuk_____ = yuk @target @tt
yuk______ = yuk @target @tt
yi'yuk = yuk @target @tt

kyo :: forall source target t tt ll a o .
 Component target t (t `T'TT'I` tt `L` tt `T` ll) =>
 Covariant Yoneda Functor source target t =>
 -- (forall e . Covariant Functor source target (T'I'II source e)) =>
 -- (forall e . Contravariant Functor source target (T'II'I source e)) =>
 (forall e . Contravariant Endo Semi Functor target (T'II'I target e)) =>
 (forall e . Contravariant Semi Functor source target (T'II'I source e)) =>
 (forall e . Covariant Semi Functor source target (T'I'II source e)) =>
 (forall e ee . Wrapper target (T'I'II source e ee)) =>
 (forall e ee . Wrapper target (T'II'I source e ee)) =>
 (forall e ee . Wrapper target (T'II'I target e ee)) =>
 (forall e . Wrapper source (I e)) =>
 (forall e . Wrapper source (I `L` tt `T` ll `T'I` e)) =>
 (forall e . Wrapper source (tt `L` tt `T` ll `T'I` e)) =>
 (forall e . Wrapper target (t `T'TT'I` tt `L` tt `T` ll `T'I_` e)) =>
 target (t a) (target (source (tt a) (I `L` tt `T` ll `T` o)) (t o))
kyo = fai @target (fai @source super `compose` fio @source (super @_ @(I _) `compose` super))
 `compose` yo @source @target @t
 `compose` super `compose` component @target @t @(t `T'TT'I` tt `L` tt `T` ll)

-- kyo x = fai @target (fai @source super `compose` fio @source (super @_ @(I _) `compose` super))
--  `compose` yo @source @target @t
--  `compose` super (component @(AR) @t @(t `T'TT'I` tt `L` tt `T` ll) x)

-- kyok :: forall source target t tt ttt l ll lll a o .
--  Covariant Yoneda Functor source target t =>
--  Component (AR) t (t `T'TT'I` tt `L` tt `T` ll) =>
--  Component source (t `T'TT'I` ttt `L` ttt `T` lll) t =>
--  (forall e . Contravariant Functor source target (T'II'I source e)) =>
--  (forall e . Covariant Functor source target (T'I'II source e)) =>
--  (forall e . Covariant Functor source (AR) (T'I'II target e)) =>
--  (forall e ee . Wrapper target (T'I'II source e ee)) =>
--  (forall e ee . Wrapper target (T'II'I source e ee)) =>
--  (forall e . Wrapper source (I `L` tt `T` ll `T` e)) =>
--  (forall e . Wrapper source (tt `L` tt `T` ll `T` e)) =>
--  (forall e . Wrapper source (t `TT'T'I` ttt `T'I_` e)) =>
--  (forall e . Wrapper source (t `T'TT'I` ttt `L` ttt `T` lll `T'I_` e)) =>
--  (forall e . Wrapper source (I e)) =>
--  t a -> target (source (tt a) (I `L` tt `T` ll `T'I` ttt `L` ttt `T` lll `T` o)) (t o)
-- kyok = fio @source (component @source @(t `T'TT'I` ttt `L` ttt `T` lll) @t `compose` wrap)
--  `compose` kyo @source @target @t @tt @ll

kyokl :: forall source target t tt ttt l ll lll a o .
 Covariant Yoneda Functor source target t =>
 Component target t (t `T'TT'I` tt `L` tt `T` ll) =>
 Component source (t `T'TT'I` ttt `L` ttt `T` lll `L` t `T` l) (t `TT'T'I` ttt) =>
 (forall e . Contravariant Functor source target (T'II'I source e)) =>
 (forall e . Contravariant Endo Semi Functor target (T'II'I target e)) =>
 (forall e . Covariant Functor source target (T'I'II target e)) =>
 (forall e . Covariant Functor source target (T'I'II source e)) =>
 (forall e . Covariant Functor source (AR) (T'I'II target e)) =>
 (forall e ee . Wrapper target (T'I'II source e ee)) =>
 (forall e ee . Wrapper target (T'II'I source e ee)) =>
 (forall e . Wrapper source (I `L` tt `T` ll `T` e)) =>
 (forall e . Wrapper source (tt `L` tt `T` ll `T` e)) =>
 (forall e . Wrapper source (t `TT'T'I` ttt `T'I_` e)) =>
 (forall e . Wrapper source (t `T'TT'I` ttt `L` ttt `T` lll `L` t `T` l `T'I_` e)) =>
 (forall e . Wrapper target (t `T'TT'I` tt `L` tt `T` ll `T'I_` e)) =>
 (forall e . Wrapper source (I e)) =>
 (forall e ee . Wrapper target (T'II'I target e ee)) =>
 (forall e ee . Wrapper target (T'I'II target e ee)) =>
 target (t a) (target (source (tt a) (I `L` tt `T` ll `T'I` ttt `L` ttt `T` lll `L` t `T` l `T` o)) (ttt (t o)))
kyokl = fio @source (wrapped (component @source @(t `T'TT'I` ttt `L` ttt `T` lll `L` t `T` l) @(t `TT'T'I` ttt)))
 `compose` kyo @source @target @t @tt @ll

-- TODO: Let's define ha'kyo first...

-- ha'kyokl :: forall source target t tt ttt tttt ll lll llll i a o .
--  Covariant Yoneda Functor source target tt =>
--  Component (AR) tt (tt `T'TT'I` ttt `L` ttt `T` lll) =>
--  Component source (tt `T'TT'I` tttt `L` tttt `T` llll `L` tt `T` ll) (tt `TT'T'I` tttt) =>
--  (forall e . Contravariant Functor source target (T'II'I source e)) =>
--  (forall e . Covariant Functor source target (T'I'II source e)) =>
--  (forall e . Covariant Functor source (AR) (T'I'II target e)) =>
--  (forall e ee . Wrapper target (T'I'II source e ee)) =>
--  (forall e ee . Wrapper target (T'II'I source e ee)) =>
--  (forall e . Wrapper source (I `L` ttt `T` lll `T` e)) =>
--  (forall e . Wrapper source (ttt `L` ttt `T` lll `T` e)) =>
--  (forall e . Wrapper source (tt `TT'T'I` tttt `T'I_` e)) =>
--  (forall e . Wrapper source (tt `T'TT'I` tttt `L` tttt `T` llll `L` tt `T` ll `T'I_` e)) =>
--  (forall e . Wrapper source (I e)) =>
--  t (tt o) i -> target
--   (source (ttt `L` ttt `T` lll `T` a) (tttt `L` tttt `T` llll `L` tt `T` ll `T` o))
--   (t ((tttt (tt a))) i)
-- ha'kyokl = fai (kfokl @source) `compose` ha @source @target @t

-- ha'yok = fai fok `compose` ha @source @target @t

-- fai wrap `compose` fio (wrap `compose` wrap)

-- t (tt a) i `AR___` target (source o a) (t ((tttt (tt o))) i)

-- fio (wrap `compose` wrap) `compose` fai wrap `compose`
-- kfokl `compose` fai wrap `compose` fio (wrap `compose` wrap)

-- kfokl: source (ttt `L` ttt `T` lll `T` a) (tt `L` tt `T` ll `L` t `T` l `T` o) -> target (t a) (tt (t o))
-- ha'yuk = fai fuk `compose` ha @(AR) @u

yokl, yokl_, yokl__, yokl___, yokl____, yokl_____, li'yokl ::
 forall source target t tt l ll a o .
 Covariant Endo Transformation Functor target (t `T'TT'I` tt `L` tt `T` ll `L` t `T` l) (t `TT'T'I` tt) =>
 Covariant Yoneda Functor source target t =>
 (forall e . Covariant Endo Semi Functor target (T'I'II target e)) =>
 (forall e . Contravariant Endo Semi Functor target (T'II'I target e)) =>
 (forall i . Wrapper target (t `T'TT'I` tt `L` tt `T` ll `L` t `T` l `T'I_` i)) =>
 (forall i . Wrapper target ((t `TT'T'I` tt) i)) =>
 (forall e ee . Wrapper target (T'I'II source e ee)) =>
 (forall e ee . Wrapper target (T'I'II target e ee)) =>
 (forall e ee . Wrapper target (T'II'I target e ee)) =>
 target (t a) (target (source a (tt `L` tt `T` ll `L` t `T` l `T` o)) (tt (t o)))
yokl = fio (wrapped @target (component @target @(t `T'TT'I` tt `L` tt `T` ll `L` t `T` l) @(t `TT'T'I` tt))) `compose` yo

yokl_ = yokl
yokl__ = yokl
yokl___ = yokl
yokl____ = yokl
yokl_____ = yokl

li'yokl = yokl

yukl, yukl_, yukl__, yukl___, yukl____, yukl_____
 :: forall target t tt l ll a o .
 Category target =>
 Covariant Endo Transformation Functor target I (T'I'II target a) =>
 Covariant Endo Transformation Functor target (t `T'TT'I` tt `L` tt `T` ll `L` t `T` l) (t `TT'T'I` tt) =>
 -- Component target I (T'I'II target a) =>
 Covariant Yoneda Functor target target t =>
 (forall e . Covariant Endo Semi Functor target (T'I'II target e)) =>
 (forall e . Contravariant Endo Semi Functor target (T'II'I target e)) =>
 (forall i . Wrapper target ((t `T'TT'I` tt `L` tt `T` ll `L` t `T` l) i)) =>
 (forall i . Wrapper target ((t `TT'T'I` tt) i)) =>
 (forall i ii . Wrapper target (T'I'II target i (tt `L` tt `T` ll `L` t `T` l `T` ii))) =>
 (forall i ii . Wrapper target (T'I'II target ((tt `L` tt `T` ll) i) ii)) =>
 (forall i ii . Wrapper target (T'II'I target (tt `L` tt `T` ll `L` t `T` l `T` i) ii)) =>
 -- (forall e . Wrapper target (I (tt `L` tt `T` ll `L` t `T` l `T` e))) =>
 (forall e ee . Wrapper target (T'I'II target e ee)) =>
 (forall e ee . Wrapper target (T'II'I target e ee)) =>
 (forall e . Wrapper target (I e)) =>
 target (t a) (target (tt `L` tt `T` ll `L` t `T` l `T` o) (tt (t o)))
yukl = fio (wrapped @target (component @target @(t `T'TT'I` tt `L` tt `T` ll `L` t `T` l) @(t `TT'T'I` tt))) `compose` yu

yukl_ = yukl
yukl__ = yukl
yukl___ = yukl
yukl____ = yukl
yukl_____ = yukl

yiokl :: forall source target t tt l ll a o i .
 Category target =>
 Covariant Endo Transformation Functor target (T'I'II t i `T'TT'I` tt `L` tt `T` ll `L` T'I'II t i `T` l) (T'I'II t i `TT'T'I` tt) =>
 Covariant Yoneda Functor source target (T'I'II t i) =>
 Covariant Functor source target tt =>
 (forall e . Covariant Endo Semi Functor target (T'I'II target e)) =>
 (forall e . Contravariant Endo Semi Functor target (T'II'I target e)) =>
 (forall e . Wrapper target (T'I'II t i `T'TT'I` tt `L` tt `T` ll `L` T'I'II t i `T` l `T'I_` e)) =>
 (forall e . Wrapper target (T'I'II t i `TT'T'I` tt `T'I_` e)) =>
 (forall e . Wrapper source (T'I'II t i e)) =>
 (forall e . Wrapper target (T'I'II t i e)) =>
 (forall e ee . Wrapper target (T'II'I target e ee)) =>
 (forall e ee . Wrapper target (T'I'II target e ee)) =>
 (forall e ee . Wrapper target (T'I'II source e ee)) =>
 target (t i a) (target (source a (tt `L` tt `T` ll `L` T'I'II t i `T` l `T'I` o)) (tt (t i o)))
yiokl = fio (fo @source super `compose` wrapped @target (component @target @(T'I'II t i `T'TT'I` tt `L` tt `T` ll `L` T'I'II t i `T` l) @(T'I'II t i `TT'T'I` tt)))
 `compose` yo
 `compose` wrap

-- yiokl'yokl :: forall source target t tt ttt l ll lll a o i .
--  Covariant Yoneda Functor source target (T'I'II t i) =>
--  Covariant Endo Semi Functor source tt =>
--  Covariant Functor source target ttt =>
--  Covariant Endo Transformation Functor target (T'I'II t i `T'TT'I` ttt `L` ttt `T` lll `L` T'I'II t i `T` l) (T'I'II t i `TT'T'I` ttt) =>
--  Covariant Endo Transformation Functor source (tt `T'TT'I` ttt `L` ttt `T` lll `L` tt `T` ll) (tt `TT'T'I` ttt) =>
--  Contravariant Endo Semi Functor (AR) (T'II'I target (ttt (t i (tt o)))) =>
--  (forall e . Wrapper source (ttt `L` ttt `T` lll `L` T'I'II t i `T` l `T` e)) =>
--  (forall e . Wrapper source (ttt `L` ttt `T` lll `L` tt `T` ll `L` T'I'II t i `T` l `T` e)) =>
--  (forall e . Wrapper source (TT'T'I tt (ttt `L` ttt `T` lll) e)) =>
--  (forall e . Wrapper source (T'I'II t i e)) =>
--  (forall e . Wrapper source (ttt `L` ttt `T` lll `T` e)) =>
--  (forall e . Wrapper source (ttt `L` ttt `T` lll `L` tt `T` ll `T` e)) =>
--  (forall e . Wrapper source (T'TT'I tt (ttt `L` ttt `T` lll `L` tt `T` ll) e)) =>
--  (forall e . Wrapper target (ttt `L` ttt `T` lll `T` e)) =>
--  (forall e . Wrapper target (ttt `L` ttt `T` lll `L` T'I'II t i `T` l `T` e)) =>
--  (forall e . Wrapper target (ttt `L` ttt `T` lll `L` T'I'II t i `T` l `T` e)) =>
--  (forall e . Wrapper target (T'I'II t i `T'TT'I` ttt `L` ttt `T` lll `L` T'I'II t i `T` l `T'I_` e)) =>
--  (forall e . Wrapper target (T'I'II t i `TT'T'I` ttt `L` ttt `T` lll `L` T'I'II t i `T` l `T'I_` e)) =>
--  (forall e . Wrapper target (T'TT'I (T'I'II t i) ttt e)) =>
--  (forall e . Wrapper target (TT'T'I (T'I'II t i) ttt e)) =>
--  (forall e . Wrapper source (TT'T'I tt ttt e)) =>
--  (forall e ee . Wrapper target (T'I'II source e ee)) =>
--  t i (tt a) -> target (source a (ttt `L` ttt `T` lll `L` tt `T` ll `L` T'I'II t i `T` l `T` o)) (ttt (t i (tt o)))
-- yiokl'yokl x = fai
--  (fio @source (wrap `compose` wrap)
--   `compose` fokl @source @source @tt @ttt @ll @lll
--   `compose` fio @source super
--  )
--  (yiokl @source @target @t @ttt @l @lll @(tt a) @(tt o) x)

-- yoikl :: forall source target t tt l ll a o i .
--  Category target =>
--  Covariant Endo Transformation Functor target (T'II'I t i `T'TT'I` tt `L` tt `T` ll `L` t `T` l) (T'II'I t i `TT'T'I` tt) =>
--  Covariant Yoneda Functor source target (T'II'I t i) =>
--  Covariant Functor source target tt =>
--  (forall e . Wrapper target (T'II'I t i `T'TT'I` tt `L` tt `T` ll `L` t `T` l `T'I_` e)) =>
--  (forall e . Wrapper target (T'II'I t i `TT'T'I` tt `T'I_` e)) =>
--  (forall e . Wrapper source (T'II'I t i e)) =>
--  (forall e ee . Wrapper target (T'I'II source e ee)) =>
--  t a i -> target (source a (tt `L` tt `T` ll `L` t `T` l `T'I` o)) (tt (t o i))
-- yoikl x = fo @source super
--  `compose` super @target @(TT'T'I (T'II'I t i) tt _)
--  `compose` component @target @(T'II'I t i `T'TT'I` tt `L` tt `T` ll `L` t `T` l) @(T'II'I t i `TT'T'I` tt)
--  `compose` wrap @target @((T'II'I t i `T'TT'I` tt `L` tt `T` ll `L` t `T` l) _)
--  `compose` yo (wrap x)

-- yoikl'yokl :: forall source target t tt ttt l ll lll a o i .
--  Covariant Yoneda Functor source target (T'II'I t i) =>
--  Covariant Endo Semi Functor source tt =>
--  Covariant Functor source target ttt =>
--  Covariant Endo Transformation Functor target (T'II'I t i `T'TT'I` ttt `L` ttt `T` lll `L` t `T` l) (T'II'I t i `TT'T'I` ttt) =>
--  Covariant Endo Transformation Functor source (tt `T'TT'I` ttt `L` ttt `T` lll `L` tt `T` ll) (tt `TT'T'I` ttt) =>
--  Contravariant Endo Semi Functor (AR) (T'II'I target (ttt (t (tt o) i))) =>
--  (forall e . Wrapper source (ttt `L` ttt `T` lll `L` t `T` l `T` e)) =>
--  (forall e . Wrapper source (ttt `L` ttt `T` lll `L` tt `T` ll `L` t `T` l `T` e)) =>
--  (forall e . Wrapper source (TT'T'I tt (ttt `L` ttt `T` lll) e)) =>
--  (forall e . Wrapper source (T'II'I t i e)) =>
--  (forall e . Wrapper source (ttt `L` ttt `T` lll `T` e)) =>
--  (forall e . Wrapper source (ttt `L` ttt `T` lll `L` tt `T` ll `T` e)) =>
--  (forall e . Wrapper source (T'TT'I tt (ttt `L` ttt `T` lll `L` tt `T` ll) e)) =>
--  (forall e . Wrapper target (ttt `L` ttt `T` lll `T` e)) =>
--  (forall e . Wrapper target (ttt `L` ttt `T` lll `L` t `T` l `T` e)) =>
--  (forall e . Wrapper target (ttt `L` ttt `T` lll `L` t `T` l `T` e)) =>
--  (forall e . Wrapper target (T'II'I t i `T'TT'I` ttt `L` ttt `T` lll `L` t `T` l `T'I_` e)) =>
--  (forall e . Wrapper target (T'II'I t i `TT'T'I` ttt `L` ttt `T` lll `L` t `T` l `T'I_` e)) =>
--  (forall e . Wrapper target (T'TT'I (T'II'I t i) ttt e)) =>
--  (forall e . Wrapper target (TT'T'I (T'II'I t i) ttt e)) =>
--  (forall e . Wrapper source (TT'T'I tt ttt e)) =>
--  (forall e ee . Wrapper target (T'I'II source e ee)) =>
--  t (tt a) i -> target (source a (ttt `L` ttt `T` lll `L` tt `T` ll `L` t `T` l `T` o)) (ttt (t (tt o) i))
-- yoikl'yokl x = fai
--  (fio @source (wrap `compose` wrap)
--   `compose` fokl @source @source @tt @ttt @ll @lll
--   `compose` fio @source super
--  )
--  (yoikl @source @target @t @ttt @l @lll @(tt a) @(tt o) x)

-- -- TODO: hasbeling
-- yiok :: forall source target tt t i a o .
--  Category target =>
--  Component target (T'I'II t i `T'TT'I` tt) (T'I'II t i) =>
--  Covariant Yoneda Functor source target (T'I'II t i) =>
--  (forall e ee . Wrapper target (T'I'II source e ee)) =>
--  Elicitable T'I'II target (T'I'II t i o) =>
--  Elicitable T'II'I target (T'TT'I (T'I'II t i) tt o) =>
--  t i a -> target (source a (tt o)) (t i o)
-- yiok x = super @target @(T'I'II t i o)
--  `compose` component @target @(T'TT'I (T'I'II t i) tt)
--  `compose` wrap @target @(T'TT'I (T'I'II t i) tt _)
--  `compose` yo (T'I'II x)

-- TODO: yok'yo
-- TODO: yok'st'yo

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
--  (yok @source @target @t @tt @ll x `compose` fio (super @target @()))

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
 (forall e . Contravariant Semi Functor (AR) target (T'II'I target e)) =>
 (forall e . Covariant Endo Semi Functor target (T'I'II target e)) =>
 (forall e . Contravariant Endo Semi Functor target (T'II'I target e)) =>
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
 (forall e ee . Wrapper target (T'II'I target e ee)) =>
 (forall e ee . Wrapper target (T'I'II target e ee)) =>
 target (t (tt a)) (target (source a (ttt `L` ttt `T` lll `L` tt `T` ll `L` t `T` l `T` o)) (ttt (t (tt o))))
yokl'yokl = fai
 (fio @source (wrap `compose` wrap)
  `compose` fokl @source @source @tt @ttt @ll @lll
  `compose` fio @source super
 )
 `compose` yokl @source @target @t @ttt @l @lll @(tt a) @(tt o)

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

ho'st'st, ho_'st'st, ho__'st'st, ho___'st'st, ho____'st'st, ho_____'st'st, ho______'st'st, ho_______'st'st, ho________'st'st
 :: forall source target u i a o .
 (forall e . Covariant Endo Semi Functor target (T'I'II target e)) =>
 (forall e . Contravariant Endo Semi Functor target (T'II'I target e)) =>
 Covariant Yoneda Functor source target (T'I'II u i) =>
 Contravariant Semi Functor source target (T'II'I source o) =>
 Covariant Semi Functor source target (T'I'II source o) =>
 Wrapper source a =>
 Wrapper source (Supertype a) =>
 (forall e . Wrapper target (T'I'II u i e)) =>
 (forall e ee . Wrapper target (T'I'II source e ee)) =>
 (forall e ee . Wrapper target (T'II'I source e ee)) =>
 (forall e ee . Wrapper target (T'I'II target e ee)) =>
 (forall e ee . Wrapper target (T'II'I target e ee)) =>
 Wrapper target (T'II'I source o (Supertype a)) =>
 Wrapper target (T'II'I source o (Supertype (Supertype a))) =>
 target (u i a) (target (source (Supertype (Supertype a)) o) (u i o))
ho'st'st = fai @target (fai @source (super `compose` super)) `compose` yio @source @target @u

ho_'st'st = ho'st'st
ho__'st'st = ho'st'st
ho___'st'st = ho'st'st
ho____'st'st = ho'st'st
ho_____'st'st = ho'st'st
ho______'st'st = ho'st'st
ho_______'st'st = ho'st'st
ho________'st'st = ho'st'st

-- ho'st'st'st, ho_'st'st'st, ho__'st'st'st, ho___'st'st'st, ho____'st'st'st, ho_____'st'st'st, ho______'st'st'st, ho_______'st'st'st, ho________'st'st'st
--  :: forall source target u i a o .
--  Precategory source =>
--  Precategory target =>
--  Covariant Yoneda Functor source target (T'I'II u i) =>
--  Contravariant Semi Functor source target (T'II'I source o) =>
--  Covariant Semi Functor source target (T'I'II source o) =>
--  Wrapper source a =>
--  Wrapper source (Supertype a) =>
--  Wrapper source (Supertype (Supertype a)) =>
--  (forall e . Wrapper target (T'I'II u i e)) =>
--  (forall e ee . Wrapper target (T'I'II source e ee)) =>
--  (forall e ee . Wrapper target (T'II'I source e ee)) =>
--  Wrapper target (T'II'I source o (Supertype a)) =>
--  Wrapper target (T'II'I source o (Supertype (Supertype a))) =>
--  Wrapper target (T'II'I source o (Supertype (Supertype (Supertype a)))) =>
--  target (u i a) (target (source (Supertype (Supertype (Supertype a))) o) (u i o))
-- ho'st'st'st = fai (fai @source super `compose` fai @source super `compose` fai @source super) `compose` yio @source @target

-- ho_'st'st'st = ho'st'st'st
-- ho__'st'st'st = ho'st'st'st
-- ho___'st'st'st = ho'st'st'st
-- ho____'st'st'st = ho'st'st'st
-- ho_____'st'st'st = ho'st'st'st
-- ho______'st'st'st = ho'st'st'st
-- ho_______'st'st'st = ho'st'st'st
-- ho________'st'st'st = ho'st'st'st

-- ho'st'st'st'st, ho_'st'st'st'st, ho__'st'st'st'st, ho___'st'st'st'st, ho____'st'st'st'st, ho_____'st'st'st'st, ho______'st'st'st'st, ho_______'st'st'st'st, ho________'st'st'st'st
--  :: forall source target u i a o .
--  Precategory source =>
--  Precategory target =>
--  Covariant Yoneda Functor source target (T'I'II u i) =>
--  Contravariant Semi Functor source target (T'II'I source o) =>
--  Covariant Semi Functor source target (T'I'II source o) =>
--  Wrapper source a =>
--  Wrapper source (Supertype a) =>
--  Wrapper source (Supertype (Supertype a)) =>
--  Wrapper source (Supertype (Supertype (Supertype a))) =>
--  (forall e . Wrapper target (T'I'II u i e)) =>
--  (forall e ee . Wrapper target (T'I'II source e ee)) =>
--  (forall e ee . Wrapper target (T'II'I source e ee)) =>
--  Wrapper target (T'II'I source o (Supertype a)) =>
--  Wrapper target (T'II'I source o (Supertype (Supertype a))) =>
--  Wrapper target (T'II'I source o (Supertype (Supertype (Supertype a)))) =>
--  Wrapper target (T'II'I source o (Supertype (Supertype (Supertype (Supertype a))))) =>
--  u i a -> target (source (Supertype (Supertype (Supertype (Supertype a)))) o) (u i o)
-- ho'st'st'st'st x = yio @source @target @u x `compose` fai @source super `compose` fai @source super `compose` fai @source super `compose` fai @source super

-- ho_'st'st'st'st = ho'st'st'st'st
-- ho__'st'st'st'st = ho'st'st'st'st
-- ho___'st'st'st'st = ho'st'st'st'st
-- ho____'st'st'st'st = ho'st'st'st'st
-- ho_____'st'st'st'st = ho'st'st'st'st
-- ho______'st'st'st'st = ho'st'st'st'st
-- ho_______'st'st'st'st = ho'st'st'st'st
-- ho________'st'st'st'st = ho'st'st'st'st

-- yio'yio'yui, yio'ho'yui, ho'yio'yui, ho'ho'yui
--  :: forall source u uu uuu o i ii iii a .
--  Terminal source =>
--  Category source =>
--  Covariant Yoneda Functor u source (T'I'II u i) =>
--  Contravariant Yoneda Functor (AR) (AR) (T'II'I u i) =>
--  Covariant Semi Functor source u (T'I'II uu ii) =>
--  Covariant Endo Semi Functor source (T'II'I uuu iii) =>
--  Covariant Endo Semi Functor (AR) (T'I'II (AR) (u i (uu a ii))) =>
--  Contravariant Semi Functor (AR) (AR) (T'II'I source (u i (uu ii (uuu o iii)))) =>
--  (forall e ee . Wrapper source (T'II'I uuu e ee)) =>
--  (forall e ee . Wrapper source (T'I'II uu e ee)) =>
--  (forall e ee . Wrapper source (T'I'II u e ee)) =>
--  (forall e ee . Wrapper u (T'I'II uu e ee)) =>
--  (forall e . Wrapper (AR) (source Unit e)) =>
--  u i (uu ii (uuu a iii)) -> source (Supertype (source Unit o)) (u i (uu ii (uuu o iii)))
-- yio'yio'yui x = fai @(AR) @(AR) (fio @source `compose` fui @source) (ho @u @source x)

-- ho'yio'yui = yio'yio'yui
-- yio'ho'yui = yio'yio'yui
-- ho'ho'yui = yio'yio'yui

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
 (forall e . Covariant Endo Semi Functor (AR) (T'I'II (AR) e)) =>
 (forall e . Contravariant Semi Functor (AR) source (T'II'I source e)) =>
 (forall e . Covariant Endo Semi Functor source (T'I'II source e)) =>
 (forall e . Contravariant Endo Semi Functor source (T'II'I source e)) =>
 (forall e . Wrapper t (T'I'II tt ii e)) =>
 (forall e . Wrapper (AR) (source Unit e)) =>
 (forall e ee . Wrapper source (T'I'II tt e ee)) =>
 (forall e ee . Wrapper source (T'I'II t e ee)) =>
 (forall e ee . Wrapper source (T'II'I source e ee)) =>
 (forall e ee . Wrapper source (T'I'II source e ee)) =>
 source (t i (tt ii a)) (source (Supertype (source Unit o)) (t i (tt ii o)))
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

-- ho'ha'st'st, ho_'ha'st'st, ho__'ha'st'st, ho___'ha'st'st, ho____'ha'st'st, ho_____'ha'st'st, ho______'ha'st'st, ho_______'ha'st'st, ho________'ha'st'st
--  :: forall source u uu o i ii a .
--  Covariant Yoneda Functor u (AR) (T'I'II u i) =>
--  Contravariant Semi Functor source u (T'II'I uu ii) =>
--  (forall e ee . Wrapper u (T'II'I uu e ee)) =>
--  Wrapper source a =>
--  Wrapper source (Supertype a) =>
--  u i (uu o ii) -> source (Supertype (Supertype a)) o -> u i (uu a ii)
-- ho'ha'st'st x = fai (fai `compose` fai @source super'super) (ho @u x)

-- ho_'ha'st'st = ho'ha'st'st
-- ho__'ha'st'st = ho'ha'st'st
-- ho___'ha'st'st = ho'ha'st'st
-- ho____'ha'st'st = ho'ha'st'st
-- ho_____'ha'st'st = ho'ha'st'st
-- ho______'ha'st'st = ho'ha'st'st
-- ho_______'ha'st'st = ho'ha'st'st
-- ho________'ha'st'st = ho'ha'st'st

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

-- ho'yoo, ho_'yoo, ho__'yoo, ho___'yoo, ho____'yoo, ho_____'yoo, ho______'yoo, ho_______'yoo, ho________'yoo
--  :: forall source target t i tt a o .
--  Covariant Endo Semi Functor source (T'I'I tt) =>
--  Covariant Yoneda Functor source target (T'I'II t i) =>
--  (forall e ee . Wrapper target (T'I'II t e ee)) =>
--  Contravariant Endo Semi Functor (AR) (T'II'I target (t i ((tt o o)))) =>
--  (forall e ee . Wrapper target (T'I'II source e ee)) =>
--  (forall e . Wrapper source (T'I'I tt e)) =>
--  target (t i (tt a a)) (target (source (a) o) (t i (tt o o)))
-- ho'yoo = fai (foo @source @source @tt) `compose` yio @source @target

-- ho_'yoo = ho'yoo
-- ho__'yoo = ho'yoo
-- ho___'yoo = ho'yoo
-- ho____'yoo = ho'yoo
-- ho_____'yoo = ho'yoo
-- ho______'yoo = ho'yoo
-- ho_______'yoo = ho'yoo
-- ho________'yoo = ho'yoo

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

-- st'ho, he_'ho, he__'ho, he___'ho, he____'ho, he_____'ho, he______'ho, he_______'ho, he________'ho
--  :: forall source target u i a o .
--  Covariant Yoneda Functor source target (T'I'II u (Supertype i)) =>
--  Contravariant Semi Functor target target (T'II'I u o) =>
--  Wrapper target i =>
--  (forall e ee . Wrapper target (T'I'II source e ee)) =>
--  (forall e ee . Wrapper target (T'I'II u e ee)) =>
--  (forall e ee . Wrapper target (T'II'I u e ee)) =>
--  u (Supertype i) a -> target (source a o) (u i o)
-- st'ho x = fai @target super `compose` yio @source @target @u

-- he_'ho= st'ho
-- he__'ho= st'ho
-- he___'ho= st'ho
-- he____'ho= st'ho
-- he_____'ho= st'ho
-- he______'ho= st'ho
-- he_______'ho= st'ho
-- he________'ho= st'ho

-- st'ho'st, he_'ho'st, he__'ho'st, he___'ho'st, he____'ho'st, he_____'ho'st, he______'ho'st, he_______'ho'st, he________'ho'st
--  :: forall source target u i a o .
--  Covariant Yoneda Functor source target (T'I'II u (Supertype i)) =>
--  Contravariant Semi Functor source target (T'II'I u o) =>
--  Contravariant Semi Functor source target (T'II'I source o) =>
--  Wrapper source a =>
--  Wrapper source i =>
--  (forall e ee . Wrapper target (T'II'I source e ee)) =>
--  (forall e ee . Wrapper target (T'I'II source e ee)) =>
--  (forall e ee . Wrapper target (T'II'I u e ee)) =>
--  (forall e ee . Wrapper target (T'I'II u e ee)) =>
--  Wrapper target (T'II'I u o (Supertype i)) =>
--  Wrapper target (T'II'I source o (Supertype a)) =>
--  u (Supertype i) a -> target (source (Supertype a) o) (u i o)
-- st'ho'st x = fai @source @target super
--  `compose` yio @source @target @u x
--  `compose` fai @source @target super

-- he_'ho'st = st'ho'st
-- he__'ho'st = st'ho'st
-- he___'ho'st = st'ho'st
-- he____'ho'st = st'ho'st
-- he_____'ho'st = st'ho'st
-- he______'ho'st = st'ho'st
-- he_______'ho'st = st'ho'st
-- he________'ho'st = st'ho'st

-- st'hu
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
-- st'hu = yiu @target @u `compose` st @source

-- st'st'ho
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
-- -- st'st'ho = yio @source @target @u `compose` fai @source super'st

-- st'st'st'ho
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
-- st'st'st'ho = yio @source @target @u `compose` fai @source super'st'st

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

ha'st, ha_'st, ha__'st, ha___'st, ha____'st, ha_____'st, ha______'st, ha_______'st, ha________'st
 :: forall source target t i a o .
 Contravariant Yoneda Functor source target (T'II'I t i) =>
 (forall e . Contravariant Semi Functor source target (T'II'I source e)) =>
 (forall e . Contravariant Endo Semi Functor target (T'II'I target e)) =>
 (forall e . Covariant Endo Semi Functor target (T'I'II target e)) =>
 (forall e ee . Wrapper target (T'II'I t e ee)) =>
 (forall e ee . Wrapper target (T'II'I source e ee)) =>
 (forall e ee . Wrapper target (T'I'II target e ee)) =>
 (forall e ee . Wrapper target (T'II'I target e ee)) =>
 Wrapper source o =>
 target (t a i) (target (source (Supertype o) a) (t o i))
ha'st = fai (fai @source @target super) `compose` yai @source @target @t

ha_'st = ha'st
ha__'st = ha'st
ha___'st = ha'st
ha____'st = ha'st
ha_____'st = ha'st
ha______'st = ha'st
ha_______'st = ha'st
ha________'st = ha'st

ha'st'st, ha_'st'st, ha__'st'st, ha___'st'st, ha____'st'st, ha_____'st'st, ha______'st'st, ha_______'st'st, ha________'st'st
 :: forall source target t e a o .
 (forall e . Covariant Endo Semi Functor target (T'I'II target e)) =>
 (forall e . Contravariant Endo Semi Functor target (T'II'I target e)) =>
 Contravariant Yoneda Functor source target (T'II'I t e) =>
 Contravariant Semi Functor source target (T'II'I source a) =>
 Wrapper source o =>
 (forall e ee . Wrapper target (T'II'I source e ee)) =>
 (forall e ee . Wrapper target (T'I'II target e ee)) =>
 (forall e ee . Wrapper target (T'II'I target e ee)) =>
 (forall e ee . Wrapper target (T'II'I t e ee)) =>
 Wrapper source (Supertype o) =>
 target (t a e) (target (source (Supertype (Supertype o)) a) (t o e))
ha'st'st = fai @target (fai @source (super `compose` super)) `compose` yai @source @target @t

ha_'st'st = ha'st'st
ha__'st'st = ha'st'st
ha___'st'st = ha'st'st
ha____'st'st = ha'st'st
ha_____'st'st = ha'st'st
ha______'st'st = ha'st'st
ha_______'st'st = ha'st'st
ha________'st'st = ha'st'st

-- st'ha :: forall source target t i a o .
--  Contravariant Yoneda Functor source target (T'II'I t i) =>
--  Contravariant Semi Functor target (AR) (T'II'I t i) =>
--  Wrapper target a =>
--  (forall e ee . Wrapper target (T'II'I source e ee)) =>
--  (forall e ee . Wrapper target (T'I'II t e ee)) =>
--  (forall e ee . Wrapper target (T'II'I t e ee)) =>
--  t (Supertype a) i -> target (source o a) (t o i)
-- st'ha = yai @source @target @t `compose` fai @target super

-- st'ho: u (Supertype i) a -> target (source a o) (u i o)
-- ho'st: u i a -> target (source (Supertype a) o) (u i o)

-- st'ho: u (Supertype i) a -> target (source a o) (u i o)
-- ho'st: u i a -> target (source (Supertype a) o) (u i o)
-- ha'st: u a i -> target (source (Supertype o) a) (u o i)

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

-- ha'st'hu :: forall source u uu o e ee a .
 -- Covariant Semi Functor u u (T'I'II uu ee) =>
 -- Constant Semi Functor u u (T'I'II uu ee) (T'I'II uu ee) =>
 -- Contravariant Yoneda Functor u (AR) (T'II'I u e) =>
 -- Wrapper u (T'I'II uu ee a) =>
 -- Wrapper u (T'I'II uu ee o) =>
 -- Elicitable T'II'I (AR) (u () o) =>
 -- u (uu ee o) e -> Supertype (u () o) -> u (uu ee a) e
-- ha'st'hu x = fai @(AR) @(AR) fiu (ha'st @u x)

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

-- -- TODO: rephasce with `ho_`
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
-- ho_yi x = fai @source (fio @source super) (ho x)

-- -- TODO: rephasce with `ho_ho`
-- ho_yi'ho :: forall source u e a o .
--  Covariant Yoneda Functor source (AR) (T'I'II u e) =>
--  Elicitable T'I'II source a =>
--  u e a -> source (Supertype a) o -> u e o
-- ho_yi'ho x xx = x `ho` st @source `ho` xx

-- hu, hu_, hu__, hu___, hu____, hu_____, hu______, hu_______, hu________ ::
 -- forall target t i a o .
 -- Covariant Yoneda Functor target target (T'I'II t i) =>
 -- Mapping T'I'II T'I'II target target I (T'I'II target a) =>
 -- (forall e ee . Wrapper target (T'I'II targee ee )o) =>
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

yor :: forall source target t object o .
 Covariant Transformation Functor source target t (T'I'II source object) =>
 (forall e . Wrapper target (T'I'II source object e)) =>
 target (t o) (source object o)
yor = super `compose` map @T'I'II @T'I'II @source @target @t @(T'I'II source object) identity

yior :: forall source target t object i o .
 Covariant Transformation Functor source target (T'I'II t i) (T'I'II source object) =>
 (forall e ee . Wrapper target (T'I'II source e ee)) =>
 (forall e ee . Wrapper target (T'I'II t e ee)) =>
 target (t i o) (source object o)
yior = super `compose` map @T'I'II @T'I'II @source @target @(T'I'II t _) @(T'I'II source object) identity `compose` wrap @target @(T'I'II t _ _)

yoir :: forall source target t object i o .
 Covariant Yoneda Functor source target (T'II'I t i) =>
 Covariant Transformation Functor source target (T'II'I t i) (T'I'II source object) =>
 (forall e ee . Wrapper target (T'I'II source e ee)) =>
 (forall e ee . Wrapper target (T'II'I t e ee)) =>
 target (t o i) (source object o)
yoir = super `compose` map @T'I'II @T'I'II @source @target @(T'II'I t _) @(T'I'II source object) identity `compose` wrap @target @(T'II'I t _ _)

yoor :: forall source target t object a o .
 Covariant Transformation Functor source target (T'I'I t) (T'I'II source object) =>
 (forall e . Wrapper target (T'I'II source object e)) =>
 (forall e ee . Wrapper target (T'I'II source e ee)) =>
 (forall e . Wrapper target (T'I'I t e)) =>
 target (t o o) (source object o)
yoor = super `compose` map @T'I'II @T'I'II @source @target @(T'I'I t) @(T'I'II source object) identity `compose` wrap @target @(T'I'I t _)

-- yor: target (t o) (source object o)
-- ryo: target (source object o) (t o)

ryo :: forall source target t object a o i .
 Covariant Yoneda Functor source target I =>
 (forall e . Covariant Endo Semi Functor target (T'I'II target e)) =>
 (forall e . Contravariant Endo Semi Functor target (T'II'I target e)) =>
 Component target (T'I'II source object) t =>
 (forall e ee . Wrapper target (T'I'II source e ee)) =>
 (forall e ee . Wrapper target (T'I'II target e ee)) =>
 (forall e ee . Wrapper target (T'II'I target ee e)) =>
 (forall e . Wrapper target (I e)) =>
 target (source object a) (target (source (t a) o) o)
ryo = yv `compose` component @target @(T'I'II source object) @t `compose` wrap

hjd'q, hjd_'q, hjd__'q, hjd___'q, hjd____'q, hjd_____'q, hjd______'q, hjd_______'q, hjd________'q
 :: forall target a .
 Adjoint Functor target target (T'II'I (P) a) (T'I'II target a) =>
 (forall e . Wrapper target ((T'I'II target a `T'TT'I` T'II'I (P) a) e)) =>
 (forall e . Wrapper target (T'II'I (P) a e)) =>
 (forall e . Wrapper target (T'I'II target a e)) =>
 (forall e . Wrapper target (I e)) =>
 Setoid target a =>
 target a (target a (a `P` a `S` a))
hjd'q = fij @target @target @(P) @target q

hjd_'q = hjd'q
hjd__'q = hjd'q
hjd___'q = hjd'q
hjd____'q = hjd'q
hjd_____'q = hjd'q
hjd______'q = hjd'q
hjd_______'q = hjd'q
hjd________'q = hjd'q

hop'q, hop_'q, hop__'q, lo___'q, lo____'q, lo_____'q, lo______'q, lo_______'q, lo________'q
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
hop'q x y = q `compose` hop x y

hop_'q = hop'q
hop__'q = hop'q
lo___'q = hop'q
lo____'q = hop'q
lo_____'q = hop'q
lo______'q = hop'q
lo_______'q = hop'q
lo________'q = hop'q

hjd's, hjd_'s, hjd__'s, hjd___'s, hjd____'s, hjd_____'s, hjd______'s, hjd_______'s, hjd________'s
 :: forall target a .
 Adjoint Functor target target (T'II'I (P) a) (T'I'II target a) =>
 (forall e . Wrapper target ((T'I'II target a `T'TT'I` T'II'I (P) a) e)) =>
 (forall e . Wrapper target (T'II'I (P) a e)) =>
 (forall e . Wrapper target (T'I'II target a e)) =>
 (forall e . Wrapper target (I e)) =>
 Semigroup target a =>
 target a (target a a)
hjd's = fij @target @target @(P) @target s

hjd_'s = hjd's
hjd__'s = hjd's
hjd___'s = hjd's
hjd____'s = hjd's
hjd_____'s = hjd's
hjd______'s = hjd's
hjd_______'s = hjd's
hjd________'s = hjd's

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

-- st'ya :: forall source target t a o e .
--  Precategory target =>
--  (Supertype e ~ t a) =>
--  Contravariant Yoneda Functor source target t =>
--  Wrapper target (T'II'I source a o) =>
--  Wrapper (AR) e =>
--  e -> target (source o a) (t o)
-- st'ya = ya @source @target `compose` super

-- st'yo :: forall source target t a o e .
--  Precategory target =>
--  (Supertype e ~ t a) =>
--  Covariant Yoneda Functor source target t =>
--  (forall e ee . Wrapper target (T'I'II source e ee)) =>
--  Wrapper (AR) e =>
--  e -> target (source a o) (t o)
-- st'yo = yo @source @target `compose` super

-- st'yu :: forall target t a o e .
--  Precategory target =>
--  Covariant Yoneda Functor target target t =>
--  Mapping T'I'II T'I'II (AR) (AR) t t =>
--  Mapping T'I'II T'I'II target target I (T'I'II target a) =>
--  (forall e ee . Wrapper target (T'I'II targee ee)) =>
--  Wrapper (AR) (target () o) =>
--  Wrapper target (target () o) =>
--  Elicitable T'II'I target (T'I'II target () o) =>
--  Wrapper target (I o) =>
--  Wrapper (AR) e =>
--  t a -> target o (t o)
-- st'yu = yu @target

hop, hop_, hop__, lo___, lo____, lo_____, lo______, lo_______
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
hop l r = objective @T'II'I @target @_ @(o `P` oo)
 `compose` foi @target @target l `compose` fio @target @target r
 `compose` wrapped (map @T'II'I @T'II'I @target @target @(Both Product) @I identity)

hop_ = hop
hop__ = hop
lo___ = hop
lo____ = hop
lo_____ = hop
lo______ = hop
lo_______ = hop

-- TODO: define longer versions of this operator
hop'hjd :: forall target a aa o oo .
 Category target =>
 Limit T'I'II target target =>
 Covariant Endo Semi Functor target (P'I'II (a `P` aa)) =>
 Covariant Endo Semi Functor target (T'II'I (P) oo) =>
 (forall e ee . Wrapper target (e `P'I'II` ee)) =>
 (forall e ee . Wrapper target (T'II'I (P) e ee)) =>
 (forall e . Wrapper target (Both (P) e)) =>
 (forall e . Wrapper target (I e)) =>
 target a o -> target aa oo -> target (a `P` aa) (o `P` oo)
hop'hjd l r = hop
 (l `compose` (wrapped (left @T'I'II @target identity)))
 (r `compose` (wrapped (right @T'I'II @target identity)))

hop'yp, hop_'yp, hop__'yp, lo___'yp, lo____'yp, lo_____'yp, lo______'yp, lo_______'yp
 :: forall t tt l a o oo .
 Mapping T'I'II T'I'II (AR) (AR) (Covariant Day (AR) (P) P t (tt `L` tt `T` l) o oo) t =>
 Arrow a (t o) -> Arrow a ((tt `L` tt `T` l) oo) -> Arrow a (t (Product o oo))
hop'yp l r = yp `compose` hop @(AR) @(t o `P` (tt `L` tt `T` l) oo) l r

hop_'yp = hop'yp
hop__'yp = hop'yp
lo___'yp = hop'yp
lo____'yp = hop'yp
lo_____'yp = hop'yp
lo______'yp = hop'yp
lo_______'yp = hop'yp

hop'yp'yo'q, hop_'yp'yo'q, hop__'yp'yo'q, lo___'yp'yo'q, lo____'yp'yo'q, lo_____'yp'yo'q, lo______'yp'yo'q, lo_______'yp'yo'q
 :: forall a o t tt ll .
 Mapping T'I'II T'I'II (AR) (AR) (Covariant Day (AR) (P) P t (tt `L` tt `T` ll) o o) t =>
 Covariant Yoneda Functor (AR) (AR) (T'I'II Product (t o)) =>
 Covariant Yoneda Functor (AR) (AR) (T'II'I Product ()) =>
 Setoid (AR) o =>
 Arrow a (t o) -> Arrow a (tt `L` tt `T` ll `T` o) -> Arrow a (t (o `P` o `S` o))
hop'yp'yo'q x xx xxx = yp'yo (hop x xx xxx) q

hop_'yp'yo'q = hop'yp'yo'q
hop__'yp'yo'q = hop'yp'yo'q
lo___'yp'yo'q = hop'yp'yo'q
lo____'yp'yo'q = hop'yp'yo'q
lo_____'yp'yo'q = hop'yp'yo'q
lo______'yp'yo'q = hop'yp'yo'q
lo_______'yp'yo'q = hop'yp'yo'q

hop'ys, hop_'ys, hop__'ys, lo___'ys, lo____'ys, lo_____'ys, lo______'ys, lo_______'ys
 :: forall t tt l a o oo .
 Mapping T'I'II T'I'II (AR) (AR) (Covariant Day (AR) (P) (S) t (tt `L` tt `T` l) o oo) t =>
 Arrow a (t o) -> Arrow a ((tt `L` tt `T` l) oo) -> Arrow a (t (Sum o oo))
hop'ys l r = ys `compose` hop @(AR) @(t o `P` (tt `L` tt `T` l) oo) l r

hop_'ys = hop'ys
hop__'ys = hop'ys
lo___'ys = hop'ys
lo____'ys = hop'ys
lo_____'ys = hop'ys
lo______'ys = hop'ys
lo_______'ys = hop'ys

hop'ys'has, hop_'ys'has, hop__'ys'has, lo___'ys'has, lo____'ys'has, lo_____'ys'has, lo______'ys'has, lo_______'ys'has
 :: forall t tt l a o .
 Mapping T'I'II T'I'II (AR) (AR) (Covariant Day (AR) (P) (S) t (tt `L` tt `T` l) o o) t =>
 Arrow a (t o) -> Arrow a ((tt `L` tt `T` l) o) -> Arrow a (t o)
hop'ys'has l r = (\x -> ys'yo x (identity @(AR) `has` identity)) `compose` hop @(AR) @(_ `P` _) l r

hop_'ys'has = hop'ys'has
hop__'ys'has = hop'ys'has
lo___'ys'has = hop'ys'has
lo____'ys'has = hop'ys'has
lo_____'ys'has = hop'ys'has
lo______'ys'has = hop'ys'has
lo_______'ys'has = hop'ys'has

hjd'ys'has, hjd_'ys'has, hjd__'ys'has, hjd___'ys'has, hjd____'ys'has, hjd_____'ys'has, hjd______'ys'has, hjd_______'ys'has
 :: forall t tt l a o .
 Mapping T'I'II T'I'II (AR) (AR) (Covariant Day (AR) (P) (S) t (tt `L` tt `T` l) o o) t =>
 Covariant Yoneda Functor (AR) (AR) (T'I'II Product (t o)) =>
 Covariant Yoneda Functor (AR) (AR) (T'II'I Product ()) =>
 t o -> (tt `L` tt `T` l) o -> (t o)
hjd'ys'has l r = ys'yo (hjd @AR @AR @_ @(t o `P` _) l r) (identity @(AR) `has` identity)

hjd_'ys'has = hjd'ys'has
hjd__'ys'has = hjd'ys'has
hjd___'ys'has = hjd'ys'has
hjd____'ys'has = hjd'ys'has
hjd_____'ys'has = hjd'ys'has
hjd______'ys'has = hjd'ys'has
hjd_______'ys'has = hjd'ys'has

has, has_, has__, has___, has____, has_____, has______, has_______ :: forall source i a o oo .
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
has l r = wrapped (map @T'II'I @T'II'I @source @source @I @(Both Sum) identity)
 `compose` foi @source @source l
 `compose` fio @source @source r
 `compose` objective @T'I'II @source @a @(o `S` oo)

has_ = has
has__ = has
has___ = has
has____ = has
has_____ = has
has______ = has
has_______ = has

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
-- `has`: source o i -> source oo i -> source (o `S` oo) i
-- `hop`: target a o -> target a oo -> target a (o `P` oo)
--     : u (source o i) (source oo i) -> source (uu o oo) i

-- TODO: to test
-- rwr'has :: forall source target r o a aa .
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
-- rwr'has l r = rwr /
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
-- yip = super @Arrow
 -- `compose` day @T'I'II @(AR) @(T'I'II t e) @u @(P) identity identity
 -- `compose` fio @Arrow wrap `compose` foi @Arrow wrap

-- TODO: try to generalize
-- yip'yo :: forall u e ee eee t r .
 -- Covariant Endo Semi Functor (AR) (T'II'I u (t e eee)) =>
 -- Covariant Endo Semi Functor (AR) (T'I'II u (T'I'II t e ee)) =>
 -- Covariant Monoidal Functor (AR) (AR) u (P) (T'I'II t e) =>
 -- u (t e ee) (t e eee) -> (AR) (ee `P` eee) r -> t e r
-- yip'yo x f = super @Arrow
 -- `compose` day @T'I'II @(AR) @(T'I'II t e) @u @(P) identity f
 -- `compose` fio @Arrow wrap `compose` foi @Arrow wrap
 -- `hc`x

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
-- yis = super @Arrow
 -- `compose` day @T'I'II @(AR) @(T'I'II t e) @u @(S) identity identity
 -- `compose` fio @Arrow wrap `compose` foi @Arrow wrap

-- TODO: try to generalize
yw :: forall u e ee t tt l .
 -- Covariant Monoidal Functor (AR) (AR) u (W) l t =>
 Mapping T'I'II T'I'II (AR) (AR) (Covariant Day (AR) u (W) t (tt `L` tt `T` l) e ee) t =>
 u (t e) ((tt `L` tt `T` l) ee) -> t (e `S` ee `S_` e `P` ee)
yw = day @T'I'II @(AR) @l @t @tt @u @(W) identity super

-- TODO: try to generalize
yw'yo :: forall source u e ee r t tt ll .
 Category source =>
 Mapping T'I'II T'I'II source (AR) (Covariant Day source u (W) t (tt `L` tt `T` ll) e ee) t =>
 Wrapper source (e `W` ee) =>
 u (t e) (tt `L` tt `T` ll `T` ee) -> source (e `S` ee `S_` e `P` ee) r -> t r
yw'yo x f = day @T'I'II @source @ll @t @tt @u @(W) identity (f `compose` super) x

-- TODO: try to generalize
yw'yokl :: forall source u e ee r t tt ttt l ll lll .
 Category source =>
 Covariant Endo Transformation Functor (AR) (t `T'TT'I` ttt `L` ttt `T` lll `L` t `T` l) (t `TT'T'I` ttt) =>
 Mapping T'I'II T'I'II source (AR) (Covariant Day source u (W) t (tt `L` tt `T` ll) e ee) t =>
 Wrapper source (e `W` ee) =>
 u (t e) (tt `L` tt `T` ll `T` ee) -> source (e `S` ee `S_` e `P` ee) (ttt `L` ttt `T` lll `L` t `T` l `T` r) -> ttt (t r)
yw'yokl x f = wrapped (component @(AR) @(t `T'TT'I` ttt `L` ttt `T` lll `L` t `T` l) @(t `TT'T'I` ttt))
 (day @T'I'II @source @ll @t @tt @u @(W) identity (f `compose` super) x)

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
-- yp'yok :: forall i ii source target t tt ttt l ll o .
--  Covariant Transformation Functor (AR) (AR) (Covariant Day (AR) (P) P t (ttt `L` ttt `T` l) i ii) t =>
--  Covariant Endo Semi Functor target tt =>
--  Covariant Endo Semi Functor target t =>
--  Covariant Yoneda Functor source target t =>
--  Covariant Endo Transformation Functor target (t `T'TT'I` tt `L` tt `T` ll) t =>
--  (forall e ee . Wrapper target (T'I'II source e ee)) =>
--  (forall e . Wrapper target ((t `T'TT'I` tt `L` tt `T` ll) e)) =>
--  target (t i `P` (ttt `L` ttt `T` l) ii) (target (source (i `P` ii) ((tt `L` tt `T` ll) o)) (t o))
-- yp'yok = yok @source @target `compose` yp

-- -- TODO: try to generalize
-- yp'yokl :: forall e ee source target t tt ttt l ll lll o .
--  Covariant Endo Transformation Functor target (t `T'TT'I` tt `L` tt `T` ll `L` t `T` l) (t `TT'T'I` tt) =>
--  Covariant Transformation Functor (AR) (AR) (Covariant Day (AR) (P) P t (ttt `L` ttt `T` lll) e ee) t =>
--  Covariant Yoneda Functor source target t =>
--  Elicitable T'II'I target (T'I'II source (e `P` ee) (tt o)) =>
--  (forall i . Wrapper target (t `T'TT'I` tt `T'I_` i)) =>
--  (forall i . Wrapper target (TT'T'I t tt i)) =>
--  (forall i . Wrapper target ((t `T'TT'I` tt `L` tt `T` ll `L` t `T` l) i)) =>
--  (forall e ee . Wrapper target (T'I'II source e ee)) =>
--  target (t e `P` (ttt `L` ttt `T` lll) ee) (target (source (e `P` ee) (tt `L` tt `T` ll `L` t `T` l `T` o)) (tt (t o)))
-- yp'yokl = yokl @source @target `compose` yp

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
-- w'rw target = wrap @target `compose` target `compose` st @target

-- rw'w :: forall target a o .
 -- Precategory target =>
 -- Elicitable T'II'I target a =>
 -- Elicitable T'I'II target o =>
 -- target a o -> target (Supertype a) (Supertype o)
-- rw'w target = _' @target `compose` target `compose` wrap @target

-- yv__, yv___, yv____, yv_____, yv______ :: forall target a .
 -- Precategory target =>
 -- Elicitable T'I'II target a =>
 -- Elicitable T'I'II target (Supertype a) =>
 -- target a (Supertype (Supertype a))
-- yv__ = _' @target `compose` _' @target

-- yv___ = yv__
-- yv____ = yv__
-- yv_____ = yv__
-- yv______ = yv__

-- yv___, yv____, yv_____, yv______, yv_______ :: forall target a .
 -- Precategory target =>
 -- Elicitable T'I'II target a =>
 -- Elicitable T'I'II target (Supertype a) =>
 -- Elicitable T'I'II target (Supertype (Supertype a)) =>
 -- target a (Supertype (Supertype (Supertype a)))
-- yv___ = _' @target `compose` _' @target `compose` _' @target

-- yv____ = yv___
-- yv_____ = yv___
-- yv______ = yv___
-- yv_______ = yv___

-- TODO: it's wrong, we ne_d to rewrite it
-- st'st'st'ho :: forall a e o oo .
--  Elicitable T'I'II (AR) a =>
--  Elicitable T'I'II (AR) (Supertype a) =>
--  Elicitable T'I'II (AR) (Supertype (Supertype a)) =>
--  ((e `ARR` o) ~ Supertype (Supertype (Supertype a))) =>
--  a `ARR` e `ARR` (o `ARR` oo) `ARR` oo
-- st'st'st'ho x e f = f (_' (_' (_' x)) e)

-- TODO: define `rw'o`
-- TODO: define `rw'rw'o`
-- TODO: define `rw'ha`
-- TODO: define `rw'rw'ha`
-- TODO: define `rw'rw'rw'ha`

-- TODO: defined manually temporarily, rephasce with generated version
-- yo'yok
--  :: forall source target t tt ttt lll a o .
--  Covariant Endo Semi Functor source tt =>
--  Component source (tt `T'TT'I` ttt `L` ttt `T` lll) tt =>
--  Covariant Yoneda Functor source target t =>
--  Contravariant Endo Semi Functor (AR) (T'II'I target (t (tt o))) =>
--  (forall e ee . Wrapper target (T'I'II source e ee)) =>
--  (forall e . Wrapper source (tt `T'TT'I` ttt `L` ttt `T` lll `T'I_` e)) =>
--  (t (tt a)) -> target (source (a) (ttt `L` ttt `T` lll `T'I` o)) (t (tt o))
-- yo'yok = fai (fok @source @source @tt @ttt) `compose` yo @source @target

-- TODO: defined manually temporarily, rephasce with generated version
ho'yok, ho_'yok, ho__'yok, ho___'yok, ho____'yok, ho_____'yok, ho______'yok, ho_______'yok, ho________'yok :: forall source t tt ttt lll a o e .
 Covariant Endo Semi Functor source ttt =>
 Covariant Endo Semi Functor source tt =>
 Mapping T'I'II T'I'II source source (tt `T'TT'I` ttt `L` ttt `T` lll) tt =>
 Covariant Yoneda Functor source (AR) (T'I'II t e) =>
 (forall ee . Wrapper source ((tt `T'TT'I` ttt `L` ttt `T` lll) ee)) =>
 (forall ee . Wrapper source ((tt `T'TT'I` ttt) ee)) =>
 (forall ee . Wrapper source (ttt `L` ttt `T` lll `T` ee)) =>
 t e (tt a) -> source a (ttt `L` ttt `T` lll `T` o) -> t e (tt o)
ho'yok x = fai fok (ho @source x)

ho_'yok = ho'yok
ho__'yok = ho'yok
ho___'yok = ho'yok
ho____'yok = ho'yok
ho_____'yok = ho'yok
ho______'yok = ho'yok
ho_______'yok = ho'yok
ho________'yok = ho'yok

-- TODO: defined manually temporarily, rephasce with generated version
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

-- ha'kyo, ha_'kyo, ha__'kyo, ha___'kyo, ha____'kyo, ha_____'kyo, ha______'kyo, ha_______'kyo
--  :: forall source target t tt ttt l a o i .
--  Contravariant Yoneda Functor source target (T'II'I t i) =>
--  Covariant Endo Semi Functor source tt =>
--  Covariant Endo Semi Functor source ttt =>
--  (forall e . Covariant Endo Semi Functor (AR) (T'I'II source e)) =>
--  Covariant Endo Transformation Functor source tt (tt `T'TT'I` ttt `L` ttt `T` l) =>
--  (forall e . Contravariant Endo Yoneda Functor (AR) (T'II'I target e)) =>
--  (forall e . Wrapper source ((tt `T'TT'I` ttt `L` ttt `T` l) e)) =>
--  (forall e . Wrapper source ((tt `T'TT'I` ttt) e)) =>
--  (forall e . Wrapper source (ttt `L` ttt `T` l `T` e)) =>
--  (forall e . Wrapper source (I `L` ttt `T` l `T` e)) =>
--  (forall e . Wrapper source (I e)) =>
--  (forall e ee . Wrapper target (T'II'I source e ee)) =>
--  (forall e ee . Wrapper target (T'II'I t e ee)) =>
--  t (tt o) i -> target (source (ttt a) (I `L` ttt `T` l `T` o)) (t (tt a) i)
-- ha'kyo = fai kfo `compose` ha @source @target @t

-- ha_'kyo = ha'kyo
-- ha__'kyo = ha'kyo
-- ha___'kyo = ha'kyo
-- ha____'kyo = ha'kyo
-- ha_____'kyo = ha'kyo
-- ha______'kyo = ha'kyo
-- ha_______'kyo = ha'kyo

-- ha'kyok, ha_'kyok, ha__'kyok, ha___'kyok, ha____'kyok, ha_____'kyok, ha______'kyok, ha_______'kyok
--  :: forall source target t tt ttt tttt lll llll a o i .
--  Contravariant Yoneda Functor source target (T'II'I t i) =>
--  Covariant Endo Semi Functor source tt =>
--  Covariant Endo Semi Functor source ttt =>
--  (forall e . Covariant Endo Semi Functor (AR) (T'I'II source e)) =>
--  Covariant Endo Transformation Functor source tt (tt `T'TT'I` ttt `L` ttt `T` lll) =>
--  Covariant Endo Transformation Functor source (tt `T'TT'I` tttt `L` tttt `T` llll) tt =>
--  (forall e . Contravariant Endo Yoneda Functor (AR) (T'II'I target e)) =>
--  (forall e . Wrapper source (tt `T'TT'I` ttt `L` ttt `T` lll `T'I_` e)) =>
--  (forall e . Wrapper source (tt `T'TT'I` ttt `T'I_` e)) =>
--  (forall e . Wrapper source (tt `T'TT'I` tttt `L` tttt `T` llll `T'I_` e)) =>
--  (forall e . Wrapper source (ttt `L` ttt `T` lll `T` e)) =>
--  (forall e . Wrapper source (I e)) =>
--  (forall e . Wrapper source (I `L` ttt `T` lll `T` e)) =>
--  (forall e ee . Wrapper target (T'II'I source e ee)) =>
--  (forall e ee . Wrapper target (T'II'I t e ee)) =>
--  t (tt o) i -> target (source (ttt a) (I `L` ttt `T` lll `T'I` tttt `L` tttt `T` llll `T` o)) (t (tt a) i)
-- ha'kyok = fai kfok `compose` ha @source @target @t

-- ha_'kyok = ha'kyok
-- ha__'kyok = ha'kyok
-- ha___'kyok = ha'kyok
-- ha____'kyok = ha'kyok
-- ha_____'kyok = ha'kyok
-- ha______'kyok = ha'kyok
-- ha_______'kyok = ha'kyok

-- TODO: defined manually temporarily, rephasce with generated version haster
ha'yok, ha_'yok, ha__'yok, ha___'yok, ha____'yok, ha_____'yok, ha______'yok, ha_______'yok, ha________'yok
 :: forall source target t tt ttt l a o i .
 Contravariant Yoneda Functor source target (T'II'I t i) =>
 Covariant Endo Semi Functor source tt =>
 Covariant Endo Semi Functor source ttt =>
 Covariant Endo Transformation Functor source (tt `T'TT'I` ttt `L` ttt `T` l) tt =>
 (forall e . Contravariant Semi Functor (AR) target (T'II'I target e)) =>
 (forall e . Contravariant Endo Yoneda Functor target (T'II'I target e)) =>
 (forall e . Covariant Endo Yoneda Functor target (T'I'II target e)) =>
 -- Contravariant Yoneda Functor source (AR) (T'II'I t i) =>
 (forall e . Contravariant Endo Yoneda Functor (AR) (T'II'I target e)) =>
 (forall e . Wrapper source ((tt `T'TT'I` ttt `L` ttt `T` l) e)) =>
 (forall e . Wrapper source ((tt `T'TT'I` ttt) e)) =>
 (forall e . Wrapper source (ttt `L` ttt `T` l `T` e)) =>
 (forall e ee . Wrapper target (T'II'I source e ee)) =>
 (forall e ee . Wrapper target (T'II'I target e ee)) =>
 (forall e ee . Wrapper target (T'I'II target e ee)) =>
 (forall e ee . Wrapper target (T'II'I t e ee)) =>
 target (t (tt o) i) (target (source a (ttt `L` ttt `T` l `T` o)) (t (tt a) i))
ha'yok = fai fok `compose` ha @source @target @t

ha_'yok = ha'yok
ha__'yok = ha'yok
ha___'yok = ha'yok
ha____'yok = ha'yok
ha_____'yok = ha'yok
ha______'yok = ha'yok
ha_______'yok = ha'yok
ha________'yok = ha'yok

-- TODO: defined manually temporarily, rephasce with generated version
-- ha'yuk, ha_'yuk, ha__'yuk, ha___'yuk, ha____'yuk, ha_____'yuk, ha______'yuk, ha_______'yuk, ha________'yuk
--  :: forall target t tt ttt l a o i .
--  Contravariant Yoneda Functor (AR) target (T'II'I t i) =>
--  Covariant Endo Semi Functor (AR) tt =>
--  Covariant Endo Semi Functor (AR) ttt =>
--  Covariant Endo Transformation Functor (AR) (tt `T'TT'I` ttt `L` ttt `T` l) tt =>
--  Contravariant Yoneda Functor (AR) (AR) (T'II'I t i) =>
--  (forall e . Contravariant Yoneda Functor (AR) (AR) (T'II'I target e)) =>
--  (forall e . Wrapper (AR) ((tt `T'TT'I` ttt `L` ttt `T` l) e)) =>
--  (forall e . Wrapper (AR) (ttt `L` ttt `T` l `T` e)) =>
--  (forall e ee . Wrapper target (T'II'I (AR) e ee)) =>
--  (forall e . Wrapper target (T'II'I t i e)) =>
--  t (tt o) i -> target (ttt `L` ttt `T` l `T` o) (t (tt a) i)
-- ha'yuk = fai fuk `compose` ha @(AR) @target @t

-- ha_'yuk = ha'yuk
-- ha__'yuk = ha'yuk
-- ha___'yuk = ha'yuk
-- ha____'yuk = ha'yuk
-- ha_____'yuk = ha'yuk
-- ha______'yuk = ha'yuk
-- ha_______'yuk = ha'yuk
-- ha________'yuk = ha'yuk

-- TODO: defined manually temporarily, rephasce with generated version
ha'yokl, ha_'yokl, ha__'yokl, ha___'yokl, ha____'yokl, ha_____'yokl, ha______'yokl, ha_______'yokl, ha________'yokl
 :: forall source target t tt ttt l ll a o i .
 Contravariant Yoneda Functor source target (T'II'I t i) =>
 Covariant Endo Semi Functor source tt =>
 Covariant Endo Semi Functor source ttt =>
 Covariant Endo Transformation Functor source (tt `T'TT'I` ttt `L` ttt `T` ll `L` tt `T` l) (tt `TT'T'I` ttt) =>
 (forall e . Contravariant Endo Semi Functor target (T'II'I target e)) =>
 (forall e . Contravariant Semi Functor (AR) target (T'II'I target e)) =>
 (forall e . Covariant Endo Yoneda Functor target (T'I'II target e)) =>
 Contravariant Yoneda Functor source (AR) (T'II'I t i) =>
 (forall e . Wrapper source ((tt `T'TT'I` ttt `L` ttt `T` ll `L` tt `T` l) e)) =>
 (forall e . Wrapper source ((tt `T'TT'I` ttt) e)) =>
 (forall e . Wrapper source ((tt `TT'T'I` ttt) e)) =>
 (forall e . Wrapper source (ttt `L` ttt `T` l `T` e)) =>
 (forall e ee . Wrapper target (T'II'I source e ee)) =>
 (forall e ee . Wrapper target (T'I'II target e ee)) =>
 (forall e ee . Wrapper target (T'II'I target e ee)) =>
 (forall e ee . Wrapper target (T'II'I t e ee)) =>
 target (t (ttt (tt o)) i) (target (source a (ttt `L` ttt `T` ll `L` tt `T` l `T` o)) (t (tt a) i))
ha'yokl = fai fokl `compose` ha @source

ha_'yokl = ha'yokl
ha__'yokl = ha'yokl
ha___'yokl = ha'yokl
ha____'yokl = ha'yokl
ha_____'yokl = ha'yokl
ha______'yokl = ha'yokl
ha_______'yokl = ha'yokl
ha________'yokl = ha'yokl

-- TODO: defined manually temporarily, rephasce with generated version
-- yai'yukl, ha'yukl, ha_'yukl, ha__'yukl, ha___'yukl, ha____'yukl, ha_____'yukl, ha______'yukl, ha_______'yukl, ha________'yukl
--  :: forall target t ttt tt l ll a o i .
--  Constant Endo Semi Functor (AR) ttt =>
--  Covariant Endo Semi Functor (AR) tt =>
--  Covariant Endo Transformation Functor (AR) (ttt `T'TT'I` tt `L` tt `T` ll `L` ttt `T` l) (ttt `TT'T'I` tt) =>
--  Contravariant Yoneda Functor (AR) target (T'II'I t i) =>
--  (forall e . Contravariant Endo Semi Functor (AR) (T'II'I target e)) =>
--  (forall e . Covariant Semi Functor target (AR) (T'I'II target e)) =>
--  (forall e . Wrapper (AR) ((ttt `T'TT'I` tt `L` tt `T` ll `L` ttt `T` l) e)) =>
--  (forall e . Wrapper (AR) ((ttt `T'TT'I` tt) e)) =>
--  (forall e . Wrapper (AR) ((ttt `TT'T'I` tt) e)) =>
--  (forall e . Wrapper (AR) (tt `L` tt `T` l `T` e)) =>
--  (forall e ee . Wrapper target (T'II'I AR e ee)) =>
--  (forall e . Wrapper target (T'II'I t i e)) =>
--  Wrapper (AR) (I `T'I_` tt `L` tt `T` ll `L` ttt `T` l `T'I` o) =>
--  t (tt (ttt o)) i -> target (tt `L` tt `T` ll `L` ttt `T` l `T` o) (t (ttt a) i)
-- yai'yukl = fai fukl `compose` ha @(AR) @target @t

-- ha'yukl = yai'yukl
-- ha_'yukl = yai'yukl
-- ha__'yukl = yai'yukl
-- ha___'yukl = yai'yukl
-- ha____'yukl = yai'yukl
-- ha_____'yukl = yai'yukl
-- ha______'yukl = yai'yukl
-- ha_______'yukl = yai'yukl
-- ha________'yukl = yai'yukl

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

-- yokl__ :: forall source t t tt a o e .
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

-- yio'yokl'yokl
--  , ho'yokl'yokl
--  , ho_'yokl'yokl
--  , ho__'yokl'yokl
--  , ho___'yokl'yokl
--  , ho____'yokl'yokl
--  , ho_____'yokl'yokl
--  , ho______'yokl'yokl
--  , ho_______'yokl'yokl
--  , ho________'yokl'yokl
--  :: forall source target u t tt ttt l ll lll a o i .
--  Category source =>
--  Covariant Yoneda Functor source target (T'I'II u i) =>
--  Covariant Endo Semi Functor source t =>
--  Covariant Endo Semi Functor source tt =>
--  Covariant Semi Functor target source t =>
--  Covariant Endo Semi Functor source ttt =>
--  Covariant Semi Functor target source ttt =>
--  Contravariant Semi Functor (AR) (AR) (T'II'I target (u i (ttt (t (tt o))))) =>
--  Covariant Transformation Functor source source (t `T'TT'I` ttt `L` ttt `T` lll `L` t `T` ll) (t `TT'T'I` ttt) =>
--  Covariant Transformation Functor source source (tt `T'TT'I` ttt `L` ttt `T` lll `L` tt `T` ll) (tt `TT'T'I` ttt) =>
--  (forall e ee . Wrapper target (T'I'II source e ee)) =>
--  (forall e . Wrapper target (T'I'II u i e)) =>
--  (forall e . Wrapper source ((tt `TT'T'I` ttt) e)) =>
--  (forall e . Wrapper source ((t `TT'T'I` ttt) e)) =>
--  (forall e . Wrapper source (ttt `L` ttt `T` lll `T` e)) =>
--  (forall e . Wrapper source (ttt `L` ttt `T` lll `L` tt `T` ll `L` t `T` l `T'I` e)) =>
--  (forall e . Wrapper source ((tt `T'TT'I` ttt `L` ttt `T` lll `L` tt `T` ll) e)) =>
--  (forall e . Wrapper source (t `T'TT'I` ttt `L` ttt `T` lll `L` t `T` ll `T'I_` e)) =>
--  (forall e . Wrapper source (ttt `L` ttt `T` lll `L` t `T` ll `T` e)) =>
--  (forall e . Wrapper source (ttt `L` ttt `T` lll `L` tt `T` ll `T` e)) =>
--  u i (t (tt a)) -> target (source a (ttt `L` ttt `T` lll `L` tt `T` ll `L` t `T` l `T` o)) (u i (ttt (t (tt o))))
-- yio'yokl'yokl x = fai @(AR)
--  (fokl @source @source @t @ttt @ll @lll
--   `compose` fio @source (wrap @source @(ttt `L` ttt `T` lll `L` t `T` ll `T` _) `compose` wrap @source @(_ `L` _ `T` _ `T` _))
--   `compose` fokl @source @source @tt @ttt @ll @lll
--   `compose` fio @source (super @source @(_ `L` _ `T` _ `T` _)))
--  (yio @source x)

-- ho'yokl'yokl = yio'yokl'yokl
-- ho_'yokl'yokl = yio'yokl'yokl
-- ho__'yokl'yokl = yio'yokl'yokl
-- ho___'yokl'yokl = yio'yokl'yokl
-- ho____'yokl'yokl = yio'yokl'yokl
-- ho_____'yokl'yokl = yio'yokl'yokl
-- ho______'yokl'yokl = yio'yokl'yokl
-- ho_______'yokl'yokl = yio'yokl'yokl
-- ho________'yokl'yokl = yio'yokl'yokl

-- yio'yokl'yukl
--  , ho'yokl'yukl
--  , ho_'yokl'yukl
--  , ho__'yokl'yukl
--  , ho___'yokl'yukl
--  , ho____'yokl'yukl
--  , ho_____'yokl'yukl
--  , ho______'yokl'yukl
--  , ho_______'yokl'yukl
--  , ho________'yokl'yukl
--  :: forall target u t tt ttt l ll lll a o i .
--  Covariant Yoneda Functor (AR) target (T'I'II u i) =>
--  Covariant Endo Semi Functor (AR) t =>
--  Constant Endo Semi Functor (AR) tt =>
--  Covariant Semi Functor target (AR) t =>
--  Covariant Endo Semi Functor (AR) ttt =>
--  Covariant Semi Functor target (AR) ttt =>
--  Contravariant Semi Functor (AR) (AR) (T'II'I target (u i (ttt (t (tt o))))) =>
--  Covariant Transformation Functor (AR) (AR) (t `T'TT'I` ttt `L` ttt `T` lll `L` t `T` ll) (t `TT'T'I` ttt) =>
--  Covariant Transformation Functor (AR) (AR) (tt `T'TT'I` ttt `L` ttt `T` lll `L` tt `T` ll) (tt `TT'T'I` ttt) =>
--  (forall e ee . Wrapper target (T'I'II (AR) e ee)) =>
--  (forall e . Wrapper target (T'I'II u i e)) =>
--  (forall e . Wrapper (AR) ((tt `TT'T'I` ttt) e)) =>
--  (forall e . Wrapper (AR) ((t `TT'T'I` ttt) e)) =>
--  (forall e . Wrapper (AR) (ttt `L` ttt `T` lll `T` e)) =>
--  (forall e . Wrapper (AR) (ttt `L` ttt `T` lll `L` tt `T` ll `L` t `T` l `T` e)) =>
--  (forall e . Wrapper (AR) ((tt `T'TT'I` ttt `L` ttt `T` lll `L` tt `T` ll) e)) =>
--  (forall e . Wrapper (AR) ((t `T'TT'I` ttt `L` ttt `T` lll `L` t `T` l) e)) =>
--  (forall e . Wrapper (AR) (ttt `L` ttt `T` lll `L` t `T` l `T` e)) =>
--  u i (t (tt a)) -> target (ttt `L` ttt `T` lll `L` tt `T` ll `L` t `T` l `T` o) (u i (ttt (t (tt o))))
-- yio'yokl'yukl x = fai @(AR)
--  (fokl @(AR) @(AR) @t @ttt @ll @lll
--   `compose` fio @(AR) (wrap @(AR) @(_ `L` _ `T` ll `T` _) `compose` wrap @(AR) @(_ `L` _ `T` _ `T` _))
--   `compose` fukl @(AR) @tt @ttt @ll @lll
--   `compose` super @(AR) @(_ `L` _ `T` _ `T` _))
--  (yio @(AR) x)

-- ho'yokl'yukl = yio'yokl'yukl
-- ho_'yokl'yukl = yio'yokl'yukl
-- ho__'yokl'yukl = yio'yokl'yukl
-- ho___'yokl'yukl = yio'yokl'yukl
-- ho____'yokl'yukl = yio'yokl'yukl
-- ho_____'yokl'yukl = yio'yokl'yukl
-- ho______'yokl'yukl = yio'yokl'yukl
-- ho_______'yokl'yukl = yio'yokl'yukl
-- ho________'yokl'yukl = yio'yokl'yukl

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

-- yio'yoikl, ho'yoikl, ho_'yoikl, ho__'yoikl, ho___'yoikl, ho____'yoikl, ho_____'yoikl, ho______'yoikl, ho_______'yoikl, ho________'yoikl
--  :: forall source u t tt l ll a o i ii .
--  Covariant Semi Functor source (AR) (T'I'II u i) =>
--  Covariant Endo Semi Functor source tt =>
--  Covariant Endo Semi Functor source (T'II'I t ii) =>
--  Covariant Endo Transformation Functor source (T'II'I t ii `T'TT'I` tt `L` tt `T` ll `L` T'II'I t ii `T` l) (T'II'I t ii `TT'T'I` tt) =>
--  Covariant Yoneda Functor source (AR) (T'I'II u i) =>
--  (forall e . Wrapper source ((T'II'I t ii `T'TT'I` tt `L` tt `T` ll `L` T'II'I t ii `T` l) e)) =>
--  (forall e . Wrapper source ((T'II'I t ii `T'TT'I` tt) e)) =>
--  (forall e . Wrapper source ((T'II'I t ii `TT'T'I` tt) e)) =>
--  (forall e . Wrapper source (tt `L` tt `T` ll `L` T'II'I t ii `T` l `T` e)) =>
--  (forall e . Wrapper source (tt `L` tt `T` ll `T` e)) =>
--  (forall e . Wrapper source (T'II'I t ii e)) =>
--  u i (t a ii) -> source a (tt `L` tt `T` ll `L` T'II'I t ii `T` l `T` o) -> u i (tt (t o ii))
-- yio'yoikl x = fai foikl (ho @source x)

-- ho'yoikl = yio'yoikl
-- ho_'yoikl = yio'yoikl
-- ho__'yoikl = yio'yoikl
-- ho___'yoikl = yio'yoikl
-- ho____'yoikl = yio'yoikl
-- ho_____'yoikl = yio'yoikl
-- ho______'yoikl = yio'yoikl
-- ho_______'yoikl = yio'yoikl
-- ho________'yoikl = yio'yoikl

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
hjd'yp, hjd_'yp, hjd__'yp, hjd___'yp, hjd____'yp, hjd_____'yp, hjd______'yp
 :: forall o oo t tt l .
 Mapping T'I'II T'I'II (AR) (AR) (Covariant Day (AR) (P) P t (tt `L` tt `T` l) o oo) t =>
 -- Covariant Monoidal Functor (AR) (AR) (P) P l t =>
 Covariant Yoneda Functor (AR) (AR) (T'I'II Product (t o)) =>
 Covariant Yoneda Functor (AR) (AR) (T'II'I Product ()) =>
 t o -> (tt `L` tt `T` l) oo -> t (o `P` oo)
hjd'yp source_left r = yp (hjd @AR @AR @_ @(t o `P` _) source_left r)

hjd_'yp = hjd'yp
hjd__'yp = hjd'yp
hjd___'yp = hjd'yp
hjd____'yp = hjd'yp
hjd_____'yp = hjd'yp
hjd______'yp = hjd'yp

hjd'yp'yo'q, hjd_'yp'yo'q, hjd__'yp'yo'q, hjd___'yp'yo'q, hjd____'yp'yo'q, hjd_____'yp'yo'q, hjd______'yp'yo'q, hjd_______'yp'yo'q
 :: forall o t tt l .
 Mapping T'I'II T'I'II (AR) (AR) (Covariant Day (AR) (P) P t (tt `L` tt `T` l) o o) t =>
 -- Covariant Monoidal Functor (AR) (AR) (P) P l t =>
 Covariant Yoneda Functor (AR) (AR) (T'I'II Product (t o)) =>
 Covariant Yoneda Functor (AR) (AR) (T'II'I Product ()) =>
 Setoid (AR) o =>
 t o -> (tt `L` tt `T` l) o -> t (o `P` o `S` o)
hjd'yp'yo'q source_left r = yp'yo (hjd @AR source_left r) q

hjd_'yp'yo'q = hjd'yp'yo'q
hjd__'yp'yo'q = hjd'yp'yo'q
hjd___'yp'yo'q = hjd'yp'yo'q
hjd____'yp'yo'q = hjd'yp'yo'q
hjd_____'yp'yo'q = hjd'yp'yo'q
hjd______'yp'yo'q = hjd'yp'yo'q
hjd_______'yp'yo'q = hjd'yp'yo'q

-- hjd'yip, hjd_'yip, hjd__'yip, hjd___'yip, hjd____'yip, hjd_____'yip, hjd______'yip, hjd_______'yip
 -- :: forall e o oo t .
 -- Covariant Monoidal Functor (AR) (AR) (P) P (T'I'II t e) =>
 -- Covariant Yoneda Functor (AR) (AR) (T'I'II Product (t e o)) =>
 -- Covariant Yoneda Functor (AR) (AR) (T'II'I Product ()) =>
 -- t e o -> t e oo -> t e (o `P` oo)
-- hjd'yip l r = yip (hjd l r)

-- hjd_'yip = hjd'yip
-- hjd__'yip = hjd'yip
-- hjd___'yip = hjd'yip
-- hjd____'yip = hjd'yip
-- hjd_____'yip = hjd'yip
-- hjd______'yip = hjd'yip
-- hjd_______'yip = hjd'yip

hjd'ys, hjd_'ys, hjd__'ys, hjd___'ys, hjd____'ys, hjd_____'ys, hjd______'ys, hjd_______'ys
 :: forall o oo t tt l .
 -- Covariant Lax Monoidal Functor (AR) (AR) (P) (S) l t =>
 Mapping T'I'II T'I'II (AR) (AR) (Covariant Day (AR) (P) (S) t (tt `L` tt `T` l) o oo) t =>
 Covariant Yoneda Functor (AR) (AR) (P'I'II (t o)) =>
 Covariant Yoneda Functor (AR) (AR) (T'II'I (P) ()) =>
 t o -> (tt `L` tt `T` l) oo -> t (o `S` oo)
hjd'ys l r = ys (hjd @AR @AR @_ @(t o `P` _) l r)

hjd_'ys = hjd'ys
hjd__'ys = hjd'ys
hjd___'ys = hjd'ys
hjd____'ys = hjd'ys
hjd_____'ys = hjd'ys
hjd______'ys = hjd'ys
hjd_______'ys = hjd'ys

-- hjd'yis, hjd_'yis, hjd__'yis, hjd___'yis, hjd____'yis, hjd_____'yis, hjd______'yis, hjd_______'yis
 -- :: forall e o oo t .
 -- Covariant Monoidal Functor (AR) (AR) (P) (S) (T'I'II t e) =>
 -- Covariant Yoneda Functor (AR) (AR) (P'I'II (t e o)) =>
 -- Covariant Yoneda Functor (AR) (AR) (T'II'I (P) ()) =>
 -- t e o -> t e oo -> t e (o `S` oo)
-- hjd'yis l r = yis (hjd l r)

-- hjd_'yis = hjd'yis
-- hjd__'yis = hjd'yis
-- hjd___'yis = hjd'yis
-- hjd____'yis = hjd'yis
-- hjd_____'yis = hjd'yis
-- hjd______'yis = hjd'yis
-- hjd_______'yis = hjd'yis

hjd'yp'yp :: forall o oo t tt l ll .
 Covariant Endo Semi Functor (AR) tt =>
 Covariant Transformation Functor (AR) (AR) (Covariant Day (AR) (P) P t (t `L` t `T` l) (tt o) (tt `L` tt `T` ll `T` oo)) t =>
 Covariant Transformation Functor (AR) (AR) (Covariant Day (AR) (P) P tt (tt `L` tt `T` ll) o oo) tt =>
 Covariant Yoneda Functor (AR) (AR) (T'I'II Product (t (tt o))) =>
 Covariant Yoneda Functor (AR) (AR) (T'II'I Product Unit) =>
 t (tt o) -> (t `L` t `T` l) ((tt `L` tt `T` ll) oo) -> t (tt (o `P` oo))
hjd'yp'yp l r = yp'yp @(P) (hjd @AR @AR l r)

hjd'yp'ys
 :: forall t tt l ll o oo .
 Covariant Lax Monoidal Functor (AR) (AR) (P) P l t =>
 Covariant Lax Monoidal Functor (AR) (AR) (P) (S) ll tt =>
 Covariant Endo Semi Functor (AR) t =>
 Covariant Yoneda Functor (AR) (AR) (T'II'I Product ()) =>
 Covariant Yoneda Functor (AR) (AR) (T'I'II Product (t (tt o))) =>
 t (tt o) -> (t `L` t `T` l) ((tt `L` tt `T` ll) oo) -> t (tt (o `S` oo))
hjd'yp'ys l r = yp'ys (hjd @AR @AR @_ @(t (tt o) `P` _) l r)

-- hjd'yip'yp
 -- :: forall t tt o oo e .
 -- Covariant Lax Monoidal Functor (AR) (AR) (P) P tt =>
 -- Covariant Monoidal Functor (AR) (AR) (P) P (T'I'II t e) =>
 -- Covariant Endo Semi Functor (AR) (T'I'II t e) =>
 -- Covariant Yoneda Functor (AR) (AR) (T'II'I Product ()) =>
 -- Covariant Yoneda Functor (AR) (AR) (T'I'II Product (t e (tt o))) =>
 -- t e (tt o) -> t e (tt oo) -> t e (tt (o `P` oo))
-- hjd'yip'yp l r = yip'yp (hjd l r)

-- hjd'yip'yip
 -- :: forall t tt o oo e ee .
 -- Covariant Monoidal Functor (AR) (AR) (P) P (T'I'II tt ee) =>
 -- Covariant Monoidal Functor (AR) (AR) (P) P (T'I'II t e) =>
 -- Covariant Endo Semi Functor (AR) (T'I'II t e) =>
 -- Covariant Yoneda Functor (AR) (AR) (T'II'I Product ()) =>
 -- Covariant Yoneda Functor (AR) (AR) (T'I'II Product (t e (tt ee o))) =>
 -- t e (tt ee o) -> t e (tt ee oo) -> t e (tt ee (o `P` oo))
-- hjd'yip'yip l r = yip'yip (hjd l r)

-- hjd'yip'yis
 -- :: forall t tt l ll `T` o oo e ee .
 -- Covariant Monoidal Functor (AR) (AR) (P) P l (T'I'II t e) =>
 -- Covariant Monoidal Functor (AR) (AR) (P) (S) ll (T'I'II tt ee) =>
 -- Covariant Endo Semi Functor (AR) (T'I'II t e) =>
 -- Covariant Yoneda Functor (AR) (AR) (T'II'I Product ()) =>
 -- Covariant Yoneda Functor (AR) (AR) (T'I'II Product (t e (tt ee o))) =>
 -- t e (tt ee o) -> (t `L` t `T` l) e ((tt `L` tt `T` ll) ee oo) -> t e (tt ee (o `S` oo))
-- hjd'yip'yis l r = yip'yis (hjd l r)

 -- forall target tt i eee e ee . target i (tt ee eee)

hjd'yw, hjd_'yw, hjd__'yw, hjd___'yw, hjd____'yw, hjd_____'yw, hjd______'yw, hjd_______'yw
 :: forall e o oo t tt l .
 Mapping T'I'II T'I'II (AR) (AR) (Covariant Day (AR) (P) (W) t (tt `L` tt `T` l) o oo) t =>
 Covariant Yoneda Functor (AR) (AR) (T'II'I Product ()) =>
 Covariant Yoneda Functor (AR) (AR) (T'I'II Product (t o)) =>
 t o -> (tt `L` tt `T` l) oo -> t (o `S` oo `S_` o `P` oo)
hjd'yw l r = yw (hjd @AR @AR @_ @(t o `P` _) l r)

hjd_'yw = hjd'yw
hjd__'yw = hjd'yw
hjd___'yw = hjd'yw
hjd____'yw = hjd'yw
hjd_____'yw = hjd'yw
hjd______'yw = hjd'yw
hjd_______'yw = hjd'yw

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

hjd, hjd_, hjd__, hjd___, hjd____ :: forall target tt i eee e ee .
 Adjoint Functor target target (T'II'I P e) (T'I'II tt ee) =>
 (forall eee . Wrapper target (T'I'II tt ee `T'TT'I` T'II'I P e `T'I_` eee)) =>
 (forall eee . Wrapper target (I eee)) =>
 (forall eee . Wrapper target (T'II'I P e eee)) =>
 (forall eee . Wrapper target (T'I'II tt ee eee)) =>
 Contravariant Objective target eee (P i e) =>
 target i (tt ee eee)
hjd = fio @target (objective @T'II'I @target @eee @(P i e) `compose` super) `compose` super `compose` super `compose` component @target @I @(T'I'II tt ee `T'TT'I` T'II'I P e) `compose` wrap

hjd_ = fio @target (objective @T'II'I @target @eee @(P i e) `compose` super) `compose` super `compose` super `compose` component @target @I @(T'I'II tt ee `T'TT'I` T'II'I P e) `compose` wrap
hjd__ = fio @target (objective @T'II'I @target @eee @(P i e) `compose` super) `compose` super `compose` super `compose` component @target @I @(T'I'II tt ee `T'TT'I` T'II'I P e) `compose` wrap
hjd___ = fio @target (objective @T'II'I @target @eee @(P i e) `compose` super) `compose` super `compose` super `compose` component @target @I @(T'I'II tt ee `T'TT'I` T'II'I P e) `compose` wrap
hjd____ = fio @target (objective @T'II'I @target @eee @(P i e) `compose` super) `compose` super `compose` super `compose` component @target @I @(T'I'II tt ee `T'TT'I` T'II'I P e) `compose` wrap

hdj, hdj_, hdj__, hdj___, hdj____ :: forall target t tt i e ee .
 Adjoint Functor target target (T'II'I t e) (T'I'II tt ee) =>
 (forall eee . Wrapper target (T'II'I t e `T'TT'I` T'I'II tt ee `T'I_` eee)) =>
 (forall eee . Wrapper target (I eee)) =>
 (forall eee . Wrapper target (T'II'I t e eee)) =>
 (forall eee . Wrapper target (T'I'II tt ee eee)) =>
 target (t (tt ee i) e) i
hdj = super `compose` component @target @(T'II'I t e `T'TT'I` T'I'II tt ee) @I 
 `compose` wrap `compose` wrap `compose` foi @target wrap

hdj_ = hdj
hdj__ = hdj
hdj___ = hdj
hdj____ = hdj

hc, hc_, hc__, hc___, hc____, hc_____, hc______, hc_______, hc________
 :: forall target i tt o a .
 Adjoint Functor target target (T'II'I (P) a) (T'I'II tt a) =>
 (forall e . Wrapper target (T'II'I (P) a `T'TT'I` T'I'II tt a `T'I_` e)) =>
 (forall e . Wrapper target (I e)) =>
 (forall e . Wrapper target (T'II'I (P) a e)) =>
 (forall e . Wrapper target (T'I'II tt a e)) =>
 (forall e . Wrapper target (T'TT'I (T'I'II tt a) (T'II'I (P) a) e)) =>
 Covariant Objective target i (tt a o) =>
 target i (tt a o)
hc = objective @T'I'II @target @i @(tt a o)

hc_ = hc
hc__ = hc
hc___ = hc
hc____ = hc
hc_____ = hc
hc______ = hc
hc_______ = hc
hc________ = hc

hc'st, hc_'st, hc__'st, hc___'st, hc____'st, hc_____'st :: forall target i tt o a .
 Adjoint Functor target target (T'II'I (P) a) (T'I'II tt a) =>
 (forall e . Contravariant Endo Semi Functor target (T'II'I tt e)) =>
 (forall e . Wrapper target (T'II'I (P) a `T'TT'I` T'I'II tt a `T'I_` e)) =>
 (forall e . Wrapper target (I e)) =>
 (forall e . Wrapper target (T'II'I (P) a e)) =>
 (forall e . Wrapper target (T'I'II tt a e)) =>
 (forall e . Wrapper target (T'TT'I (T'I'II tt a) (T'II'I (P) a) e)) =>
 Covariant Objective target i (tt (Supertype a) o) =>
 Covariant Elicitable target a =>
 (forall e . Wrapper target (T'II'I tt o e)) =>
 target i (tt a o)
hc'st = fai @target super `compose` objective @T'I'II @target @i @(tt (Supertype a) o)

hc_'st = hc'st
hc__'st = hc'st
hc___'st = hc'st
hc____'st = hc'st
hc_____'st = hc'st

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
