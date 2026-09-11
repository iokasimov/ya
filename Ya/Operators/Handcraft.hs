{-# LANGUAGE AllowAmbiguousTypes #-}
module Ya.Operators.Handcraft where

import Ya.Algebra.Abstract
import Ya.Algebra.Definition
import Ya.Algebra.Effectful
import Ya.Algebra.Instances ()

import Ya.Operators.Mappings

infixl 9 `ho`, `ho'yioi`, `ho'yoo'ut`, `ho'yoi'ut`, `ho'yok`, `ho'yok'ut`, `ho'yokl`, `ho'yokl'ut`, `ho'yoikl` -- `ho'yokl'yokl`, `ho'yokl'yokl`, --, `ho'yoo`
 , `ho'vt`, `ho'st'vt`, `ho'ut`, `ho'ut'st`
 , `ho'st`
 , `ho'st'st`
 , `ho'hjd`
 , `ho'hjd'eq`
 -- , `ho'st'st'st`
 -- , `ho'st'st'st'st`
 -- , `ho'hd`
 -- , `ho'hd'hd`
 , `ho'ho'ut`
 , `ho'ho'ut'st`
infixl 8 `ho_`, `ho_'yoo'ut`, `ho_'yok`, `ho_'yok'ut`, `ho_'yokl`, `ho_'yokl'ut` --, `ho_'yokl'yokl`, `ho_'yokl'yokl`
 , `ho_'yoikl` --, `ho_'yoo`,
 , `ho_'vt`, `ho_'st'vt`, `ho_'ut`, `ho_'ut'st`
 , `ho_'st`
 , `ho_'st'st`
 , `ho_'hjd`
 , `ho_'hjd'eq`
 -- , `ho_'st'st'st`
 -- , `ho_'st'st'st'st`
 -- , `ho_'hd`
infixl 7 `ho__`, `ho__'yoo'ut`, `ho__'yok`, `ho__'yok'ut`, `ho__'yokl`, `ho__'yokl'ut` --, `ho__'yokl'yokl`, `ho__'yokl'yokl`
 , `ho__'yoikl` -- `ho__'yoo`,
 , `ho__'vt`, `ho__'st'vt`, `ho__'ut`, `ho__'ut'st`
 , `ho__'st`
 , `ho__'st'st`
 , `ho__'hjd`
 , `ho__'hjd'eq`
 -- , `ho__'st'st'st`
 -- , `ho__'st'st'st'st`
 -- , `ho__'hd`
infixl 6 `ho___`, `ho___'yoo'ut`, `ho___'yok`, `ho___'yok'ut`, `ho___'yokl`, `ho___'yokl'ut` --, `ho___'yokl'yokl`, `ho___'yokl'yokl`
 , `ho___'yoikl`
 , `ho___'vt`, `ho___'st'vt`, `ho___'ut`, `ho___'ut'st`
 , `ho___'st`
 , `ho___'st'st`
 , `ho___'hjd`
 , `ho___'hjd'eq`
 -- , `ho___'st'st'st`
 -- , `ho___'st'st'st'st`
 -- , `ho___'hd`
infixl 5 `ho____`, `ho____'yoo'ut`, `ho____'yok`, `ho____'yok'ut`, `ho____'yokl`, `ho____'yokl'ut` --, `ho____'yokl'yokl`, `ho____'yokl'yokl`
 , `ho____'yoikl`
 , `ho____'vt`, `ho____'st'vt`, `ho____'ut`, `ho____'ut'st`
 , `ho____'st`
 , `ho____'st'st`
 , `ho____'hjd`
 , `ho____'hjd'eq`
 -- , `ho____'st'st'st`
 -- , `ho____'st'st'st'st`
infixl 4 `ho_____`, `ho_____'yoo'ut`, `ho_____'yok`, `ho_____'yok'ut`, `ho_____'yokl`, `ho_____'yokl'ut` --, `ho_____'yokl'yokl`, `ho_____'yokl'yokl`
 , `ho_____'yoikl`
 , `ho_____'vt`, `ho_____'st'vt`, `ho_____'ut`, `ho_____'ut'st`
 , `ho_____'st`
 , `ho_____'st'st`
 , `ho_____'hjd`
 , `ho_____'hjd'eq`
 -- , `ho_____'st'st'st`
 -- , `ho_____'st'st'st'st`
 -- , `ho____'hd`
infixl 3 `ho______`
 , `ho______'vt`, `ho______'st'vt`, `ho______'ut`, `ho______'ut'st`
 , `ho______'st` -- , `ho______'yok`, `ho______'yok`, `ho______'yokl`, `ho______'yokl'yokl`, `ho______'yokl'yokl`, `ho______'yokl`
 , `ho______'yoikl`
 , `ho______'hjd`
 , `ho______'hjd'eq`
infixl 2 `ho_______`  -- `ho_______'yoo`, `ho_______'yok`, `ho_______'yok`, `ho_______'yokl`, `ho_______'yokl'yokl`, `ho_______'yokl'yokl`, `ho_______'yokl`
 , `ho_______'yoikl`
 , `ho_______'vt`, `ho_______'st'vt`, `ho_______'ut`, `ho_______'ut'st`
 , `ho_______'st`
 , `ho_______'st'st`
 , `ho_______'hjd`
 , `ho_______'hjd'eq`
 -- , `ho_______'st'st'st`
 -- , `ho_______'st'st'st'st`
 -- , `ho_____'hd`
infixl 1 `ho________` -- , `ho________'yok`, `ho________'yok`, `ho________'yokl`, `ho________'yokl` , `ho________'yokl'yokl`, `ho________'yokl'yokl`
 , `ho________'yoikl`
 , `ho________'vt`, `ho________'st'vt`, `ho________'ut`, `ho________'ut'st`
 , `ho________'st`
 , `ho________'st'st`
 , `ho________'hjd`
 , `ho________'hjd'eq`
 -- , `ho________'st'st'st`
 -- , `ho________'st'st'st'st`
 -- , `ho______'hd`
 -- , `ho________'yo`
 -- , `ho________'yoi`

infixl 8 `hor`, `hor'st`
infixl 7 `hor_`, `hor_'st`
infixl 6 `hor__`, `hor__'st`
infixl 5 `hor___`, `hor___'st`
infixl 4 `hor____`, `hor____'st`
infixl 3 `hor_____`, `hor_____'st`
infixl 2 `hor______`, `hor______'st`
infixl 1 `hor_______`, `hor_______'st`

infixl 9 `ha`, `ha'ho'ho'ut`, `ha'ho'ut`
 , `ha'yok`
 -- , `ha'yok`
 -- , `ha'kyo`
 -- , `ha'kyok`
 , `ha'yokl`
 -- , `ha'yokl`
 , `ha'st`
 , `ha'ut`
 , `ha'ut'st`
 , `ha'vt`
 , `ha'hjd`
 , `ha'hjd'eq`
 -- , `st'ha`
 -- , `ha'hd`
 -- , `ha'hd'hd`
infixl 8 `ha_`
 , `ha_'st`
 , `ha_'ut`
 , `ha_'ut'st`
 , `ha_'vt`
 , `ha_'hjd`
 , `ha_'hjd'eq`
 , `ha_'ho'ut`
 , `ha_'yok`
 -- , `ha_'yok`
 -- , `ha_'kyo`
 -- , `ha_'kyok`
 , `ha_'yokl`
 -- , `ha_'yokl`
infixl 7 `ha__`
 , `ha__'st`
 , `ha__'ut`
 , `ha__'ut'st`
 , `ha__'vt`
 , `ha__'hjd`
 , `ha__'hjd'eq`
 , `ha__'ho'ut`
 , `ha__'yok`
 -- , `ha__'yok`
 -- , `ha__'kyo`
 -- , `ha__'kyok`
 , `ha__'yokl`
 -- , `ha__'yokl`
infixl 6 `ha___`
 , `ha___'st`
 , `ha___'ut`
 , `ha___'ut'st`
 , `ha___'vt`
 , `ha___'hjd`
 , `ha___'hjd'eq`
 , `ha___'ho'ut`
 , `ha___'yok`
 -- , `ha___'yok`
 -- , `ha___'kyo`
 -- , `ha___'kyok`
 , `ha___'yokl`
 -- , `ha___'yokl`
infixl 5 `ha____`
 , `ha____'st`
 , `ha____'ut`
 , `ha____'ut'st`
 , `ha____'vt`
 , `ha____'hjd`
 , `ha____'hjd'eq`
 , `ha____'ho'ut`
 , `ha____'yok`
 -- , `ha____'yok`
 -- , `ha____'kyo`
 -- , `ha____'kyok`
 , `ha____'yokl`
 -- , `ha____'yokl`
infixl 4 `ha_____`
 , `ha_____'st`
 , `ha_____'ut`
 , `ha_____'ut'st`
 , `ha_____'vt`
 , `ha_____'hjd`
 , `ha_____'hjd'eq`
 , `ha_____'ho'ut`
 , `ha_____'yok`
 -- , `ha_____'yok`
 -- , `ha_____'kyo`
 -- , `ha_____'kyok`
 , `ha_____'yokl`
 -- , `ha_____'yokl`
infixl 3 `ha______`
 , `ha______'st`
 , `ha______'ut`
 , `ha______'ut'st`
 , `ha______'vt`
 , `ha______'hjd`
 , `ha______'hjd'eq`
 , `ha______'ho'ut`
 , `ha______'yok`
 -- , `ha______'yok`
 -- , `ha______'kyo`
 -- , `ha______'kyok`
 , `ha______'yokl`
 -- , `ha______'yokl`
infixl 2 `ha_______`
 , `ha_______'st`
 , `ha_______'ut`
 , `ha_______'ut'st`
 , `ha_______'vt`
 , `ha_______'hjd`
 , `ha_______'hjd'eq`
 , `ha_______'ho'ut`
 , `ha_______'yok`
 -- , `ha_______'yok`
 -- , `ha_______'kyo`
 -- , `ha_______'kyok`
 , `ha_______'yokl`
 -- , `ha_______'yokl`
infixl 1 `ha________`
 , `ha________'st`
 , `ha________'ut`
 , `ha________'ut'st`
 , `ha________'vt`
 , `ha________'hjd`
 , `ha________'hjd'eq`
 , `ha________'ho'ut`
 -- , `ha________'yok`
 -- , `ha________'yok`
 , `ha________'yokl`
 -- , `ha________'yokl`

infixl 8 `har`, `har'st`, `st'har`, `bt'har`, `bt'har'st`
infixl 7 `har_`, `har_'st`, `st'har_`, `bt'har_`, `bt'har_'st`
infixl 6 `har__`, `har__'st`, `st'har__`, `bt'har__`, `bt'har__'st`
infixl 5 `har___`, `har___'st`, `st'har___`, `bt'har___`, `bt'har___'st`
infixl 4 `har____`, `har____'st`, `st'har____`, `bt'har____`, `bt'har____'st`
infixl 3 `har_____`, `har_____'st`, `st'har_____`, `bt'har_____`, `bt'har_____'st`
infixl 2 `har______`, `har______'st`, `st'har______`, `bt'har______`, `bt'har______'st`
infixl 1 `har_______`, `har_______'st`, `st'har_______`, `bt'har_______`, `bt'har_______'st`

infixl 8 `hdj`
infixl 7 `hdj_`
infixl 6 `hdj__`
infixl 5 `hdj___`
infixl 4 `hdj____`

infixl 8 `hop`, `hop'tb`, `hop'hjd`, `hop'dcpp`, `hop'dcpp'yo'eq`, `hop'dcps`, `hop'dcps'has`, `hop'eq`, `hjd'dcps'has`
infixl 7 `hop_`, `hop_'tb`, `hop_'dcpp`, `hop_'dcpp'yo'eq`, `hop_'dcps`, `hop_'dcps'has`, `hop_'eq`, `hjd_'dcps'has`
infixl 6 `hop__`, `hop__'tb`, `hop__'dcpp`, `hop__'dcpp'yo'eq`, `hop__'dcps`, `hop__'dcps'has`, `hop__'eq`, `hjd__'dcps'has`
infixl 5 `hop___`, `hop___'tb`, `hop___'dcpp`, `hop___'dcpp'yo'eq`, `hop___'dcps`, `hop___'dcps'has`, `hop___'eq`, `hjd____'dcps'has`
infixl 4 `hop____`, `hop____'tb`, `hop____'dcpp`, `hop____'dcpp'yo'eq`, `hop____'dcps`, `hop____'dcps'has`, `hop____'eq`, `hjd_____'dcps'has`
infixl 3 `hop_____`, `hop_____'tb`, `hop_____'dcpp`, `hop_____'dcpp'yo'eq`, `hop_____'dcps`, `hop_____'dcps'has`, `hop_____'eq`, `hjd______'dcps'has`
infixl 2 `hop______`, `hop______'tb`, `hop______'dcpp`, `hop______'dcpp'yo'eq`, `hop______'dcps`, `hop______'dcps'has`, `hop______'eq`,  `hjd_______'dcps'has`

-- infixl 5 `hop__`, `hop__'tb`, `hop__'dcpp`, `hop__'dcpp'yo'eq`, `hop__'dcps`, `hop__'dcps'has`, `hop__'eq`, `hjd___'dcps'has`

infixl 8 `has`, `st'has`, `bt'has`
infixl 7 `has_`, `st'has_`, `bt'has_`
infixl 6 `has__`, `st'has__`, `bt'has__`
infixl 5 `has___`, `st'has___`, `bt'has___`
infixl 4 `has____`, `st'has____`, `bt'has____`
infixl 3 `has_____`, `st'has_____`, `bt'has_____`
infixl 2 `has______`, `st'has______`, `bt'has______`
infixl 1 `has_______`, `st'has_______`, `bt'has_______`

infixl 8 `hap`
infixl 7 `hap_`
infixl 6 `hap__`
infixl 5 `hap___`
infixl 4 `hap____`
infixl 3 `hap_____`
infixl 2 `hap______`
infixl 1 `hap_______`

infixl 8 `hjd`, `hjd'tb`, `st'hjd`, `st'hjd'tb`, `hjd'dcpp`, `hjd'dcpp'yo'eq`, `hjd'dcps`, `hjd'dcpw`, `hjd'eq` -- `hjd'dcpp'dcpp`,
infixl 7 `hjd_`, `hjd_'tb`, `st'hjd_`, `st'hjd_'tb`, `hjd_'dcpp`, `hjd_'dcpp'yo'eq`, `hjd_'dcps`, `hjd_'dcpw`, `hjd_'eq`
infixl 6 `hjd__`, `hjd__'tb`, `st'hjd__`, `st'hjd__'tb`, `hjd__'dcpp`, `hjd__'dcpp'yo'eq`, `hjd__'dcps`, `hjd__'dcpw`, `hjd__'eq`
infixl 5 `hjd___`, `hjd___'tb`, `st'hjd___`, `st'hjd___'tb`, `hjd___'dcpp`, `hjd___'dcpp'yo'eq`, `hjd___'dcps`, `hjd___'dcpw`, `hjd___'eq`
infixl 4 `hjd____`, `hjd____'tb`, `st'hjd____`, `st'hjd____'tb`, `hjd____'dcpp`, `hjd____'dcpp'yo'eq`, `hjd____'dcps`, `hjd____'dcpw`, `hjd____'eq`

infixl 8 `yi`
infixl 7 `yi_`
infixl 6 `yi__`
infixl 5 `yi___`
infixl 4 `yi____`
infixl 3 `yi_____`
infixl 2 `yi______`
infixl 1 `yi_______`

infixl 8 `yo`, `yo'st`, `yo'vt`, `yo'ut`, `yo'dcpp`, `yo'yoo`, `yo'yoo'ut`
infixl 7 `yo_`, `yo_'st`, `yoo`
infixl 6 `yo__`, `yo__'st`
infixl 5 `yo___`, `yo___'st`
infixl 4 `yo____`, `yo____'st`
infixl 3 `yo_____`, `yo_____'st`
infixl 2 `yo______`, `yo______'st`
infixl 1 `yo_______`, `yo_______'st`

infixl 7 `yok` --, `yok'yokl`, `yok'yokl`
infixl 6 `yok_` --, `yok_'yokl`, `yok_'yokl`
infixl 5 `yok__` --, `yok__'yokl`, `yok__'yokl`
infixl 4 `yok___` --, `yok___'yokl`, `yok___'yokl`
infixl 3 `yok____` --, `yok____'yokl`, `yok____'yokl`
infixl 2 `yok_____` --, `yok_____'yokl`, `yok_____'yokl`
infixl 1 `yok______` --, `yok______'yokl`, `yok______'yokl`

infixl 7 `kyo`
infixl 6 `_kyo`
infixl 5 `__kyo`
infixl 4 `___kyo`
infixl 3 `____kyo`
infixl 2 `_____kyo`
infixl 1 `______kyo`

infixl 6 `kyok`
infixl 5 `_kyok`, `kyok_`
infixl 4 `__kyok`, `_kyok_`, `kyok__`
infixl 3 `___kyok`, `__kyok_`, `_kyok__`, `kyok___`
infixl 2 `____kyok`, `___kyok_`, `__kyok__`, `_kyok___`, `kyok____`
infixl 1 `_____kyok`, `____kyok_`, `___kyok__`, `__kyok___`, `_kyok____`, `kyok_____`

infixl 5 `kyokl`
infixl 4 `kyokl_`, `_kyokl`
infixl 3 `kyokl__`
infixl 2 `kyokl___`
infixl 1 `kyokl____`

-- infixl 6 `yiok`

infixl 7 `yok'ut`
infixl 6 `yok_'ut`
infixl 5 `yok__'ut`
infixl 4 `yok___'ut`
infixl 3 `yok____'ut`
infixl 2 `yok_____'ut`
infixl 1 `yok______'ut`

infixl 6 `yokl`, `yokl'yokl`
infixl 5 `yokl_`
infixl 4 `yokl__`
infixl 3 `yokl___`
infixl 2 `yokl____`
infixl 1 `yokl_____`

infixl 6 `yokl'ut`
infixl 5 `yokl_'ut`
infixl 4 `yokl__'ut`
infixl 3 `yokl___'ut`
infixl 2 `yokl____'ut`
infixl 1 `yokl_____'ut`

infixl 5 `yiokl` --, `yiokl'yokl`
-- infixl 5 `yoikl`, `yoikl'yokl`

infixl 8 `ya`, `ya'ut`, `ya'vt`

infixl 7 `yoo'ut`

infixl 6 `dcpp`, `dcpp'yo`, `dcpp'dcpp`, `dcpp'dcpp'yo`, `dcpp'dcps` --, `dcpdcppyok`, `dcpp'yokl`, `dcpp'yo'hd`, `dcpp'yo'ut`, `dcpp'dcpp'jt`, `dcpp'dcpp'jt'yok`
-- infixl 7 `dcpp_'yo`-- , `yip`, `yip'yo`, `yip'dcpp`, `yip'yip`, `yip'yis`

infixl 6 `dcps`, `dcps'yo` -- `dcps'yo'ut`
-- infixl 7 `yis`

infixl 6 `dcpw`, `dcpw'yo`, `dcpw'yokl`

infixl 7 `yoi`, `yio'st`, `yio'vt`, `yio'st'vt`, `yio'ut`, `yio'ut'st`, `yio'hjd`, `yio'hjd'eq`

infixl 7 `yai`, `yai'st`, `yai'vt`, `yai'ut`, `yai'ut'st`, `yai'hjd`, `yai'hjd'eq` -- `yai'yokl`

infixl 7 `yio`, `yio'dcpp`, `yio'yoikl`, `yio'yok` , `yio'yokl` -- `yio'yokl'yokl`, `yio'yokl'yokl`

-- infixl 6 `yioi`

infixl 8 `eq`
infixl 7 `eq_`
infixl 6 `eq__`
infixl 5 `eq___`
infixl 4 `eq____`
infixl 3 `eq_____`
infixl 2 `eq______`
infixl 1 `eq_______`
infixl 0 `eq________`

infixl 7 `yor`, `yor'st`
infixl 7 `ryo`

infixl 6 `ryok`
infixl 5 `ryok_`
infixl 4 `ryok__`
infixl 3 `ryok___`

infixl 5 `ryokl`
infixl 4 `ryokl_`
infixl 3 `ryokl__`
infixl 2 `ryokl___`

infixl 6 `yor_`
infixl 6 `_ryo`

infixl 5 `__ryo`
infixl 4 `___ryo`
infixl 3 `____ryo`
infixl 2 `_____ryo`
infixl 1 `______ryo`

infixl 6 `yior`, `yior'st`
infixl 6 `yoir`, `yoir'st`
infixl 6 `yoor`, `yoor'st`

infixl 7 `yar`, `yar'st`
infixl 7 `rya`

infixl 6 `_rya`
infixl 6 `yar_`

infixl 6 `yiar`, `yiar'st`
infixl 6 `yair`, `yair'st`, `st'yair`, `bt'yair`, `bt'yair'st`
infixl 6 `yaar`, `yaar'st`

infixl 6 `ryio`
infixl 6 `ryoi`
infixl 6 `ryoo`

infixl 5 `_ryio`
infixl 5 `_ryoi`
infixl 5 `_ryoo`

yi, yi_, yi__, yi___, yi____, yi_____, yi______, yi_______
 :: forall source target t a o .
 Covariant Yoneda Functor source target I =>
 Hom Functor target =>
 (forall e ee . Wrapper target (T'I'II source e ee)) =>
 (forall e ee . Wrapper target (T'I'II target e ee)) =>
 (forall e ee . Wrapper target (T'II'I target ee e)) =>
 (forall e . Wrapper target (I e)) =>
 target a (target (source a o) o)
yi = fai @target subtype
 `compose` fio @target supertype
 `compose` yoneda @T'I'II @Functor
 `compose` subtype @target @(I a)

yi_ = yi
yi__ = yi
yi___ = yi
yi____ = yi
yi_____ = yi
yi______ = yi
yi_______ = yi

{-
yi'
 :: forall source target t i r .
 Covariant Yoneda Functor source target I =>
 Hom Functor target =>
 (forall e ee . Wrapper target (T'I'II source e ee)) =>
 (forall e ee . Wrapper target (T'I'II target e ee)) =>
 (forall e ee . Wrapper target (T'II'I target ee e)) =>
 (forall e . Wrapper target (I e)) =>
 target (t i) (target (source (t i) r) r)
yi' = fai @target subtype
 `compose` fio @target supertype
 `compose` yoneda @T'I'II @Functor
 `compose` subtype @target @(I _)
-}

yo, yo_, yo__, yo___, yo____, yo_____, yo______, yo_______
 :: forall source target t a o .
 Hom Functor target =>
 Covariant Yoneda Functor source target t =>
 (forall e ee . Wrapper target (T'I'II source e ee)) =>
 (forall e ee . Wrapper target (T'II'I target e ee)) =>
 target (t a) (target (source a o) (t o))
yo = fai @target subtype `compose` yoneda @T'I'II @Functor

yo_ = yo
yo__ = yo
yo___ = yo
yo____ = yo
yo_____ = yo
yo______ = yo
yo_______ = yo

yo'st, yo_'st, yo__'st, yo___'st, yo____'st, yo_____'st, yo______'st, yo_______'st
 :: forall source target t a o .
 Hom Functor target =>
 (forall e . Contravariant Semi Functor source target (T'II'I source e)) =>
 Covariant Yoneda Functor source target t =>
 (forall e ee . Wrapper target (T'I'II source e ee)) =>
 (forall e ee . Wrapper target (T'II'I source e ee)) =>
 (forall e ee . Wrapper target (T'II'I target e ee)) =>
 (forall e . Wrapper source e) =>
 target (t a) (target (source (Supertype a) o) (t o))
yo'st = fai @target (fai @source supertype) `compose` yo @source @target @t

yo_'st = yo'st
yo__'st = yo'st
yo___'st = yo'st
yo____'st = yo'st
yo_____'st = yo'st
yo______'st = yo'st
yo_______'st = yo'st

yo'vt
 :: forall target t i a o .
 Hom Functor target =>
 Covariant Endo Yoneda Functor target t =>
 Initial target =>
 (forall e . Wrapper target (target Void e)) =>
 (Supertype (target Void o) ~ Unit) =>
 (forall e ee . Wrapper target (T'II'I target e ee)) =>
 (forall e ee . Wrapper target (T'I'II target e ee)) =>
 (forall e ee . Wrapper target (T'I'II target e ee)) =>
 (forall e ee . Wrapper target (T'II'I target e ee)) =>
 target (t Void) (target Unit (t o))
yo'vt = fai @target (fai @target initial `compose` subtype @target @(target Void o)) `compose` yo @target @target @t

yo'ut
 :: forall target t i a o .
 Hom Functor target =>
 Covariant Endo Yoneda Functor target t =>
 Terminal target =>
 (forall e . Wrapper target (target Unit e)) =>
 (Supertype (target Unit o) ~ o) =>
 (forall e ee . Wrapper target (T'II'I target e ee)) =>
 (forall e ee . Wrapper target (T'I'II target e ee)) =>
 (forall e ee . Wrapper target (T'I'II target e ee)) =>
 (forall e ee . Wrapper target (T'II'I target e ee)) =>
 target (t a) (target o (t o))
yo'ut = fai @target (fai @target terminal `compose` subtype @target @(target Unit o)) `compose` yo @target @target @t

yo'yoo :: forall source target t tt a o .
 Covariant Yoneda Functor source target (T'I t) =>
 Covariant Semi Functor source source (T'I'I tt) =>
 (forall e . Wrapper source (T'I'I tt e)) =>
 (forall e ee . Wrapper target (T'I'II source e ee)) =>
 (forall e ee . Wrapper target (T'II'I target e ee)) =>
 (forall e . Contravariant Semi Functor (AR) target (T'II'I target e)) =>
 Hom Functor target =>
 target (t (tt a a)) (target (source a o) (t (tt o o)))
yo'yoo = fai (foo @source @source @tt) `compose` yo @source @target

yo'yoo'ut :: forall target t tt a aa o .
 Covariant Yoneda Functor target target (T'I t) =>
 Covariant Functor target target (T'I'II tt a) =>
 Covariant Functor target target (T'II'I tt o) =>
 Hom Functor target =>
 (forall e . Contravariant Semi Functor (AR) target (T'II'I target e)) =>
 (forall e ee . Wrapper target (T'I'II tt e ee)) =>
 (forall e ee . Wrapper target (T'II'I tt e ee)) =>
 (forall e ee . Wrapper target (T'I'II target e ee)) =>
 (forall e ee . Wrapper target (T'II'I target e ee)) =>
 (forall e . Wrapper (AR) (target Unit e)) =>
 Terminal target =>
 Contravariant Functor (AR) (AR) (T'II'I target (t (tt o o))) =>
 target (t (tt a aa)) (target (Supertype (target Unit o)) (t (tt o o)))
yo'yoo'ut = fai (fuu @target @target @tt) `compose` yo @target @target

yoo :: forall source target t a o .
 Hom Functor target =>
 Covariant Yoneda Functor source target (T'I'I t) =>
 (forall e . Wrapper target (T'I'I t e)) =>
 (forall e ee . Wrapper target (T'I'II source e ee)) =>
 (forall e ee . Wrapper target (T'I'II target e ee)) =>
 (forall e ee . Wrapper target (T'II'I target e ee)) =>
 target (t a a) (target (source a o) (t o o))
yoo = fio @target supertype `compose` yo @source @target @(T'I'I t) `compose` subtype

yoi
 :: forall source target t i a o .
 Hom Functor target =>
 Covariant Yoneda Functor source target (T'II'I t i) =>
 (forall e ee . Wrapper target (T'I'II source e ee)) =>
 (forall e . Wrapper target (T'II'I t i e)) =>
 (forall e ee . Wrapper target (T'I'II target e ee)) =>
 (forall e ee . Wrapper target (T'II'I target e ee)) =>
 target (t a i) (target (source a o) (t o i))
yoi = fio @target supertype `compose` yo @source @target @(T'II'I t i) `compose` subtype

-- TODO: add Hom functor aliases here
yio, ho, ho_, ho__, ho___, ho____, ho_____, ho______, ho_______, ho________
 :: forall source target t i a o .
 Hom Functor target =>
 Covariant Yoneda Functor source target (T'I'II t i) =>
 (forall e ee . Wrapper target (T'I'II source e ee)) =>
 (forall e ee . Wrapper target (T'I'II target e ee)) =>
 (forall e ee . Wrapper target (T'II'I target e ee)) =>
 (forall e . Wrapper target (T'I'II t i e)) =>
 target (t i a) (target (source a o) (t i o))
yio = fio @target supertype `compose` yo @source @target @(T'I'II t i) `compose` subtype

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
 Hom Functor target =>
 Covariant Yoneda Functor source target (T'I'II t i) =>
 Contravariant Semi Functor source target (T'II'I source o) =>
 Covariant Semi Functor source target (T'I'II source o) =>
 Covariant Elicitable source a =>
 (forall e ee . Wrapper target (T'II'I target e ee)) =>
 (forall e ee . Wrapper target (T'I'II target e ee)) =>
 (forall e ee . Wrapper target (T'I'II source e ee)) =>
 (forall e ee . Wrapper target (T'II'I source e ee)) =>
 (forall e ee . Wrapper target (T'I'II t e ee)) =>
 target (t i a) (target (source (Supertype a) o) (t i o))
yio'st = fai @target (fai @source supertype) `compose` yio @source @target @t

ho'st = yio'st
ho_'st = yio'st
ho__'st = yio'st
ho___'st = yio'st
ho____'st = yio'st
ho_____'st = yio'st
ho______'st = yio'st
ho_______'st = yio'st
ho________'st = yio'st

yio'vt, ho'vt, ho_'vt, ho__'vt, ho___'vt, ho____'vt, ho_____'vt, ho______'vt, ho_______'vt, ho________'vt
 :: forall target t i a o .
 Hom Functor target =>
 Covariant Endo Yoneda Functor target (T'I'II t i) =>
 Hom Functor target =>
 Initial target =>
 (forall e . Wrapper target (target Void e)) =>
 (Supertype (target Void o) ~ Unit) =>
 (forall e ee . Wrapper target (T'II'I target e ee)) =>
 (forall e ee . Wrapper target (T'I'II target e ee)) =>
 (forall e ee . Wrapper target (T'I'II target e ee)) =>
 (forall e ee . Wrapper target (T'II'I target e ee)) =>
 (forall e ee . Wrapper target (T'I'II t e ee)) =>
 target (t i Void) (target Unit (t i o))
yio'vt = fai @target (fai @target initial `compose` subtype @target @(target Void o)) `compose` yio @target @target @t

ho'vt = yio'vt
ho_'vt = yio'vt
ho__'vt = yio'vt
ho___'vt = yio'vt
ho____'vt = yio'vt
ho_____'vt = yio'vt
ho______'vt = yio'vt
ho_______'vt = yio'vt
ho________'vt = yio'vt

yio'st'vt, ho'st'vt, ho_'st'vt, ho__'st'vt, ho___'st'vt, ho____'st'vt, ho_____'st'vt, ho______'st'vt, ho_______'st'vt, ho________'st'vt
 :: forall target t i a o .
 Hom Functor target =>
 Covariant Endo Yoneda Functor target (T'I'II t i) =>
 Hom Functor target =>
 Initial target =>
 (forall e . Wrapper target (target Void e)) =>
 (Supertype (target Void o) ~ Unit) =>
 Covariant Elicitable target a =>
 (Supertype a ~ Void) =>
 (forall e ee . Wrapper target (T'II'I target e ee)) =>
 (forall e ee . Wrapper target (T'I'II target e ee)) =>
 (forall e ee . Wrapper target (T'I'II target e ee)) =>
 (forall e ee . Wrapper target (T'II'I target e ee)) =>
 (forall e ee . Wrapper target (T'I'II t e ee)) =>
 target (t i a) (target Unit (t i o))
yio'st'vt = fai @target (fai @target (initial `compose` supertype) `compose` subtype @target @(target Void o)) `compose` yio @target @target @t

ho'st'vt = yio'st'vt
ho_'st'vt = yio'st'vt
ho__'st'vt = yio'st'vt
ho___'st'vt = yio'st'vt
ho____'st'vt = yio'st'vt
ho_____'st'vt = yio'st'vt
ho______'st'vt = yio'st'vt
ho_______'st'vt = yio'st'vt
ho________'st'vt = yio'st'vt

yio'ut, ho'ut, ho_'ut, ho__'ut, ho___'ut, ho____'ut, ho_____'ut, ho______'ut, ho_______'ut, ho________'ut
 :: forall target t i a o .
 Hom Functor target =>
 Covariant Endo Yoneda Functor target (T'I'II t i) =>
 Hom Functor target =>
 Terminal target =>
 (forall e . Wrapper target (target Unit e)) =>
 (Supertype (target Unit o) ~ o) =>
 (forall e ee . Wrapper target (T'II'I target e ee)) =>
 (forall e ee . Wrapper target (T'I'II target e ee)) =>
 (forall e ee . Wrapper target (T'I'II target e ee)) =>
 (forall e ee . Wrapper target (T'II'I target e ee)) =>
 (forall e ee . Wrapper target (T'I'II t e ee)) =>
 target (t i a) (target o (t i o))
yio'ut = fai @target (fai @target terminal `compose` subtype @target @(target Unit o)) `compose` yio @target @target @t

ho'ut = yio'ut
ho_'ut = yio'ut
ho__'ut = yio'ut
ho___'ut = yio'ut
ho____'ut = yio'ut
ho_____'ut = yio'ut
ho______'ut = yio'ut
ho_______'ut = yio'ut
ho________'ut = yio'ut

yio'ut'st, ho'ut'st, ho_'ut'st, ho__'ut'st, ho___'ut'st, ho____'ut'st, ho_____'ut'st, ho______'ut'st, ho_______'ut'st, ho________'ut'st
 :: forall target t i a o .
 Hom Functor target =>
 Covariant Endo Yoneda Functor target (T'I'II t i) =>
 Terminal target =>
 (forall e . Wrapper target (target Unit e)) =>
 (Supertype (target Unit o) ~ o) =>
 (Wrapper target o) =>
 (forall e ee . Wrapper target (T'I'II target e ee)) =>
 (forall e ee . Wrapper target (T'II'I target e ee)) =>
 (forall e ee . Wrapper target (T'I'II t e ee)) =>
 target (t i a) (target o (t i (Supertype o)))
yio'ut'st = fio @target (fio @target supertype)
 `compose` fai @target (fai @target terminal `compose` subtype @target @(target Unit o))
 `compose` yio @target @target @t

ho'ut'st = yio'ut'st
ho_'ut'st = yio'ut'st
ho__'ut'st = yio'ut'st
ho___'ut'st = yio'ut'st
ho____'ut'st = yio'ut'st
ho_____'ut'st = yio'ut'st
ho______'ut'st = yio'ut'st
ho_______'ut'st = yio'ut'st
ho________'ut'st = yio'ut'st

yai'vt, ha'vt, ha_'vt, ha__'vt, ha___'vt, ha____'vt, ha_____'vt, ha______'vt, ha_______'vt, ha________'vt
 :: forall target t i a o .
 Hom Functor target =>
 Contravariant Endo Yoneda Functor target (T'II'I t i) =>
 Initial target =>
 (forall e . Wrapper target (target Void e)) =>
 (Supertype (target Void a) ~ Unit) =>
 (forall e ee . Wrapper target (T'I'II target e ee)) =>
 (forall e ee . Wrapper target (T'II'I target e ee)) =>
 (forall e ee . Wrapper target (T'II'I t e ee)) =>
 target (t a i) (target Unit (t Void i))
yai'vt = fai @target (fai @target initial `compose` subtype @target @(target Void a))
 `compose` yai @target @target @t

ha'vt = yai'vt @target @t @i @a @o
ha_'vt = yai'vt @target @t @i @a @o
ha__'vt = yai'vt @target @t @i @a @o
ha___'vt = yai'vt @target @t @i @a @o
ha____'vt = yai'vt @target @t @i @a @o
ha_____'vt = yai'vt @target @t @i @a @o
ha______'vt = yai'vt @target @t @i @a @o
ha_______'vt = yai'vt @target @t @i @a @o
ha________'vt = yai'vt @target @t @i @a @o

yai'ut, ha'ut, ha_'ut, ha__'ut, ha___'ut, ha____'ut, ha_____'ut, ha______'ut, ha_______'ut, ha________'ut
 :: forall target t i a o .
 Hom Functor target =>
 Contravariant Endo Yoneda Functor target (T'II'I t i) =>
 Terminal target =>
 (forall e . Wrapper target (target Unit e)) =>
 (Supertype (target Unit a) ~ a) =>
 (forall e ee . Wrapper target (T'I'II target e ee)) =>
 (forall e ee . Wrapper target (T'II'I target e ee)) =>
 (forall e ee . Wrapper target (T'II'I t e ee)) =>
 target (t a i) (target a (t o i))
yai'ut = fai @target (fai @target terminal `compose` subtype @target @(target Unit a))
 `compose` yai @target @target @t

ha'ut = yai'ut
ha_'ut = yai'ut
ha__'ut = yai'ut
ha___'ut = yai'ut
ha____'ut = yai'ut
ha_____'ut = yai'ut
ha______'ut = yai'ut
ha_______'ut = yai'ut
ha________'ut = yai'ut

yai'ut'st, ha'ut'st, ha_'ut'st, ha__'ut'st, ha___'ut'st, ha____'ut'st, ha_____'ut'st, ha______'ut'st, ha_______'ut'st, ha________'ut'st
 :: forall target t i a o .
 Hom Functor target =>
 Contravariant Endo Yoneda Functor target (T'II'I t i) =>
 Terminal target =>
 (forall e . Wrapper target (target Unit e)) =>
 (Supertype (target Unit a) ~ a) =>
 (Covariant Elicitable target (Supertype o)) =>
 (forall e ee . Wrapper target (T'I'II target e ee)) =>
 (forall e ee . Wrapper target (T'II'I target e ee)) =>
 (forall e ee . Wrapper target (T'II'I t e ee)) =>
 target (t a i) (target (a) (t (Supertype o) i))
yai'ut'st = fio @target (fai @target supertype)
 `compose` fai @target (fai @target terminal `compose` subtype @target @(target Unit a))
 `compose` yai @target @target @t

ha'ut'st = yai'ut'st @target @t @i @a @o
ha_'ut'st = yai'ut'st @target @t @i @a @o
ha__'ut'st = yai'ut'st @target @t @i @a @o
ha___'ut'st = yai'ut'st @target @t @i @a @o
ha____'ut'st = yai'ut'st @target @t @i @a @o
ha_____'ut'st = yai'ut'st @target @t @i @a @o
ha______'ut'st = yai'ut'st @target @t @i @a @o
ha_______'ut'st = yai'ut'st @target @t @i @a @o
ha________'ut'st = yai'ut'st @target @t @i @a @o

yoo'ut :: forall target t a o .
 Terminal target =>
 Covariant Yoneda Functor target target (T'I'I t) =>
 Hom Functor target =>
 (forall e ee . Wrapper target (T'I'II target e ee)) =>
 (forall e ee . Wrapper target (T'II'I target e ee)) =>
 (forall e . Wrapper target (T'I'I t e)) =>
 (forall e . Wrapper target (target Unit e)) =>
 (Supertype (target Unit o) ~ o) =>
 target (t a a) (target o (t o o))
yoo'ut = fio @target supertype `compose` yo'ut @target `compose` subtype @target @(T'I'I t _)

ya :: forall source target t a o .
 Hom Functor target =>
 Contravariant Yoneda Functor source target t =>
 (forall e ee . Wrapper target (T'II'I source e ee)) =>
 (forall e ee . Wrapper target (T'II'I target e ee)) =>
 target (t a) (target (source o a) (t o))
ya = fai @target subtype `compose` yoneda @T'II'I @Functor

ya'vt
 :: forall target t i a o .
 Hom Functor target =>
 Contravariant Endo Yoneda Functor target t =>
 Initial target =>
 (forall e . Wrapper target (target Void e)) =>
 (Supertype (target Void a) ~ Unit) =>
 (forall e ee . Wrapper target (T'I'II target e ee)) =>
 (forall e ee . Wrapper target (T'II'I target e ee)) =>
 target (t a) (target Unit (t Void))
ya'vt = fai @target (fai @target initial `compose` subtype @target @(target Void a))
 `compose` ya @target @target @t

ya'ut
 :: forall target t i a o .
 Hom Functor target =>
 Contravariant Endo Yoneda Functor target t =>
 Terminal target =>
 (forall e . Wrapper target (target Unit e)) =>
 (Supertype (target Unit a) ~ a) =>
 (forall e ee . Wrapper target (T'I'II target e ee)) =>
 (forall e ee . Wrapper target (T'II'I target e ee)) =>
 target (t a) (target a (t o))
ya'ut = fai @target (fai @target terminal `compose` subtype @target @(target Unit a))
 `compose` ya @target @target @t

yai, ha, ha_, ha__, ha___, ha____, ha_____, ha______, ha_______, ha________ :: forall source target t i a o .
 Hom Functor target =>
 Contravariant Yoneda Functor source target (T'II'I t i) =>
 (forall e ee . Wrapper target (T'II'I source e ee)) =>
 (forall e ee . Wrapper target (T'I'II target e ee)) =>
 (forall e ee . Wrapper target (T'II'I target e ee)) =>
 (forall e ee . Wrapper target (T'II'I t e ee)) =>
 target (t a i) (target (source o a) (t o i))
yai = fio @target supertype `compose` ya @source @target @(T'II'I t i) `compose` subtype

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

{-
yio'hjd, ho'hjd :: forall source target t tt ttt i ii iii a o .
 (forall e . Covariant Endo Semi Functor target (T'I'II target e)) =>
 (forall e . Covariant Semi Functor (AR) target (T'I'II target e)) =>
 Hom Functor target =>
 Contravariant Endo Semi Functor (AR) (T'II'I target (t o i)) =>
 Adjoint Functor source source (T'II'I tt ii) (T'I'II ttt iii) =>
 Covariant Functor source (AR) (T'I'II target (source (ttt iii (t o i)) a)) =>
 Covariant Yoneda Functor source target (T'I'II t i) =>
 Covariant Endo Semi Functor source (T'II'I tt ii) =>
 Covariant Endo Semi Functor source (T'I'II ttt iii) =>
 Contravariant Endo Semi Functor (AR) (T'II'I target (t i (ttt iii o))) =>
 (forall e ee . Wrapper target (T'I'II source e ee)) =>
 (forall e ee . Wrapper target (T'I'II target e ee)) =>
 (forall e ee . Wrapper target (T'II'I target e ee)) =>
 (forall e . Wrapper source (I e)) =>
 (forall e . Wrapper target (T'I'II t i e)) =>
 (forall e . Wrapper source (T'I'II ttt iii e)) =>
 (forall e . Wrapper source (T'II'I tt ii e)) =>
 (forall e . Wrapper source (T'TT'I (T'I'II ttt iii) (T'II'I tt ii) e)) =>
 target (t i a) (target (source (tt a ii) o) (t i (ttt iii o)))
yio'hjd = fai hjd `compose` yio @source @target

-- -- t i a -> target (source (a `P` ii) o) (t i (ii `AR` o))

ho'hjd = yio'hjd
-}

-- yio'yij'yij, ho'hj'hj :: forall source target t tt ttt tttt ttttt i ii iii iiii iiiii a o .
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
 Hom Functor target =>
 (forall e . Covariant Endo Semi Functor target (T'I'II target e)) =>
 Contravariant Yoneda Functor source target (T'I'II t i) =>
 (forall e ee . Wrapper target (T'II'I source e ee)) =>
 (forall e ee . Wrapper target (T'II'I target e ee)) =>
 (forall e ee . Wrapper target (T'I'II target e ee)) =>
 (forall e ee . Wrapper target (T'I'II t e ee)) =>
 target (t i a) (target (source o a) (t i o))
yia = fio @target supertype `compose` ya @source @target @(T'I'II t i) `compose` subtype

yok, yok_, yok__, yok___, yok____, yok_____, yok______
 :: forall source target t tt ll a o .
 Hom Functor target =>
 Covariant Yoneda Functor source target t =>
 Component target (t `T'TT'I` tt `L` tt `T` ll) t =>
 (forall e ee . Wrapper target (T'I'II source e ee)) =>
 (forall e . Wrapper target (t `T'TT'I` tt `L` tt `T` ll `T'I_` e)) =>
 (forall e ee . Wrapper target (T'I'II target e ee)) =>
 (forall e ee . Wrapper target (T'II'I target e ee)) =>
 target (t a) (target (source a (tt `L` tt `T` ll `T` o)) (t o))
yok = fio (component @target @(T'TT'I t (tt `L` tt `T` ll)) `compose` subtype @target @(T'TT'I t (tt `L` tt `T` ll) _)) `compose` yo

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
-- yok'st x = yok @source @target x `compose` fai @source supertype

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
-- yok'st'st x = yok @source @target x `compose` fai @source supertype'st

-- yok_'st'st = yok'st'st
-- yok__'st'st = yok'st'st
-- yok___'st'st = yok'st'st
-- yok____'st'st = yok'st'st
-- yok_____'st'st = yok'st'st
-- yok______'st'st = yok'st'st

yok'ut, yok_'ut, yok__'ut, yok___'ut, yok____'ut, yok_____'ut, yok______'ut
 :: forall target tt t ll a o .
 Terminal target =>
 Hom Functor target =>
 (forall e . Covariant Endo Semi Functor target (T'I'II target e)) =>
 Covariant Yoneda Functor target target t =>
 Covariant Endo Transformation Functor target (T'TT'I t (tt `L` tt `T` ll)) t =>
 (forall e . Wrapper target ((t `T'TT'I` tt `L` tt `T` ll) e)) =>
 (forall e ee . Wrapper target (T'I'II target e ee)) =>
 (forall e ee . Wrapper target (T'II'I target e ee)) =>
 (forall e . Wrapper target (target Unit e)) =>
 (Supertype (target Unit (tt `L` tt `T` ll `T` o)) ~ (tt `L` tt `T` ll `T` o)) =>
 target (t a) (target (tt `L` tt `T` ll `T` o) (t o))
yok'ut = fio (component @target @(T'TT'I t (tt `L` tt `T` ll)) `compose` subtype @target @(T'TT'I t (tt `L` tt `T` ll) _)) `compose` yo'ut

yok_'ut = yok'ut @target @tt
yok__'ut = yok'ut @target @tt
yok___'ut = yok'ut @target @tt
yok____'ut = yok'ut @target @tt
yok_____'ut = yok'ut @target @tt
yok______'ut = yok'ut @target @tt

{-
kya, _kya, __kya, ___kya, ____kya, _____kya, ______kya :: forall source target t tt ll a o .
 Component target t (t `T'TT'I` tt `L` tt `T` ll) =>
 Covariant Yoneda Functor source target t =>
 Hom Functor target =>
 (forall e . Contravariant Semi Functor source target (T'II'I source e)) =>
 (forall e . Covariant Semi Functor source target (T'I'II source e)) =>
 (forall e ee . Wrapper target (T'I'II source e ee)) =>
 (forall e ee . Wrapper target (T'II'I source e ee)) =>
 (forall e ee . Wrapper target (T'II'I target e ee)) =>
 (forall e . Wrapper source (I e)) =>
 (forall e . Wrapper source (I `L` tt `T` ll `T'I` e)) =>
 (forall e . Wrapper source (tt `L` tt `T` ll `T'I` e)) =>
 (forall e . Wrapper target (t `T'TT'I` tt `L` tt `T` ll `T'I_` e)) =>
 target (t a) (target (source (I `L` tt `T` ll `T` o) (tt a)) (t o))
kya = fai @target (fai @source supertype `compose` fio @source (supertype @_ @(I _) `compose` supertype))
 `compose` ya @source @target @t
 `compose` supertype `compose` component @target @t @(t `T'TT'I` tt `L` tt `T` ll)

_kya = kya
__kya = kya
___kya = kya
____kya = kya
_____kya = kya
______kya = kya
-}

kyo, _kyo, __kyo, ___kyo, ____kyo, _____kyo, ______kyo :: forall source target t tt ll a o .
 Component target t (t `T'TT'I` tt `L` tt `T` ll) =>
 Covariant Yoneda Functor source target t =>
 Hom Functor target =>
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
kyo = fai @target (fai @source supertype `compose` fio @source (supertype @_ @(I _) `compose` supertype))
 `compose` yo @source @target @t
 `compose` supertype `compose` component @target @t @(t `T'TT'I` tt `L` tt `T` ll)

_kyo = kyo
__kyo = kyo
___kyo = kyo
____kyo = kyo
_____kyo = kyo
______kyo = kyo

-- kyo x = fai @target (fai @source supertype `compose` fio @source (supertype @_ @(I _) `compose` supertype))
--  `compose` yo @source @target @t
--  `compose` supertype (component @(AR) @t @(t `T'TT'I` tt `L` tt `T` ll) x)

kyok, _kyok, kyok_, __kyok, _kyok_, kyok__, ___kyok, __kyok_, _kyok__, kyok___, ____kyok, ___kyok_, __kyok__, _kyok___, kyok____, _____kyok, ____kyok_, ___kyok__, __kyok___, _kyok____, kyok_____
 :: forall source target t tt ttt l ll lll a o .
 Hom Functor target =>
 Covariant Yoneda Functor source target t =>
 Component target t (t `T'TT'I` tt `L` tt `T` ll) =>
 Component source (t `T'TT'I` ttt `L` ttt `T` lll) t =>
 (forall e . Contravariant Functor source target (T'II'I source e)) =>
 (forall e . Covariant Functor source target (T'I'II source e)) =>
 (forall e . Covariant Functor source target (T'I'II target e)) =>
 (forall e . Covariant Functor source (AR) (T'I'II target e)) =>
 (forall e ee . Wrapper target (T'I'II source e ee)) =>
 (forall e ee . Wrapper target (T'II'I source e ee)) =>
 (forall e . Wrapper source (I `L` tt `T` ll `T` e)) =>
 (forall e . Wrapper source (tt `L` tt `T` ll `T` e)) =>
 (forall e . Wrapper source (t `TT'T'I` ttt `T'I_` e)) =>
 (forall e . Wrapper target (t `T'TT'I` tt `L` tt `T` ll `T'I_` e)) =>
 (forall e . Wrapper target (t `TT'T'I` ttt `T'I_` e)) =>
 (forall e . Wrapper source (t `T'TT'I` ttt `L` ttt `T` lll `T'I_` e)) =>
 (forall e . Wrapper source (I e)) =>
 (forall e ee . Wrapper target (T'I'II target e ee)) =>
 (forall e ee . Wrapper target (T'II'I target e ee)) =>
 target (t a) (target (source (tt a) (I `L` tt `T` ll `T'I` ttt `L` ttt `T` lll `T` o)) (t o))
kyok = fio @source (component @source @(t `T'TT'I` ttt `L` ttt `T` lll) @t `compose` subtype)
 `compose` kyo @source @target @t @tt @ll

_kyok = kyok
kyok_ = kyok
__kyok = kyok
_kyok_ = kyok
kyok__ = kyok
___kyok = kyok
__kyok_ = kyok
_kyok__ = kyok
kyok___ = kyok
____kyok = kyok
___kyok_ = kyok
__kyok__ = kyok
_kyok___ = kyok
kyok____ = kyok
_____kyok = kyok
____kyok_ = kyok
___kyok__ = kyok
__kyok___ = kyok
_kyok____ = kyok
kyok_____ = kyok

kyokl, kyokl_, kyokl__, kyokl___, kyokl____, _kyokl :: forall source target t tt ttt l ll lll a o .
 Hom Functor target =>
 Covariant Yoneda Functor source target t =>
 Component target t (t `T'TT'I` tt `L` tt `T` ll) =>
 Component source (t `T'TT'I` ttt `L` ttt `T` lll `L` t `T` l) (t `TT'T'I` ttt) =>
 (forall e . Contravariant Functor source target (T'II'I source e)) =>
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

kyokl_ = kyokl
kyokl__ = kyokl
kyokl___ = kyokl
kyokl____ = kyokl
_kyokl = kyokl

{-
kyakl, kyakl_, kyakl__, kyakl___, kyakl____, _kyakl :: forall source target t tt ttt l ll lll a o .
 Covariant Yoneda Functor source target t =>
 Component target t (t `T'TT'I` tt `L` tt `T` ll) =>
 Component source (t `T'TT'I` ttt `L` ttt `T` lll `L` t `T` l) (t `TT'T'I` ttt) =>
 (forall e . Contravariant Functor source target (T'II'I source e)) =>
 Hom Functor target =>
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
 target (t a) (target (source (I `L` tt `T` ll `T'I` ttt `L` ttt `T` lll `L` t `T` l `T` o) (tt a)) (ttt (t o)))
kyakl = fio @source (wrapped (component @source @(t `T'TT'I` ttt `L` ttt `T` lll `L` t `T` l) @(t `TT'T'I` ttt)))
 `compose` kya @source @target @t @tt @ll

kyakl_ = kyakl
kyakl__ = kyakl
kyakl___ = kyakl
kyakl____ = kyakl
_kyakl = kyakl
-}

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

-- fai subtype `compose` fio (subtype `compose` subtype)

-- t (tt a) i `AR___` target (source o a) (t ((tttt (tt o))) i)

-- fio (subtype `compose` subtype) `compose` fai subtype `compose`
-- kfokl `compose` fai subtype `compose` fio (subtype `compose` subtype)

-- kfokl: source (ttt `L` ttt `T` lll `T` a) (tt `L` tt `T` ll `L` t `T` l `T` o) -> target (t a) (tt (t o))
-- ha'yok = fai fuk `compose` ha @(AR) @u

yokl, yokl_, yokl__, yokl___, yokl____, yokl_____ ::
 forall source target t tt l ll a o .
 Hom Functor target =>
 Covariant Yoneda Functor source target t =>
 Component target (t `T'TT'I` tt `L` tt `T` ll `L` t `T` l) (t `TT'T'I` tt) =>
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

yokl'ut, yokl_'ut, yokl__'ut, yokl___'ut, yokl____'ut, yokl_____'ut
 :: forall target t tt l ll a o .
 Category target =>
 Terminal target =>
 Covariant Endo Transformation Functor target (t `T'TT'I` tt `L` tt `T` ll `L` t `T` l) (t `TT'T'I` tt) =>
 Covariant Yoneda Functor target target t =>
 Hom Functor target =>
 (forall i . Wrapper target ((t `T'TT'I` tt `L` tt `T` ll `L` t `T` l) i)) =>
 (forall i . Wrapper target ((t `TT'T'I` tt) i)) =>
 (forall i ii . Wrapper target (T'I'II target i (tt `L` tt `T` ll `L` t `T` l `T` ii))) =>
 (forall i ii . Wrapper target (T'I'II target ((tt `L` tt `T` ll) i) ii)) =>
 (forall i ii . Wrapper target (T'II'I target (tt `L` tt `T` ll `L` t `T` l `T` i) ii)) =>
 (forall e ee . Wrapper target (T'I'II target e ee)) =>
 (forall e ee . Wrapper target (T'II'I target e ee)) =>
 (forall e . Wrapper target (target Unit e)) =>
 (Supertype (target Unit (tt `L` tt `T` ll `L` t `T` l `T` o)) ~ (tt `L` tt `T` ll `L` t `T` l `T` o)) =>
 target (t a) (target (tt `L` tt `T` ll `L` t `T` l `T` o) (tt (t o)))
yokl'ut = fio (wrapped @target (component @target @(t `T'TT'I` tt `L` tt `T` ll `L` t `T` l) @(t `TT'T'I` tt))) `compose` yo'ut

yokl_'ut = yokl'ut
yokl__'ut = yokl'ut
yokl___'ut = yokl'ut
yokl____'ut = yokl'ut
yokl_____'ut = yokl'ut

yiokl :: forall source target t tt l ll a o i .
 Category target =>
 Hom Functor target =>
 Covariant Endo Transformation Functor target (T'I'II t i `T'TT'I` tt `L` tt `T` ll `L` T'I'II t i `T` l) (T'I'II t i `TT'T'I` tt) =>
 Covariant Yoneda Functor source target (T'I'II t i) =>
 Covariant Functor source target tt =>
 (forall e . Wrapper target (T'I'II t i `T'TT'I` tt `L` tt `T` ll `L` T'I'II t i `T` l `T'I_` e)) =>
 (forall e . Wrapper target (T'I'II t i `TT'T'I` tt `T'I_` e)) =>
 (forall e . Wrapper source (T'I'II t i e)) =>
 (forall e . Wrapper target (T'I'II t i e)) =>
 (forall e ee . Wrapper target (T'II'I target e ee)) =>
 (forall e ee . Wrapper target (T'I'II target e ee)) =>
 (forall e ee . Wrapper target (T'I'II source e ee)) =>
 target (t i a) (target (source a (tt `L` tt `T` ll `L` T'I'II t i `T` l `T'I` o)) (tt (t i o)))
yiokl = fio (fo @source supertype `compose` wrapped @target (component @target @(T'I'II t i `T'TT'I` tt `L` tt `T` ll `L` T'I'II t i `T` l) @(T'I'II t i `TT'T'I` tt)))
 `compose` yo
 `compose` subtype

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
--  (fio @source (subtype `compose` subtype)
--   `compose` fokl @source @source @tt @ttt @ll @lll
--   `compose` fio @source supertype
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
-- yoikl x = fo @source supertype
--  `compose` supertype @target @(TT'T'I (T'II'I t i) tt _)
--  `compose` component @target @(T'II'I t i `T'TT'I` tt `L` tt `T` ll `L` t `T` l) @(T'II'I t i `TT'T'I` tt)
--  `compose` subtype @target @((T'II'I t i `T'TT'I` tt `L` tt `T` ll `L` t `T` l) _)
--  `compose` yo (subtype x)

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
--  (fio @source (subtype `compose` subtype)
--   `compose` fokl @source @source @tt @ttt @ll @lll
--   `compose` fio @source supertype
--  )
--  (yoikl @source @target @t @ttt @l @lll @(tt a) @(tt o) x)

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
-- yok'yokl x = fai (fio (subtype @source @(tt `L` _ `T` _ `T` _)) `compose` fokl @source @source @ttt @tt @l @ll)
--  (yok @source @target @t @tt @ll x `compose` fio (supertype @target @()))

-- (tt `L` tt `T` ll `L` t `T` lll `T` _)

-- yok_'yokl = yok'yokl
-- yok__'yokl = yok'yokl
-- yok___'yokl = yok'yokl
-- yok____'yokl = yok'yokl
-- yok_____'yokl = yok'yokl
-- yok______'yokl = yok'yokl

-- yok'yokl, yok_'yokl, yok__'yokl, yok___'yokl, yok____'yokl, yok_____'yokl, yok______'yokl
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
-- yok'yokl x = fai
 -- (fio (subtype @(AR) @(ttt `L` tt `T` ll `T` _)) `compose` fukl @(AR) @tt @ttt @ll @lll)
 -- (yok @(AR) @target @t @ttt @lll x)

-- (ttt a) `AR` (tt `L` tt `T` w0 `T` o) (t o)

-- T (T (L (T (L tt tt) ll) t) l) o -> ttt a `AR` tt (ttt o)
-- T (T (L (T (L tt tt) ll) ttt) l) o -> ttt a `AR` (tt (ttt o)))

-- yok_'yokl = yok'yokl
-- yok__'yokl = yok'yokl
-- yok___'yokl = yok'yokl
-- yok____'yokl = yok'yokl
-- yok_____'yokl = yok'yokl
-- yok______'yokl = yok'yokl

-- yok'kyokl = 

-- TODO: , yokl_'yokl, yokl__'yokl, yokl___'yokl, yokl____'yokl, yokl_____'yokl
yokl'yokl :: forall source target t tt ttt l ll lll a o .
 Covariant Yoneda Functor source target t =>
 Covariant Semi Functor source target t =>
 Covariant Endo Semi Functor source tt =>
 Covariant Endo Semi Functor source ttt =>
 Covariant Semi Functor source target ttt =>
 Component target (t `T'TT'I` ttt `L` ttt `T` lll `L` t `T` l) (t `TT'T'I` ttt) =>
 Component source (tt `T'TT'I` ttt `L` ttt `T` lll `L` tt `T` ll) (tt `TT'T'I` ttt) =>
 (forall e . Contravariant Semi Functor (AR) target (T'II'I target e)) =>
 Hom Functor target =>
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
 (fio @source (subtype `compose` subtype)
  `compose` fokl @source @source @tt @ttt @ll @lll
  `compose` fio @source supertype
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
 Hom Functor target =>
 Covariant Yoneda Functor source target (T'I'II u i) =>
 Contravariant Semi Functor source target (T'II'I source o) =>
 Covariant Semi Functor source target (T'I'II source o) =>
 Covariant Elicitable source a =>
 Covariant Elicitable source (Supertype a) =>
 (forall e . Wrapper target (T'I'II u i e)) =>
 (forall e ee . Wrapper target (T'I'II source e ee)) =>
 (forall e ee . Wrapper target (T'II'I source e ee)) =>
 (forall e ee . Wrapper target (T'I'II target e ee)) =>
 (forall e ee . Wrapper target (T'II'I target e ee)) =>
 Wrapper target (T'II'I source o (Supertype a)) =>
 Wrapper target (T'II'I source o (Supertype (Supertype a))) =>
 target (u i a) (target (source (Supertype (Supertype a)) o) (u i o))
ho'st'st = fai @target (fai @source (supertype `compose` supertype)) `compose` yio @source @target @u

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
-- ho'st'st'st = fai (fai @source supertype `compose` fai @source supertype `compose` fai @source supertype) `compose` yio @source @target

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
-- ho'st'st'st'st x = yio @source @target @u x `compose` fai @source supertype `compose` fai @source supertype `compose` fai @source supertype `compose` fai @source supertype

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

-- ho'ho'ho'ut :: forall source u uu uuu o i ee eee a .
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
-- ho'ho'ho'ut = fai (fio @source `compose` fiu @source) `compose` ho @uuu

ho'ho'ut :: forall source t tt o i ii a .
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
 (Supertype (source Unit o) ~ o) =>
 source (t i (tt ii a)) (source (o) (t i (tt ii o)))
ho'ho'ut = fai (fiu @source) `compose` ho @t

ho'ho'ut'st :: forall source t tt o i ii a .
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
 Covariant Elicitable (AR) o =>
 (Supertype (source Unit (Supertype o)) ~ Supertype o) =>
 source (t i (tt ii a)) (source (o) (t i (tt ii (Supertype o))))
ho'ho'ut'st = fai (fiu @source `compose` supertype) `compose` ho @t

ho'yoo'ut, ho_'yoo'ut, ho__'yoo'ut, ho___'yoo'ut, ho____'yoo'ut, ho_____'yoo'ut, ho______'yoo'ut, ho_______'yoo'ut, ho________'yoo'ut
 :: forall u t o e a .
 Covariant Yoneda Functor (AR) (AR) (T'I'II u e) =>
 Contravariant Yoneda Functor (AR) (AR) (T'II'I u e) =>
 Mapping T'I'II T'I'II (AR) (AR) I (T'I'II (AR) a) =>
 Covariant Endo Semi Functor (AR) t =>
 Constant Semi Functor (AR) (AR) t =>
 u e (t a) -> o -> u e (t o)
ho'yoo'ut x = fai @(AR) @(AR) (fu @(AR)) (ho @(AR) x)

ho_'yoo'ut = ho'yoo'ut
ho__'yoo'ut = ho'yoo'ut
ho___'yoo'ut = ho'yoo'ut
ho____'yoo'ut = ho'yoo'ut
ho_____'yoo'ut = ho'yoo'ut
ho______'yoo'ut = ho'yoo'ut
ho_______'yoo'ut = ho'yoo'ut
ho________'yoo'ut = ho'yoo'ut

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

ho'yoi'ut, ho_'yoi'ut, ho__'yoi'ut, ho___'yoi'ut, ho____'yoi'ut, ho_____'yoi'ut, ho______'yoi'ut, ho_______'yoi'ut, ho________'yoi'ut
 :: forall u t o e a .
 Covariant Yoneda Functor (AR) (AR) (T'I'II u e) =>
 Contravariant Yoneda Functor (AR) (AR) (T'II'I u e) =>
 Mapping T'I'II T'I'II (AR) (AR) I (T'I'II (AR) a) =>
 Covariant Endo Semi Functor (AR) (T'II'I t e) =>
 Constant Semi Functor (AR) (AR) (T'II'I t e) =>
 u e (t a e) -> o -> u e (t o e)
ho'yoi'ut x = fai @(AR) @(AR) (fui @(AR)) (ho @(AR) x)

ho_'yoi'ut = ho'yoi'ut
ho__'yoi'ut = ho'yoi'ut
ho___'yoi'ut = ho'yoi'ut
ho____'yoi'ut = ho'yoi'ut
ho_____'yoi'ut = ho'yoi'ut
ho______'yoi'ut = ho'yoi'ut
ho_______'yoi'ut = ho'yoi'ut
ho________'yoi'ut = ho'yoi'ut

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
-- st'ho x = fai @target supertype `compose` yio @source @target @u

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
-- st'ho'st x = fai @source @target supertype
--  `compose` yio @source @target @u x
--  `compose` fai @source @target supertype

-- he_'ho'st = st'ho'st
-- he__'ho'st = st'ho'st
-- he___'ho'st = st'ho'st
-- he____'ho'st = st'ho'st
-- he_____'ho'st = st'ho'st
-- he______'ho'st = st'ho'st
-- he_______'ho'st = st'ho'st
-- he________'ho'st = st'ho'st

-- st'ho'ut
 -- :: forall source target u i a o .
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
-- st'ho'ut = yiu @target @u `compose` st @source

-- st'st'ho
 -- :: forall source target u i a o .
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
-- -- st'st'ho = yio @source @target @u `compose` fai @source supertype'st

-- st'st'st'ho
 -- :: forall source target u i a o .
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
-- st'st'st'ho = yio @source @target @u `compose` fai @source supertype'st'st

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

yai'st, ha'st, ha_'st, ha__'st, ha___'st, ha____'st, ha_____'st, ha______'st, ha_______'st, ha________'st
 :: forall source target t i a o .
 Contravariant Yoneda Functor source target (T'II'I t i) =>
 (forall e . Contravariant Semi Functor source target (T'II'I source e)) =>
 Hom Functor target =>
 (forall e . Covariant Endo Semi Functor target (T'I'II target e)) =>
 (forall e ee . Wrapper target (T'II'I t e ee)) =>
 (forall e ee . Wrapper target (T'II'I source e ee)) =>
 (forall e ee . Wrapper target (T'I'II target e ee)) =>
 (forall e ee . Wrapper target (T'II'I target e ee)) =>
 Wrapper source o =>
 target (t a i) (target (source (Supertype o) a) (t o i))
yai'st = fai (fai @source @target supertype) `compose` yai @source @target @t

ha'st = yai'st
ha_'st = yai'st
ha__'st = yai'st
ha___'st = yai'st
ha____'st = yai'st
ha_____'st = yai'st
ha______'st = yai'st
ha_______'st = yai'st
ha________'st = yai'st

ha'st'st, ha_'st'st, ha__'st'st, ha___'st'st, ha____'st'st, ha_____'st'st, ha______'st'st, ha_______'st'st, ha________'st'st
 :: forall source target t e a o .
 Hom Functor target =>
 Contravariant Yoneda Functor source target (T'II'I t e) =>
 Contravariant Semi Functor source target (T'II'I source a) =>
 Wrapper source o =>
 (forall e ee . Wrapper target (T'II'I source e ee)) =>
 (forall e ee . Wrapper target (T'I'II target e ee)) =>
 (forall e ee . Wrapper target (T'II'I target e ee)) =>
 (forall e ee . Wrapper target (T'II'I t e ee)) =>
 Wrapper source (Supertype o) =>
 target (t a e) (target (source (Supertype (Supertype o)) a) (t o e))
ha'st'st = fai @target (fai @source (supertype `compose` supertype)) `compose` yai @source @target @t

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
-- st'ha = yai @source @target @t `compose` fai @target supertype

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

ha'ho'ho'ut :: forall target t tt ttt o i ii iii a .
 Terminal target =>
 (forall e . Contravariant Semi Functor (AR) target (T'II'I target e)) =>
 Contravariant Endo Yoneda Functor target (T'II'I t i) =>
 Covariant Endo Semi Functor target (T'I'II tt ii) =>
 Covariant Endo Semi Functor target (T'I'II ttt iii) =>
 Hom Functor target =>
 (forall e ee . Wrapper target (T'II'I t e ee)) =>
 (forall e ee . Wrapper target (T'I'II tt e ee)) =>
 (forall e ee . Wrapper target (T'I'II ttt e ee)) =>
 (forall e ee . Wrapper target (T'I'II target e ee)) =>
 (forall e ee . Wrapper target (T'II'I target e ee)) =>
 (forall e . Wrapper (AR) (target Unit e)) =>
 target (t (tt ii (ttt iii o)) i) (target (Supertype (target Unit o)) (t (tt ii (ttt iii a)) i))
ha'ho'ho'ut = fai (fio @target @target @tt `compose` fiu @target @target @ttt) `compose` yai @target @target @t

-- ha'ho'ut, ha_'ho'ut, ha__'ho'ut, ha___'ho'ut, ha____'ho'ut, ha_____'ho'ut, ha______'ho'ut, ha_______'ho'ut, ha________'ho'ut :: forall u uu o e ee a .
 -- Terminal u =>
 -- Covariant Semi Functor u u (T'I'II uu ee) =>
 -- Constant Semi Functor u u (T'I'II uu ee) =>
 -- Contravariant Yoneda Functor u (AR) (T'II'I u e) =>
 -- Wrapper u (T'I'II uu ee a) =>
 -- Wrapper u (T'I'II uu ee o) =>
 -- Elicitable T'II'I u (U_1_I u a o) =>
 -- Elicitable T'II'I (AR) (U_1_I u a o) =>
 -- u (uu ee o) e -> u Unit o -> u (uu ee a) e
-- ha'ho'ut x = fai @(AR) @(AR) fiu (ha @u x)

-- ha'st'ho'ut :: forall source u uu o e ee a .
 -- Covariant Semi Functor u u (T'I'II uu ee) =>
 -- Constant Semi Functor u u (T'I'II uu ee) (T'I'II uu ee) =>
 -- Contravariant Yoneda Functor u (AR) (T'II'I u e) =>
 -- Wrapper u (T'I'II uu ee a) =>
 -- Wrapper u (T'I'II uu ee o) =>
 -- Elicitable T'II'I (AR) (u () o) =>
 -- u (uu ee o) e -> Supertype (u () o) -> u (uu ee a) e
-- ha'st'ho'ut x = fai @(AR) @(AR) fiu (ha'st @u x)

ha'ho'ut, ha_'ho'ut, ha__'ho'ut, ha___'ho'ut, ha____'ho'ut, ha_____'ho'ut, ha______'ho'ut, ha_______'ho'ut, ha________'ho'ut
 :: forall u uu o i ii a .
 Terminal u =>
 Covariant Semi Functor u u (T'I'II uu ii) =>
 Constant Semi Functor u u (T'I'II uu ii) =>
 Contravariant Yoneda Functor u (AR) (T'II'I u i) =>
 (forall e ee . Wrapper u (T'I'II uu e ee)) =>
 (forall e . Wrapper (AR) (u Unit e)) =>
 u (uu ii o) i -> Supertype (u Unit o) -> u (uu ii a) i
ha'ho'ut x = fai @(AR) @(AR) (fiu @u) (ha @u x)

ha_'ho'ut = ha'ho'ut
ha__'ho'ut = ha'ho'ut
ha___'ho'ut = ha'ho'ut
ha____'ho'ut = ha'ho'ut
ha_____'ho'ut = ha'ho'ut
ha______'ho'ut = ha'ho'ut
ha_______'ho'ut = ha'ho'ut
ha________'ho'ut = ha'ho'ut

ha'yioi :: forall source u t o i ii iii a .
 Covariant Yoneda Functor source (AR) (T'I'II u i) =>
 Contravariant Yoneda Functor source (AR) (T'II'I u i) =>
 Covariant Endo Semi Functor source (W_III_I_II t iii ii) =>
 (forall e . Wrapper source (W_III_I_II t iii ii e)) =>
 u (t ii a iii) i -> source o a -> u (t ii o iii) i
ha'yioi x = fai (fioi @source) (ha @source x)

yor, yor_ :: forall source target t object o .
 Category source =>
 Category target =>
 Covariant Mapping T'I'II source target t (T'I'II source object) =>
 (forall e . Wrapper target (T'I'II source object e)) =>
 target (t o) (source object o)
yor = supertype `compose` map @T'I'II @T'I'II @source @target @t @(T'I'II source object) identity

yor_ = yor

yor'st :: forall source target t object o .
 Category source =>
 Category target =>
 Covariant Mapping T'I'II source target t (T'I'II source object) =>
 (forall e . Contravariant Semi Functor source target (T'II'I source e)) =>
 (forall e ee . Wrapper target (T'I'II source e ee)) =>
 (forall e ee . Wrapper target (T'II'I source e ee)) =>
 Wrapper source object =>
 target (t o) (source (Supertype object) o)
yor'st = fai @source subtype `compose` supertype `compose` map @T'I'II @T'I'II @source @target @t @(T'I'II source object) identity

yior :: forall source target t object i o .
 Category source =>
 Precategory target =>
 Covariant Mapping T'I'II source target (T'I'II t i) (T'I'II source object) =>
 (forall e ee . Wrapper target (T'I'II source e ee)) =>
 (forall e ee . Wrapper target (T'I'II t e ee)) =>
 target (t i o) (source object o)
yior = supertype `compose` map @T'I'II @T'I'II @source @target @(T'I'II t _) @(T'I'II source object) identity `compose` subtype @target @(T'I'II t _ _)

hor, hor_, hor__, hor___, hor____, hor_____, hor______, hor_______ :: forall source target t i o .
 Category source =>
 Precategory target =>
 Covariant Mapping T'I'II source target (T'I'II t i) (T'I'II source i) =>
 (forall e ee . Wrapper target (T'I'II source e ee)) =>
 (forall e ee . Wrapper target (T'I'II t e ee)) =>
 target (t i o) (source i o)
hor = yior @source @target @t @i
hor_ = yior @source @target @t @i
hor__ = yior @source @target @t @i
hor___ = yior @source @target @t @i
hor____ = yior @source @target @t @i
hor_____ = yior @source @target @t @i
hor______ = yior @source @target @t @i
hor_______ = yior @source @target @t @i

yior'st :: forall source target t object i o .
 Category source =>
 Covariant Mapping T'I'II source target (T'I'II t i) (T'I'II source (Supertype object)) =>
 (forall e . Contravariant Semi Functor source target (T'II'I source e)) =>
 (forall e ee . Wrapper target (T'I'II source e ee)) =>
 (forall e ee . Wrapper target (T'II'I source e ee)) =>
 (forall e ee . Wrapper target (T'I'II t e ee)) =>
 Wrapper source object =>
 target (t i o) (source object o)
yior'st = fai @source supertype `compose` supertype `compose` map @T'I'II @T'I'II @source @target @(T'I'II t _) @(T'I'II source (Supertype object)) identity `compose` subtype @target @(T'I'II t _ _)

hor'st, hor_'st, hor__'st, hor___'st, hor____'st, hor_____'st, hor______'st, hor_______'st :: forall source target t i o .
 Covariant Yoneda Functor source target (T'I'II t (Supertype i)) =>
 Covariant Transformation Functor source target (T'I'II t (Supertype i)) (T'I'II source (Supertype i)) =>
 (forall e . Contravariant Semi Functor source target (T'II'I source e)) =>
 (forall e ee . Wrapper target (T'I'II source e ee)) =>
 (forall e ee . Wrapper target (T'II'I source e ee)) =>
 (forall e ee . Wrapper target (T'I'II t e ee)) =>
 Wrapper source i =>
 target (t (Supertype i) o) (source i o)
hor'st = yior'st @source @target @t @i
hor_'st = yior'st @source @target @t @i
hor__'st = yior'st @source @target @t @i
hor___'st = yior'st @source @target @t @i
hor____'st = yior'st @source @target @t @i
hor_____'st = yior'st @source @target @t @i
hor______'st = yior'st @source @target @t @i
hor_______'st = yior'st @source @target @t @i

yoir :: forall source target t object i o .
 Covariant Transformation Functor source target (T'II'I t i) (T'I'II source object) =>
 (forall e ee . Wrapper target (T'I'II source e ee)) =>
 (forall e ee . Wrapper target (T'II'I t e ee)) =>
 target (t o i) (source object o)
yoir = supertype `compose` map @T'I'II @T'I'II @source @target @(T'II'I t _) @(T'I'II source object) identity `compose` subtype @target @(T'II'I t _ _)

yoir'st :: forall source target t object i o .
 Covariant Transformation Functor source target (T'II'I t i) (T'I'II source object) =>
 (forall e . Contravariant Semi Functor source target (T'II'I source e)) =>
 (forall e ee . Wrapper target (T'I'II source e ee)) =>
 (forall e ee . Wrapper target (T'II'I source e ee)) =>
 (forall e ee . Wrapper target (T'II'I t e ee)) =>
 Wrapper source object =>
 target (t o i) (source (Supertype object) o)
yoir'st = fai @source subtype `compose` supertype `compose` map @T'I'II @T'I'II @source @target @(T'II'I t _) @(T'I'II source object) identity `compose` subtype @target @(T'II'I t _ _)

yoor :: forall source target t object a o .
 Covariant Transformation Functor source target (T'I'I t) (T'I'II source object) =>
 (forall e . Wrapper target (T'I'II source object e)) =>
 (forall e ee . Wrapper target (T'I'II source e ee)) =>
 (forall e . Wrapper target (T'I'I t e)) =>
 target (t o o) (source object o)
yoor = supertype `compose` map @T'I'II @T'I'II @source @target @(T'I'I t) @(T'I'II source object) identity `compose` subtype @target @(T'I'I t _)

yoor'st :: forall source target t object a o .
 Covariant Transformation Functor source target (T'I'I t) (T'I'II source object) =>
 (forall e . Contravariant Semi Functor source target (T'II'I source e)) =>
 (forall e . Wrapper target (T'I'II source object e)) =>
 (forall e ee . Wrapper target (T'I'II source e ee)) =>
 (forall e ee . Wrapper target (T'II'I source e ee)) =>
 (forall e . Wrapper target (T'I'I t e)) =>
 Wrapper source object =>
 target (t o o) (source (Supertype object) o)
yoor'st = fai @source subtype `compose` supertype `compose` map @T'I'II @T'I'II @source @target @(T'I'I t) @(T'I'II source object) identity `compose` subtype @target @(T'I'I t _)

yar, yar_ :: forall source target t object a .
 Contravariant Transformation Functor source target t (T'II'I source object) =>
 (forall e . Wrapper target (T'II'I source object e)) =>
 target (t a) (source a object)
yar = supertype `compose` map @T'II'I @T'I'II @source @target @t @(T'II'I source object) identity

yar_ = yar

yar'st, yar_'st :: forall source target t object a .
 Contravariant Transformation Functor source target t (T'II'I source object) =>
 (forall e . Covariant Semi Functor source target (T'I'II source e)) =>
 (forall e ee . Wrapper target (T'II'I source e ee)) =>
 Wrapper source a =>
 target (t a) (source (Supertype a) object)
yar'st = fai @source subtype `compose` supertype `compose` map @T'II'I @T'I'II @source @target @t @(T'II'I source object) identity

yar_'st = yar'st @source @target @t @object

yair :: forall source target t object i a .
 Category source =>
 Precategory target =>
 Contravariant Mapping T'I'II source target (T'II'I t i) (T'II'I source object) =>
 (forall e ee . Wrapper target (T'II'I source e ee)) =>
 (forall e ee . Wrapper target (T'II'I t e ee)) =>
 target (t a i) (source a object)
yair = supertype `compose` map @T'II'I @T'I'II @source @target @(T'II'I t _) @(T'II'I source object) identity `compose` subtype @target @(T'II'I t _ _)

har, har_, har__, har___, har____, har_____, har______, har_______ :: forall source target t i a .
 Category source =>
 Precategory target =>
 Contravariant Mapping T'I'II source target (T'II'I t i) (T'II'I source i) =>
 (forall e ee . Wrapper target (T'II'I source e ee)) =>
 (forall e ee . Wrapper target (T'II'I t e ee)) =>
 target (t a i) (source a i)
har = yair @source @target @t @i
har_ = yair @source @target @t @i
har__ = yair @source @target @t @i
har___ = yair @source @target @t @i
har____ = yair @source @target @t @i
har_____ = yair @source @target @t @i
har______ = yair @source @target @t @i
har_______ = yair @source @target @t @i

yair'st :: forall source target t object i a .
 Category source =>
 Contravariant Transformation Functor source target (T'II'I t i) (T'II'I source object) =>
 (forall e . Covariant Semi Functor source target (T'I'II source e)) =>
 (forall e ee . Wrapper target (T'II'I source e ee)) =>
 (forall e ee . Wrapper target (T'II'I t e ee)) =>
 Wrapper source a =>
 target (t (Supertype a) i) (source a object)
yair'st = fai @source supertype `compose` supertype `compose` map @T'II'I @T'I'II @source @target @(T'II'I t _) @(T'II'I source object) identity `compose` subtype @target @(T'II'I t _ _)

har'st, har_'st, har__'st, har___'st, har____'st, har_____'st, har______'st, har_______'st :: forall source target t i a .
 Category source =>
 Contravariant Transformation Functor source target (T'II'I t i) (T'II'I source i) =>
 (forall e . Covariant Semi Functor source target (T'I'II source e)) =>
 (forall e ee . Wrapper target (T'II'I source e ee)) =>
 (forall e ee . Wrapper target (T'II'I t e ee)) =>
 Wrapper source a =>
 target (t (Supertype a) i) (source a i)
har'st = yair'st @source @target @t @i
har_'st = yair'st @source @target @t @i
har__'st = yair'st @source @target @t @i
har___'st = yair'st @source @target @t @i
har____'st = yair'st @source @target @t @i
har_____'st = yair'st @source @target @t @i
har______'st = yair'st @source @target @t @i
har_______'st = yair'st @source @target @t @i

st'yair :: forall source target t object r i a .
 Category source =>
 Precategory target =>
 Contravariant Mapping T'I'II source target (T'II'I t i) (T'II'I source object) =>
 (forall e ee . Wrapper target (T'II'I source e ee)) =>
 (forall e ee . Wrapper target (T'II'I t e ee)) =>
 Covariant Elicitable target r =>
 (Supertype r ~ t a i) =>
 target r (source a object)
st'yair = supertype `compose` map @T'II'I @T'I'II @source @target @(T'II'I t _) @(T'II'I source object) identity `compose` subtype @target @(T'II'I t _ _) `compose` supertype

st'har, st'har_, st'har__, st'har___, st'har____, st'har_____, st'har______, st'har_______ :: forall source target t r i a .
 Category source =>
 Precategory target =>
 Contravariant Mapping T'I'II source target (T'II'I t i) (T'II'I source i) =>
 (forall e ee . Wrapper target (T'II'I source e ee)) =>
 (forall e ee . Wrapper target (T'II'I t e ee)) =>
 Covariant Elicitable target r =>
 (Supertype r ~ t a i) =>
 target r (source a i)
st'har = st'yair @source @target @t @i
st'har_ = st'yair @source @target @t @i
st'har__ = st'yair @source @target @t @i
st'har___ = st'yair @source @target @t @i
st'har____ = st'yair @source @target @t @i
st'har_____ = st'yair @source @target @t @i
st'har______ = st'yair @source @target @t @i
st'har_______ = st'yair @source @target @t @i

bt'yair :: forall source target t object r i a .
 Category source =>
 Precategory target =>
 Contravariant Mapping T'I'II source target (T'II'I t i) (T'II'I source object) =>
 (forall e ee . Wrapper target (T'II'I source e ee)) =>
 (forall e ee . Wrapper target (T'II'I t e ee)) =>
 Covariant Objective target r (t a i) =>
 (Basetype r ~ t a i) =>
 target r (source a object)
bt'yair = supertype `compose` map @T'II'I @T'I'II @source @target @(T'II'I t _) @(T'II'I source object) identity `compose` subtype @target @(T'II'I t _ _) `compose` basetype

bt'har, bt'har_, bt'har__, bt'har___, bt'har____, bt'har_____, bt'har______, bt'har_______ :: forall source target t r i a .
 Category source =>
 Precategory target =>
 Contravariant Mapping T'I'II source target (T'II'I t i) (T'II'I source i) =>
 (forall e ee . Wrapper target (T'II'I source e ee)) =>
 (forall e ee . Wrapper target (T'II'I t e ee)) =>
 Covariant Objective target r (t a i) =>
 (Basetype r ~ t a i) =>
 target r (source a i)
bt'har = bt'yair @source @target @t @i
bt'har_ = bt'yair @source @target @t @i
bt'har__ = bt'yair @source @target @t @i
bt'har___ = bt'yair @source @target @t @i
bt'har____ = bt'yair @source @target @t @i
bt'har_____ = bt'yair @source @target @t @i
bt'har______ = bt'yair @source @target @t @i
bt'har_______ = bt'yair @source @target @t @i

bt'yair'st :: forall source target t object r i a .
 Category source =>
 Precategory target =>
 Contravariant Mapping T'I'II source target (T'II'I source object) (T'II'I source object) =>
 Contravariant Mapping T'I'II source target (T'II'I t i) (T'II'I source object) =>
 (forall e ee . Wrapper target (T'II'I source e ee)) =>
 (forall e ee . Wrapper target (T'II'I t e ee)) =>
 Covariant Objective target r (t (Supertype a) i) =>
 (Basetype r ~ t (Supertype a) i) =>
 Wrapper source a =>
 target r (source a object)
bt'yair'st = fai @source supertype `compose` supertype `compose` map @T'II'I @T'I'II @source @target @(T'II'I t _) @(T'II'I source object) identity `compose` subtype @target @(T'II'I t _ _) `compose` basetype

bt'har'st, bt'har_'st, bt'har__'st, bt'har___'st, bt'har____'st, bt'har_____'st, bt'har______'st, bt'har_______'st :: forall source target t r i a .
 Category source =>
 Precategory target =>
 Contravariant Mapping T'I'II source target (T'II'I source i) (T'II'I source i) =>
 Contravariant Mapping T'I'II source target (T'II'I t i) (T'II'I source i) =>
 (forall e ee . Wrapper target (T'II'I source e ee)) =>
 (forall e ee . Wrapper target (T'II'I t e ee)) =>
 Covariant Objective target r (t (Supertype a) i) =>
 (Basetype r ~ t (Supertype a) i) =>
 Wrapper source a =>
 target r (source a i)
bt'har'st = bt'yair'st @source @target @t @i
bt'har_'st = bt'yair'st @source @target @t @i
bt'har__'st = bt'yair'st @source @target @t @i
bt'har___'st = bt'yair'st @source @target @t @i
bt'har____'st = bt'yair'st @source @target @t @i
bt'har_____'st = bt'yair'st @source @target @t @i
bt'har______'st = bt'yair'st @source @target @t @i
bt'har_______'st = bt'yair'st @source @target @t @i

yiar :: forall source target t object i a .
 Category source =>
 Precategory target =>
 Contravariant Mapping T'I'II source target (T'I'II t i) (T'II'I source object) =>
 (forall e ee . Wrapper target (T'II'I source e ee)) =>
 (forall e ee . Wrapper target (T'I'II t e ee)) =>
 target (t i a) (source a object)
yiar = supertype `compose` map @T'II'I @T'I'II @source @target @(T'I'II t _) @(T'II'I source object) identity `compose` subtype @target @(T'I'II t _ _)

yiar'st :: forall source target t object i a .
 Category source =>
 Contravariant Mapping T'I'II source target (T'II'I source object) (T'II'I source object) =>
 Contravariant Mapping T'I'II source target (T'I'II t i) (T'II'I source object) =>
 (forall e . Covariant Semi Functor source target (T'I'II source e)) =>
 (forall e ee . Wrapper target (T'II'I source e ee)) =>
 (forall e ee . Wrapper target (T'I'II t e ee)) =>
 Wrapper source a =>
 target (t i a) (source (Supertype a) object)
yiar'st = fai @source subtype `compose` supertype `compose` map @T'II'I @T'I'II @source @target @(T'I'II t _) @(T'II'I source object) identity `compose` subtype @target @(T'I'II t _ _)

yaar :: forall source target t object a .
 Category source =>
 Precategory target =>
 Contravariant Mapping T'I'II source target (T'I'I t) (T'II'I source object) =>
 (forall e . Wrapper target (T'II'I source object e)) =>
 (forall e ee . Wrapper target (T'I'II source e ee)) =>
 (forall e . Wrapper target (T'I'I t e)) =>
 target (t a a) (source a object)
yaar = supertype `compose` map @T'II'I @T'I'II @source @target @(T'I'I t) @(T'II'I source object) identity `compose` subtype @target @(T'I'I t _)

yaar'st :: forall source target t object a .
 Category source =>
 Contravariant Mapping T'I'II source target (T'II'I source object) (T'II'I source object) =>
 Contravariant Mapping T'I'II source target (T'I'I t) (T'II'I source object) =>
 (forall e . Covariant Semi Functor source target (T'I'II source e)) =>
 (forall e . Wrapper target (T'I'II source object e)) =>
 (forall e ee . Wrapper target (T'II'I source e ee)) =>
 (forall e . Wrapper target (T'I'I t e)) =>
 Wrapper source a =>
 target (t a a) (source (Supertype a) object)
yaar'st = fai @source subtype `compose` supertype `compose` map @T'II'I @T'I'II @source @target @(T'I'I t) @(T'II'I source object) identity `compose` subtype @target @(T'I'I t _)

ryo, _ryo, __ryo, ___ryo, ____ryo, _____ryo, ______ryo :: forall source target t object a o i .
 Covariant Yoneda Functor source target I =>
 Hom Functor target =>
 Covariant Mapping T'I'II source target (T'I'II source object) t =>
 (forall e ee . Wrapper target (T'I'II source e ee)) =>
 (forall e ee . Wrapper target (T'I'II target e ee)) =>
 (forall e ee . Wrapper target (T'II'I target ee e)) =>
 (forall e . Wrapper target (I e)) =>
 target (source object a) (target (source (t a) o) o)
ryo = yi `compose` map @T'I'II @T'I'II @source @target @(T'I'II source object) @t identity `compose` subtype

_ryo = ryo
__ryo = ryo
___ryo = ryo
____ryo = ryo
_____ryo = ryo
______ryo = ryo

-- st'ryo, st'_ryo :: forall source target t object a o i .
--  Covariant Yoneda Functor source target I =>
--  (forall e . Covariant Endo Semi Functor target (T'I'II target e)) =>
--  Hom Functor target =>
--  Component target (T'I'II source object) t =>
--  (forall e ee . Wrapper target (T'I'II source e ee)) =>
--  (forall e ee . Wrapper target (T'I'II target e ee)) =>
--  (forall e ee . Wrapper target (T'II'I target ee e)) =>
--  (forall e . Wrapper target (I e)) =>
--  target (source object a) (target (source (t a) o) o)
-- st'ryo = yi `compose` component @target @(T'I'II source object) @t `compose` subtype

-- st'_ryo = st'ryo

ryio, _ryio :: forall source target t object a o i .
 Covariant Yoneda Functor source target I =>
 Hom Functor target =>
 Covariant Mapping T'I'II source target (T'I'II source object) (T'I'II t i) =>
 (forall e ee . Wrapper target (T'I'II source e ee)) =>
 (forall e ee . Wrapper target (T'I'II target e ee)) =>
 (forall e ee . Wrapper target (T'II'I target ee e)) =>
 (forall e ee . Wrapper target (T'I'II t e ee)) =>
 (forall e . Wrapper target (I e)) =>
 target (source object a) (target (source (t i a) o) o)
ryio = yi `compose` supertype `compose` map @T'I'II @T'I'II @source @target @(T'I'II source object) @(T'I'II t i) identity `compose` subtype

_ryio = ryio

ryoi, _ryoi :: forall source target t object a o i .
 Covariant Yoneda Functor source target I =>
 Hom Functor target =>
 Covariant Mapping T'I'II source target (T'I'II source object) (T'I'II t i) =>
 (forall e ee . Wrapper target (T'I'II source e ee)) =>
 (forall e ee . Wrapper target (T'I'II target e ee)) =>
 (forall e ee . Wrapper target (T'II'I target ee e)) =>
 (forall e ee . Wrapper target (T'I'II t e ee)) =>
 (forall e . Wrapper target (I e)) =>
 target (source object a) (target (source (t i a) o) o)
ryoi = yi `compose` supertype `compose` map @T'I'II @T'I'II @source @target @(T'I'II source object) @(T'I'II t i) identity `compose` subtype

_ryoi = ryoi

ryoo, _ryoo :: forall source target t object a o i .
 Covariant Yoneda Functor source target I =>
 Hom Functor target =>
 Covariant Mapping T'I'II source target (T'I'II source object) (T'I'I t) =>
 (forall e ee . Wrapper target (T'I'II source e ee)) =>
 (forall e ee . Wrapper target (T'I'II target e ee)) =>
 (forall e ee . Wrapper target (T'II'I target ee e)) =>
 (forall e . Wrapper target (T'I'I t e)) =>
 (forall e . Wrapper target (I e)) =>
 target (source object a) (target (source (t a a) o) o)
ryoo = yi `compose` supertype `compose` map @T'I'II @T'I'II @source @target @(T'I'II source object) @(T'I'I t) identity `compose` subtype

_ryoo = ryoo

rya, _rya :: forall source target t object a o i .
 Covariant Yoneda Functor source target I =>
 Hom Functor target =>
 Contravariant Mapping T'I'II source target (T'II'I source object) t =>
 (forall e ee . Wrapper target (T'II'I source e ee)) =>
 (forall e ee . Wrapper target (T'I'II source e ee)) =>
 (forall e ee . Wrapper target (T'I'II target e ee)) =>
 (forall e ee . Wrapper target (T'II'I target ee e)) =>
 (forall e . Wrapper target (I e)) =>
 target (source a object) (target (source (t a) o) o)
rya = yi `compose` map @T'II'I @T'I'II @source @target @(T'II'I source object) @t identity `compose` subtype

_rya = rya

ryok, ryok_, ryok__, ryok___ :: forall source target t tt l ll object a o i .
 Covariant Yoneda Functor source target t =>
 Hom Functor target =>
 Covariant Mapping T'I'II source target (T'I'II source object) t =>
 Component target (t `T'TT'I` tt `L` tt `T` ll) t =>
 (forall e ee . Wrapper target (T'I'II source e ee)) =>
 (forall e ee . Wrapper target (T'I'II target e ee)) =>
 (forall e ee . Wrapper target (T'II'I target ee e)) =>
 (forall i . Wrapper target (t `T'TT'I` tt `L` tt `T` ll `T'I_` i)) =>
 target (source object a) (target (source a (tt `L` tt `T` ll `T` o)) (t o))
ryok = yok `compose` map @T'I'II @T'I'II @source @target @(T'I'II source object) @t identity `compose` subtype

ryok_ = ryok
ryok__ = ryok
ryok___ = ryok

ryokl, ryokl_, ryokl__, ryokl___ :: forall source target t tt l ll object a o i .
 Covariant Yoneda Functor source target t =>
 Hom Functor target =>
 Covariant Mapping T'I'II source target (T'I'II source object) t =>
 Component target (t `T'TT'I` tt `L` tt `T` ll `L` t `T` l) (t `TT'T'I` tt) =>
 (forall e ee . Wrapper target (T'I'II source e ee)) =>
 (forall e ee . Wrapper target (T'I'II target e ee)) =>
 (forall e ee . Wrapper target (T'II'I target ee e)) =>
 (forall i . Wrapper target (t `T'TT'I` tt `L` tt `T` ll `L` t `T` l `T'I_` i)) =>
 (forall i . Wrapper target ((t `TT'T'I` tt) i)) =>
 target (source object a) (target (source a (tt `L` tt `T` ll `L` t `T` l `T` o)) (tt (t o)))
ryokl = yokl `compose` map @T'I'II @T'I'II @source @target @(T'I'II source object) @t identity `compose` subtype

ryokl_ = ryokl
ryokl__ = ryokl
ryokl___ = ryokl

-- yio'ryo :: forall source target t object a o i .
--  target (t i a) (target (source a o) (t i o))
-- yio'ryo = ho

{-
ho'ryo :: forall source target t r a o i .
 Covariant Yoneda Functor source target I =>
 Hom Functor target =>
 Covariant Mapping T'I'II source target (T'I'II source r) t =>
 (forall e ee . Wrapper target (T'I'II source e ee)) =>
 (forall e ee . Wrapper target (T'I'II target e ee)) =>
 (forall e ee . Wrapper target (T'II'I target ee e)) =>
 (forall e . Wrapper target (I e)) =>
 target (t i (source rr a)) (target (t i (source (t (tt a)) o)) o)
ho'ryo = _
-}

hjd'eq, hjd_'eq, hjd__'eq, hjd___'eq, hjd____'eq, hjd_____'eq, hjd______'eq, hjd_______'eq, hjd________'eq
 :: forall target a .
 (forall e . Adjoint Functor target target (T'II'I (P) e) (T'I'II target e)) =>
 (forall e . Wrapper target ((T'I'II target a `T'TT'I` T'II'I (P) a) e)) =>
 (forall e . Wrapper target (T'II'I (P) a e)) =>
 (forall e . Wrapper target (T'I'II target a e)) =>
 (forall e . Wrapper target (I e)) =>
 Setoid target a =>
 target a (target a (a `P` a `S` a))
hjd'eq = fij @target @target @(P) @target eq

hjd_'eq = hjd'eq @target @a
hjd__'eq = hjd'eq @target @a
hjd___'eq = hjd'eq @target @a
hjd____'eq = hjd'eq @target @a
hjd_____'eq = hjd'eq @target @a
hjd______'eq = hjd'eq @target @a
hjd_______'eq = hjd'eq @target @a
hjd________'eq = hjd'eq @target @a

hop'eq, hop_'eq, hop__'eq, hop___'eq, hop____'eq, hop_____'eq, hop______'eq, hop_______'eq
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
hop'eq x y = eq `compose` hop x y

hop_'eq = hop'eq
hop__'eq = hop'eq
hop___'eq = hop'eq
hop____'eq = hop'eq
hop_____'eq = hop'eq
hop______'eq = hop'eq
hop_______'eq = hop'eq

{-
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
-}

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
--  (Supertype e ~ t a) =>
--  Contravariant Yoneda Functor source target t =>
--  Wrapper target (T'II'I source a o) =>
--  Wrapper (AR) e =>
--  e -> target (source o a) (t o)
-- st'ya = ya @source @target `compose` supertype

-- st'yo :: forall source target t a o e .
--  (Supertype e ~ t a) =>
--  Covariant Yoneda Functor source target t =>
--  (forall e ee . Wrapper target (T'I'II source e ee)) =>
--  Wrapper (AR) e =>
--  e -> target (source a o) (t o)
-- st'yo = yo @source @target `compose` supertype

-- st'yu :: forall target t a o e .
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

hop, hop_, hop__, hop___, hop____, hop_____, hop______
 :: forall target r a o oo .
 Covariant Limit target target =>
 (forall e . Covariant Functor target target (T'I'II Product e)) =>
 (forall e . Covariant Functor target target (T'II'I Product e)) =>
 (forall e ee . Wrapper target (T'I'II Product e ee)) =>
 (forall e ee . Wrapper target (T'II'I Product e ee)) =>
 (forall e . Wrapper target (T'I'I Product e)) =>
 (forall e . Wrapper target (I e)) =>
 target a o -> target a oo -> target a (o `P` oo)
hop l r = foi @target @target l `compose` fio @target @target r
 `compose` wrapped (map @T'II'I @T'II'I @target @target @(T'I'I Product) @I identity)

hop_ = hop
hop__ = hop
hop___ = hop
hop____ = hop
hop_____ = hop
hop______ = hop

hop'tb, hop_'tb, hop__'tb, hop___'tb, hop____'tb, hop_____'tb, hop______'tb
 :: forall target r a o oo .
 Category target =>
 Limit T'I'II target target =>
 Contravariant Objective target r (o `P` oo) =>
 Covariant Endo Semi Functor target (T'I'II Product a) =>
 Covariant Endo Semi Functor target (T'II'I Product oo) =>
 (forall e ee . Wrapper target (T'I'II Product e ee)) =>
 (forall e ee . Wrapper target (T'II'I Product e ee)) =>
 (forall e . Wrapper target (T'I'I Product e)) =>
 (forall e . Wrapper target (I e)) =>
 target a o -> target a oo -> target a r
hop'tb l r = objective @T'II'I @target @_ @(o `P` oo)
 `compose` foi @target @target l `compose` fio @target @target r
 `compose` wrapped (map @T'II'I @T'II'I @target @target @(T'I'I Product) @I identity)

hop_'tb = hop'tb
hop__'tb = hop'tb
hop___'tb = hop'tb
hop____'tb = hop'tb
hop_____'tb = hop'tb
hop______'tb = hop'tb

hop'hjd :: forall target a aa o oo .
 Category target =>
 Limit T'I'II target target =>
 (forall e . Covariant Functor target target (T'I'II Product e)) =>
 (forall e . Covariant Functor target target (T'II'I Product e)) =>
 (forall e ee . Wrapper target (e `P'I'II` ee)) =>
 (forall e ee . Wrapper target (T'II'I (P) e ee)) =>
 (forall e . Wrapper target (T'I'I (P) e)) =>
 (forall e . Wrapper target (I e)) =>
 target a o -> target aa oo -> target (a `P` aa) (o `P` oo)
hop'hjd l r = hop
 (l `compose` (wrapped (left @T'I'II @target identity)))
 (r `compose` (wrapped (right @T'I'II @target identity)))

hop'dcpp, hop_'dcpp, hop__'dcpp, hop___'dcpp, hop____'dcpp, hop_____'dcpp, hop______'dcpp
 :: forall target t tt l a o oo .
 Covariant Limit target target =>
 (forall e . Covariant Endo Semi Functor (AR) (T'I'II target e)) =>
 (forall e . Covariant Functor target target (T'I'II Product e)) =>
 (forall e . Covariant Functor target target (T'II'I Product e)) =>
 (forall e ee . Covariant Endo Transformation Functor target (Covariant Day target (P) (P) t (tt `L` tt `T` l) e ee) t) =>
 (forall e ee . Wrapper target (T'I'II Product e ee)) =>
 (forall e ee . Wrapper target (T'II'I Product e ee)) =>
 (forall e . Wrapper target (T'I'I Product e)) =>
 (forall e ee eee . Wrapper target (Day T'I'II target (P) (P) t (tt `L` tt `T` l) e ee eee)) =>
 (forall e . Wrapper target (I e)) =>
 target a (t o) -> target a ((tt `L` tt `T` l) oo) -> target a (t (Product o oo))
hop'dcpp l r = dcpp `compose` hop @target @(t o `P` (tt `L` tt `T` l) oo) l r

hop_'dcpp = hop'dcpp
hop__'dcpp = hop'dcpp
hop___'dcpp = hop'dcpp
hop____'dcpp = hop'dcpp
hop_____'dcpp = hop'dcpp
hop______'dcpp = hop'dcpp

hop'dcpp'yo'eq, hop_'dcpp'yo'eq, hop__'dcpp'yo'eq, hop___'dcpp'yo'eq, hop____'dcpp'yo'eq, hop_____'dcpp'yo'eq, hop______'dcpp'yo'eq
 :: forall a o t tt ll .
 (forall e ee . Covariant Endo Transformation Functor (AR) (Covariant Day (AR) (P) (P) t (tt `L` tt `T` ll) e ee) t) =>
 (forall e . Covariant Yoneda Functor (AR) (AR) (T'I'II Product e)) =>
 (forall e . Covariant Yoneda Functor (AR) (AR) (T'II'I Product e)) =>
 Setoid (AR) o =>
 Arrow a (t o) -> Arrow a (tt `L` tt `T` ll `T` o) -> Arrow a (t (o `P` o `S` o))
hop'dcpp'yo'eq x xx xxx = dcpp'yo (hop x xx xxx) eq

hop_'dcpp'yo'eq = hop'dcpp'yo'eq
hop__'dcpp'yo'eq = hop'dcpp'yo'eq
hop___'dcpp'yo'eq = hop'dcpp'yo'eq
hop____'dcpp'yo'eq = hop'dcpp'yo'eq
hop_____'dcpp'yo'eq = hop'dcpp'yo'eq
hop______'dcpp'yo'eq = hop'dcpp'yo'eq

hop'dcps, hop_'dcps, hop__'dcps, hop___'dcps, hop____'dcps, hop_____'dcps, hop______'dcps
 :: forall t tt l a o oo .
 (forall e ee . Covariant Endo Transformation Functor (AR) (Covariant Day (AR) (P) (S) t (tt `L` tt `T` l) e ee) t) =>
 Arrow a (t o) -> Arrow a ((tt `L` tt `T` l) oo) -> Arrow a (t (Sum o oo))
hop'dcps l r = dcps `compose` hop @(AR) @(t o `P` (tt `L` tt `T` l) oo) l r

hop_'dcps = hop'dcps
hop__'dcps = hop'dcps
hop___'dcps = hop'dcps
hop____'dcps = hop'dcps
hop_____'dcps = hop'dcps
hop______'dcps = hop'dcps

hop'dcps'has, hop_'dcps'has, hop__'dcps'has, hop___'dcps'has, hop____'dcps'has, hop_____'dcps'has, hop______'dcps'has
 :: forall t tt l a o .
 (forall e ee . Covariant Endo Transformation Functor (AR) (Covariant Day (AR) (P) (S) t (tt `L` tt `T` l) e ee) t) =>
 Arrow a (t o) -> Arrow a ((tt `L` tt `T` l) o) -> Arrow a (t o)
hop'dcps'has l r = (\x -> dcps'yo @Arrow x (identity @(AR) `has` identity)) `compose` hop @(AR) @(_ `P` _) l r

hop_'dcps'has = hop'dcps'has
hop__'dcps'has = hop'dcps'has
hop___'dcps'has = hop'dcps'has
hop____'dcps'has = hop'dcps'has
hop_____'dcps'has = hop'dcps'has
hop______'dcps'has = hop'dcps'has

hjd'dcps'has, hjd_'dcps'has, hjd__'dcps'has, hjd___'dcps'has, hjd____'dcps'has, hjd_____'dcps'has, hjd______'dcps'has, hjd_______'dcps'has
 :: forall t tt l a o .
 Covariant Endo Semi Functor (AR) t =>
 (forall e ee . Adjoint Functor (AR) (AR) (T'II'I (P) e) (T'I'II (AR) ee)) =>
 (forall e ee . Mapping T'I'II T'I'II (AR) (AR) (Covariant Day (AR) (P) (S) t (tt `L` tt `T` l) e ee) t) =>
 (forall e . Covariant Yoneda Functor (AR) (AR) (T'I'II Product e)) =>
 (forall e . Covariant Yoneda Functor (AR) (AR) (T'II'I Product e)) =>
 t o -> (tt `L` tt `T` l) o -> (t o)
hjd'dcps'has l r = dcps'yo @(AR) @t @tt @l (hjd @AR @P @AR l r) (identity @(AR) `has` identity)

hjd_'dcps'has = hjd'dcps'has
hjd__'dcps'has = hjd'dcps'has
hjd___'dcps'has = hjd'dcps'has
hjd____'dcps'has = hjd'dcps'has
hjd_____'dcps'has = hjd'dcps'has
hjd______'dcps'has = hjd'dcps'has
hjd_______'dcps'has = hjd'dcps'has

has, has_, has__, has___, has____, has_____, has______, has_______ :: forall target i a o oo .
 Contravariant Limit target target =>
 (forall e . Covariant Functor target target (T'I'II S e)) =>
 (forall e . Covariant Functor target target (T'II'I S e)) =>
 (forall ee eee . Wrapper target (T'I'II Sum ee eee)) =>
 (forall ee eee . Wrapper target (T'II'I Sum ee eee)) =>
 (forall ee . Wrapper target (T'I'I Sum ee)) =>
 (forall ee . Wrapper target (I ee)) =>
 target o i -> target oo i -> target (o `S` oo) i
has l r = wrapped (map @T'II'I @T'II'I @target @target @I @(T'I'I Sum) identity)
 `compose` foi @target @target l
 `compose` fio @target @target r

has_ = has
has__ = has
has___ = has
has____ = has
has_____ = has
has______ = has
has_______ = has

st'has, st'has_, st'has__, st'has___, st'has____, st'has_____, st'has______, st'has_______ :: forall target i a o oo .
 Contravariant Limit target target =>
 Covariant Elicitable target a =>
 (Supertype a ~ (o `S` oo)) =>
 (forall e . Covariant Functor target target (T'I'II S e)) =>
 (forall e . Covariant Functor target target (T'II'I S e)) =>
 (forall ee eee . Wrapper target (T'I'II Sum ee eee)) =>
 (forall ee eee . Wrapper target (T'II'I Sum ee eee)) =>
 (forall ee . Wrapper target (T'I'I Sum ee)) =>
 (forall ee . Wrapper target (I ee)) =>
 target o i -> target oo i -> target a i
st'has l r = wrapped (map @T'II'I @T'II'I @target @target @I @(T'I'I Sum) identity)
 `compose` foi @target @target l
 `compose` fio @target @target r
 `compose` supertype @target @a

st'has_ = st'has
st'has__ = st'has
st'has___ = st'has
st'has____ = st'has
st'has_____ = st'has
st'has______ = st'has
st'has_______ = st'has

bt'has, bt'has_, bt'has__, bt'has___, bt'has____, bt'has_____, bt'has______, bt'has_______ :: forall target i a o oo .
 Contravariant Limit target target =>
 Covariant Objective target a (o `S` oo) =>
 (forall e . Covariant Functor target target (T'I'II S e)) =>
 (forall e . Covariant Functor target target (T'II'I S e)) =>
 (forall ee eee . Wrapper target (T'I'II Sum ee eee)) =>
 (forall ee eee . Wrapper target (T'II'I Sum ee eee)) =>
 (forall ee . Wrapper target (T'I'I Sum ee)) =>
 (forall ee . Wrapper target (I ee)) =>
 target o i -> target oo i -> target a i
bt'has l r = wrapped (map @T'II'I @T'II'I @target @target @I @(T'I'I Sum) identity)
 `compose` foi @target @target l
 `compose` fio @target @target r
 `compose` objective @T'I'II @target @a @(o `S` oo)

bt'has_ = bt'has
bt'has__ = bt'has
bt'has___ = bt'has
bt'has____ = bt'has
bt'has_____ = bt'has
bt'has______ = bt'has
bt'has_______ = bt'has

hap, hap_, hap__, hap___, hap____, hap_____, hap______, hap_______ :: forall target a aa o oo .
 (forall e . Covariant Functor target target (T'I'II (P) e)) =>
 (forall e . Covariant Functor target target (T'II'I (P) e)) =>
 (forall ee eee . Wrapper target (T'I'II (P) ee eee)) =>
 (forall ee eee . Wrapper target (T'II'I (P) ee eee)) =>
 (forall ee . Wrapper target (T'I'I (P) ee)) =>
 (forall ee . Wrapper target (I ee)) =>
 target a o -> target aa oo -> target (a `P` aa) (o `P` oo)
hap l r = foi @target @target l `compose` fio @target @target r

hap_ = hap
hap__ = hap
hap___ = hap
hap____ = hap
hap_____ = hap
hap______ = hap
hap_______ = hap

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

dcpp :: forall target i ii t tt l .
 Covariant Limit target target =>
 (forall e . Covariant Endo Semi Functor (AR) (T'I'II target e)) =>
 (forall e . Covariant Functor target target (T'I'II Product e)) =>
 (forall e . Covariant Functor target target (T'II'I Product e)) =>
 (forall e ee . Wrapper target (T'I'II Product e ee)) =>
 (forall e ee . Wrapper target (T'II'I Product e ee)) =>
 (forall e . Wrapper target (T'I'I Product e)) =>
 (forall e ee eee . Wrapper target (Day T'I'II target (P) (P) t (tt `L` tt `T` l) e ee eee)) =>
 (forall e . Wrapper target (I e)) =>
 (forall e ee . Mapping T'I'II T'I'II target target (Covariant Day target (P) (P) t (tt `L` tt `T` l) e ee) t) =>
 target (t i `P_` tt `L` tt `T` l `T` ii) (t `T'I` i `P` ii)
dcpp = day' @T'I'II @target @target @l @t @tt @(P) @(P) identity `compose` subtype `compose` (identity `hop` identity `ho'ut` subtype identity)

dcpp'yo, yp_'yo :: forall a aa o t tt l .
 (forall e ee . Mapping T'I'II T'I'II (AR) (AR) (Covariant Day (AR) (P) P t (tt `L` tt `T` l) e ee) t) =>
 t a `P` (tt `L` tt `T` l) aa -> (a `P` aa `AR` o) -> t o
dcpp'yo x f = day @T'I'II @(AR) @l @t @tt @(P) @P identity f x

yp_'yo = dcpp'yo

{-
dcpp'yo'hd :: forall i ii r t tt l .
 (forall e ee .Mapping T'I'II T'I'II (AR) (AR) (Covariant Day (AR) (P) P t (tt `L` tt `T` l) e ee) t) =>
 t i `P` (tt `L` tt `T` l) ii -> (i `AR_` ii `AR` r) -> t r
dcpp'yo'hd x f = day @T'I'II @(AR) @l @t @tt @(P) @P identity (fdi f) x

dcpp'yo'ut :: forall i ii r t tt l .
 (forall e ee .Mapping T'I'II T'I'II (AR) (AR) (Covariant Day (AR) (P) P t (tt `L` tt `T` l) e ee) t) =>
 t i `P` (tt `L` tt `T` l) ii -> r -> t r
dcpp'yo'ut x xx = day @T'I'II @(AR) @l @t @tt @(P) @P identity (constant xx) x
-}
-- TODO: try to generalize
-- yip :: forall u e ee eee t .
 -- Covariant Endo Semi Functor (AR) (T'II'I u (t e eee)) =>
 -- Covariant Endo Semi Functor (AR) (T'I'II u (T'I'II t e ee)) =>
 -- Covariant Monoidal Functor (AR) (AR) u (P) (T'I'II t e) =>
 -- u (t e ee) (t e eee) -> t e (ee `P` eee)
-- yip = supertype @Arrow
 -- `compose` day @T'I'II @(AR) @(T'I'II t e) @u @(P) identity identity
 -- `compose` fio @Arrow subtype `compose` foi @Arrow subtype

-- TODO: try to generalize
-- yip'yo :: forall u e ee eee t r .
 -- Covariant Endo Semi Functor (AR) (T'II'I u (t e eee)) =>
 -- Covariant Endo Semi Functor (AR) (T'I'II u (T'I'II t e ee)) =>
 -- Covariant Monoidal Functor (AR) (AR) u (P) (T'I'II t e) =>
 -- u (t e ee) (t e eee) -> (AR) (ee `P` eee) r -> t e r
-- yip'yo x f = supertype @Arrow
 -- `compose` day @T'I'II @(AR) @(T'I'II t e) @u @(P) identity f
 -- `compose` fio @Arrow subtype `compose` foi @Arrow subtype
 -- `hc`x

-- TODO: try to generalize
yo'dcpp :: forall ttt i ii t tt ll .
 Covariant Endo Semi Functor (AR) t =>
 (forall e ee . Mapping T'I'II T'I'II (AR) (AR) (Covariant Day (AR) ttt (P) tt (tt `L` tt `T` ll) e ee) tt) =>
 t (ttt (tt i) ((tt `L` tt `T` ll) ii)) -> t (tt (i `P` ii))
yo'dcpp = fo (day @T'I'II @(AR) @ll @tt @tt @ttt @(P) identity identity)

-- TODO: try to generalize
yio'dcpp :: forall ttt i ii iii t tt ll .
 (forall e . Covariant Endo Semi Functor (AR) (T'I'II t e)) =>
 (forall e ee . Mapping T'I'II T'I'II (AR) (AR) (Covariant Day (AR) ttt (P) tt (tt `L` tt `T` ll) e ee) tt) =>
 t iii (ttt (tt i) ((tt `L` tt `T` ll) ii)) -> t iii (tt (i `P` ii))
yio'dcpp = fio (day @T'I'II @(AR) @ll @tt @tt @ttt @(P) identity identity)

dcps :: forall target i ii t tt l .
 Covariant Limit target target =>
 (forall e . Covariant Endo Semi Functor (AR) (T'I'II target e)) =>
 (forall e . Covariant Functor target target (T'I'II Product e)) =>
 (forall e . Covariant Functor target target (T'II'I Product e)) =>
 (forall e ee . Wrapper target (T'I'II Product e ee)) =>
 (forall e ee . Wrapper target (T'II'I Product e ee)) =>
 (forall e . Wrapper target (T'I'I Product e)) =>
 (forall e ee eee . Wrapper target (Day T'I'II target (P) (S) t (tt `L` tt `T` l) e ee eee)) =>
 (forall e . Wrapper target (I e)) =>
 (forall e ee . Mapping T'I'II T'I'II target target (Covariant Day target (P) (S) t (tt `L` tt `T` l) e ee) t) =>
 target (t i `P_` tt `L` tt `T` l `T` ii) (t `T'I` i `S` ii)
dcps = day' @T'I'II @target @target @l @t @tt @(P) @(S) identity `compose` subtype `compose` (identity `hop` identity `ho'ut` subtype identity)

-- TODO: try to generalize
dcps'yo :: forall source t tt l i ii u r .
 Category source =>
 (forall e ee . Covariant Transformation Functor source (AR) (Covariant Day source u (S) t (tt `L` tt `T` l) e ee) t) =>
 u (t i) ((tt `L` tt `T` l) ii) -> source (i `S` ii) r -> t r
dcps'yo x f = day @T'I'II @source @l @t @tt @u @(S) identity f x

{-
-- TODO: try to generalize
dcps'yo'ut :: forall t tt l i ii u r .
 (forall e . Mapping T'I'II T'I'II (->) (->) I (T'I'II (AR) e)) =>
 (forall e ee . Covariant Endo Transformation Functor (AR) (Covariant Day (AR) u (S) t (tt `L` tt `T` l) e ee) t) =>
 u (t i) ((tt `L` tt `T` l) ii) -> r -> t r
dcps'yo'ut x r = day @T'I'II @(AR) @l @t @tt @u @(S) identity (constant r) x
-}

-- TODO: try to generalize
-- yis :: forall u e ee eee t .
 -- Covariant Endo Semi Functor (AR) (T'II'I u (t e eee)) =>
 -- Covariant Endo Semi Functor (AR) (T'I'II u (T'I'II t e ee)) =>
 -- Covariant Monoidal Functor (AR) (AR) u (S) (T'I'II t e) =>
 -- u (t e ee) (t e eee) -> t e (ee `S` eee)
-- yis = supertype @Arrow
 -- `compose` day @T'I'II @(AR) @(T'I'II t e) @u @(S) identity identity
 -- `compose` fio @Arrow subtype `compose` foi @Arrow subtype

-- TODO: try to generalize
dcpw :: forall target i ii t tt l .
 Covariant Limit target target =>
 (forall e ee . Mapping T'I'II T'I'II target target (Covariant Day target (P) (W) t (tt `L` tt `T` l) e ee) t) =>
 (forall e . Covariant Endo Semi Functor (AR) (T'I'II target e)) =>
 (forall e . Covariant Functor target target (T'I'II Product e)) =>
 (forall e . Covariant Functor target target (T'II'I Product e)) =>
 (forall e ee eee . Wrapper target (Day T'I'II target (P) (W) t (tt `L` tt `T` l) e ee eee)) =>
 (forall e ee . Wrapper target (T'I'II Product e ee)) =>
 (forall e ee . Wrapper target (T'II'I Product e ee)) =>
 (forall e . Wrapper target (T'I'I Product e)) =>
 (forall e . Wrapper target (I e)) =>
 target (t i `P_` tt `L` tt `T` l `T` ii) (t (i `W` ii))
dcpw = day' @T'I'II @target @target @l @t @tt @(P) @(W) identity `compose` subtype `compose` (identity `hop` identity `ho'ut` subtype identity)

-- TODO: try to generalize
dcpw'yo :: forall source u i ii r t tt ll .
 Category source =>
 (forall e ee . Covariant Transformation Functor source (AR) (Covariant Day source (P) (W) t (tt `L` tt `T` ll) e ee) t) =>
 Wrapper source (i `W` ii) =>
 P (t i) (tt `L` tt `T` ll `T` ii) -> source (i `W` ii) r -> t r
dcpw'yo x f = day @T'I'II @source @ll @t @tt @(P) @(W) identity f x

-- TODO: try to generalize
dcpw'yokl :: forall source i ii r t tt ttt l ll lll .
 Category source =>
 Component (AR) (t `T'TT'I` ttt `L` ttt `T` lll `L` t `T` l) (t `TT'T'I` ttt) =>
 (forall e ee . Covariant Transformation Functor source (AR) (Covariant Day source (P) (W) t (tt `L` tt `T` ll) e ee) t) =>
 Wrapper source (i `W` ii) =>
 P (t i) (tt `L` tt `T` ll `T` ii) -> source (i `W` ii) (ttt `L` ttt `T` lll `L` t `T` l `T` r) -> ttt (t r)
dcpw'yokl x f = wrapped
 (component @(AR) @(t `T'TT'I` ttt `L` ttt `T` lll `L` t `T` l) @(t `TT'T'I` ttt))
 (day @T'I'II @source @ll @t @tt @(P) @(W) identity f x)

-- TODO: try to generalize
dcpp'dcpp :: forall ttttt i ii t tt ttt tttt l ll .
 -- Covariant Monoidal Functor (AR) (AR) u (P) l t =>
 -- Covariant Monoidal Functor (AR) (AR) (P) P ll tt =>
 (forall e ee . Covariant Transformation Functor (AR) (AR) (Covariant Day (AR) ttttt (P) t (ttt `L` ttt `T` l) e ee) t) =>
 (forall e ee . Covariant Transformation Functor (AR) (AR) (Covariant Day (AR) (P) P tt (tttt `L` tttt `T` ll) e ee) tt) =>
 ttttt (t (tt i)) ((ttt `L` ttt `T` l) (tttt `L` tttt `T` ll `T` ii)) -> t (tt (i `P` ii))
dcpp'dcpp = day @T'I'II @(AR) @l @t @ttt @ttttt @(P) identity
 (day @T'I'II @(AR) @ll @tt @tttt @(P) @P identity identity)

-- TODO: generalize
dcpp'dcps :: forall ttt i ii t tt l ll .
 (forall e ee . Covariant Endo Transformation Functor (AR) (Covariant Day (AR) ttt (P) t (t `L` t `T` l) e ee) t) =>
 (forall e ee . Covariant Endo Transformation Functor (AR) (Covariant Day (AR) (P) (S) tt (tt `L` tt `T` ll) e ee) tt) =>
 -- Covariant Lax Monoidal Functor (AR) (AR) ttt (P) l t =>
 -- Covariant Lax Monoidal Functor (AR) (AR) (P) (S) ll tt =>
 ttt (t (tt i)) ((t `L` t `T` l) ((tt `L` tt `T` ll) ii)) -> t (tt (i `S` ii))
dcpp'dcps = day @T'I'II @(AR) @l @t @t @ttt @(P) identity
 (day @T'I'II @(AR) @ll @tt @tt @(P) @(S) identity identity)

-- yip'dcpp :: forall u e ee eee t tt .
 -- Covariant Endo Semi Functor (AR) (T'I'II t e) =>
 -- Covariant Endo Semi Functor (AR) (T'I'II u (T'I'II t e (tt ee))) =>
 -- Covariant Endo Semi Functor (AR) (T'II'I u (t e (tt eee))) =>
 -- Covariant Monoidal Functor (AR) (AR) (P) P tt =>
 -- Covariant Monoidal Functor (AR) (AR) u (P) (T'I'II t e) =>
 -- u (t e (tt ee)) (t e (tt eee)) -> t e (tt (ee `P` eee))
-- yip'dcpp x = yip'yo x yp

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
-- dcpp'yok :: forall i ii source target t tt ttt l ll o .
--  Covariant Transformation Functor (AR) (AR) (Covariant Day (AR) (P) P t (ttt `L` ttt `T` l) i ii) t =>
--  Covariant Endo Semi Functor target tt =>
--  Covariant Endo Semi Functor target t =>
--  Covariant Yoneda Functor source target t =>
--  Covariant Endo Transformation Functor target (t `T'TT'I` tt `L` tt `T` ll) t =>
--  (forall e ee . Wrapper target (T'I'II source e ee)) =>
--  (forall e . Wrapper target ((t `T'TT'I` tt `L` tt `T` ll) e)) =>
--  target (t i `P` (ttt `L` ttt `T` l) ii) (target (source (i `P` ii) ((tt `L` tt `T` ll) o)) (t o))
-- dcpp'yok = yok @source @target `compose` yp

-- -- TODO: try to generalize
-- dcpp'yokl :: forall e ee source target t tt ttt l ll lll o .
--  Covariant Endo Transformation Functor target (t `T'TT'I` tt `L` tt `T` ll `L` t `T` l) (t `TT'T'I` tt) =>
--  Covariant Transformation Functor (AR) (AR) (Covariant Day (AR) (P) P t (ttt `L` ttt `T` lll) e ee) t =>
--  Covariant Yoneda Functor source target t =>
--  Elicitable T'II'I target (T'I'II source (e `P` ee) (tt o)) =>
--  (forall i . Wrapper target (t `T'TT'I` tt `T'I_` i)) =>
--  (forall i . Wrapper target (TT'T'I t tt i)) =>
--  (forall i . Wrapper target ((t `T'TT'I` tt `L` tt `T` ll `L` t `T` l) i)) =>
--  (forall e ee . Wrapper target (T'I'II source e ee)) =>
--  target (t e `P` (ttt `L` ttt `T` lll) ee) (target (source (e `P` ee) (tt `L` tt `T` ll `L` t `T` l `T` o)) (tt (t o)))
-- dcpp'yokl = yokl @source @target `compose` yp

-- TODO: try to generalize
dcpp'dcpp'yo :: forall source i ii r t tt ttt tttt l ll .
 (forall e ee . Covariant Transformation Functor (AR) (AR) (Covariant Day (AR) (P) P t (ttt `L` ttt `T` l) e  ee) t) =>
 (forall e ee . Covariant Transformation Functor source (AR) (Covariant Day source (P) P tt (tttt `L` tttt `T` ll) e ee) tt) =>
 t (tt i) `P` (ttt `L` ttt `T` l) (tttt `L` tttt `T` ll `T` ii) -> source (i `P` ii) r -> t (tt r)
dcpp'dcpp'yo x f = day @T'I'II @(AR) @l @t @ttt @(P) @P identity
 (day @T'I'II @source @ll @tt @tttt @(P) @P identity f) x

-- w'rw :: forall target a o
 -- Elicitable T'II'I target o =>
 -- Elicitable T'I'II target a =>
 -- target (Supertype a) (Supertype o) -> target a o
-- w'rw target = subtype @target `compose` target `compose` st @target

-- rw'w :: forall target a o .
 -- Elicitable T'II'I target a =>
 -- Elicitable T'I'II target o =>
 -- target a o -> target (Supertype a) (Supertype o)
-- rw'w target = _' @target `compose` target `compose` subtype @target

-- yi__, yi___, yi____, yi_____, yi______ :: forall target a .
 -- Elicitable T'I'II target a =>
 -- Elicitable T'I'II target (Supertype a) =>
 -- target a (Supertype (Supertype a))
-- yi__ = _' @target `compose` _' @target

-- yi___ = yi__
-- yi____ = yi__
-- yi_____ = yi__
-- yi______ = yi__

-- yi___, yi____, yi_____, yi______, yi_______ :: forall target a .
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

-- TODO: defined manually temporarily, replace with generated version
yio'yok, ho'yok, ho_'yok, ho__'yok, ho___'yok, ho____'yok, ho_____'yok, ho______'yok, ho_______'yok, ho________'yok :: forall source target t tt ttt lll a o i .
 Covariant Endo Semi Functor source ttt =>
 Covariant Endo Semi Functor source tt =>
 (forall e . Contravariant Semi Functor (AR) target (T'II'I target e)) =>
 Hom Functor target =>
 (forall e . Covariant Endo Semi Functor target (T'I'II target e)) =>
 Component source (tt `T'TT'I` ttt `L` ttt `T` lll) tt =>
 (forall e . Covariant Yoneda Functor source target (T'I'II t e)) =>
 (forall e . Wrapper source ((tt `T'TT'I` ttt `L` ttt `T` lll) e)) =>
 (forall e . Wrapper source ((tt `T'TT'I` ttt) e)) =>
 (forall e . Wrapper source (ttt `L` ttt `T` lll `T` e)) =>
 (forall e ee . Wrapper target (T'I'II target e ee)) =>
 (forall e ee . Wrapper target (T'II'I target e ee)) =>
 (forall e ee . Wrapper target (T'I'II source e ee)) =>
 (forall e ee . Wrapper target (T'I'II t e ee)) =>
 target (t i (tt a)) (target (source a (ttt `L` ttt `T` lll `T` o)) (t i (tt o)))
yio'yok = fai fok `compose` ho @source

ho'yok = yio'yok
ho_'yok = yio'yok
ho__'yok = yio'yok
ho___'yok = yio'yok
ho____'yok = yio'yok
ho_____'yok = yio'yok
ho______'yok = yio'yok
ho_______'yok = yio'yok
ho________'yok = yio'yok

-- TODO: defined manually temporarily, rephasce with generated version
ho'yok'ut, ho_'yok'ut, ho__'yok'ut, ho___'yok'ut, ho____'yok'ut, ho_____'yok'ut, ho______'yok'ut, ho_______'yok'ut, ho________'yok'ut
 :: forall source t tt ll a o i .
 Covariant Endo Semi Functor source tt =>
 Constant Functor (AR) source t =>
 Covariant Endo Transformation Functor source (t `T'TT'I` tt `L` tt `T` ll) t =>
 Covariant Yoneda Functor source (AR) (T'I'II source i) =>
 (forall e . Wrapper source (t `T'TT'I` tt `L` tt `T` ll `T'I_` e)) =>
 (forall e . Wrapper source (I `T'I` tt `L` tt `T` ll `T` e)) =>
 source i (t a) -> (tt `L` tt `T` ll) o -> source i (t o)
ho'yok'ut x = fai (fuk @source @t @tt) (ho @source x)
ho_'yok'ut x = fai (fuk @source @t @tt) (ho @source x)
ho__'yok'ut x = fai (fuk @source @t @tt) (ho @source x)
ho___'yok'ut x = fai (fuk @source @t @tt) (ho @source x)
ho____'yok'ut x = fai (fuk @source @t @tt) (ho @source x)
ho_____'yok'ut x = fai (fuk @source @t @tt) (ho @source x)
ho______'yok'ut x = fai (fuk @source @t @tt) (ho @source x)
ho_______'yok'ut x = fai (fuk @source @t @tt) (ho @source x)
ho________'yok'ut x = fai (fuk @source @t @tt) (ho @source x)

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
-- ha'yok, ha_'yok, ha__'yok, ha___'yok, ha____'yok, ha_____'yok, ha______'yok, ha_______'yok, ha________'yok
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
-- ha'yok = fai fuk `compose` ha @(AR) @target @t

-- ha_'yok = ha'yok
-- ha__'yok = ha'yok
-- ha___'yok = ha'yok
-- ha____'yok = ha'yok
-- ha_____'yok = ha'yok
-- ha______'yok = ha'yok
-- ha_______'yok = ha'yok
-- ha________'yok = ha'yok

-- TODO: defined manually temporarily, rephasce with generated version
ha'yokl, ha_'yokl, ha__'yokl, ha___'yokl, ha____'yokl, ha_____'yokl, ha______'yokl, ha_______'yokl, ha________'yokl
 :: forall source target t tt ttt l ll a o i .
 Contravariant Yoneda Functor source target (T'II'I t i) =>
 Covariant Endo Semi Functor source tt =>
 Covariant Endo Semi Functor source ttt =>
 Component source (tt `T'TT'I` ttt `L` ttt `T` ll `L` tt `T` l) (tt `TT'T'I` ttt) =>
 Hom Functor target =>
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
-- yai'yokl, ha'yokl, ha_'yokl, ha__'yokl, ha___'yokl, ha____'yokl, ha_____'yokl, ha______'yokl, ha_______'yokl, ha________'yokl
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
-- yai'yokl = fai fukl `compose` ha @(AR) @target @t

-- ha'yokl = yai'yokl
-- ha_'yokl = yai'yokl
-- ha__'yokl = yai'yokl
-- ha___'yokl = yai'yokl
-- ha____'yokl = yai'yokl
-- ha_____'yokl = yai'yokl
-- ha______'yokl = yai'yokl
-- ha_______'yokl = yai'yokl
-- ha________'yokl = yai'yokl

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

-- yok'ho'ut :: forall source t tt a o e .
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
-- yok'ho'ut x f = yok @_ @_ @tt x `compose` fiu @source f

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

yio'yokl, ho'yokl, ho_'yokl, ho__'yokl, ho___'yokl, ho____'yokl, ho_____'yokl, ho______'yokl, ho_______'yokl, ho________'yokl
 :: forall source target t tt ttt l ll a o e .
 (forall e . Contravariant Semi Functor (AR) target (T'II'I target e)) =>
 Hom Functor target =>
 Covariant Endo Semi Functor source tt =>
 Covariant Endo Semi Functor source ttt =>
 Component source (ttt `T'TT'I` tt `L` tt `T` ll `L` ttt `T` l) (ttt `TT'T'I` tt) =>
 Covariant Yoneda Functor source target (T'I'II t e) =>
 (forall ee . Wrapper source ((ttt `T'TT'I` tt `L` tt `T` ll `L` ttt `T` l) ee)) =>
 (forall ee . Wrapper source ((ttt `T'TT'I` tt) ee)) =>
 (forall ee . Wrapper source ((ttt `TT'T'I` tt) ee)) =>
 (forall ee . Wrapper source (tt `L` tt `T` ll `L` ttt `T` l `T` ee)) =>
 (forall ee . Wrapper source (tt `L` tt `T` ll `T` ee)) =>
 (forall e ee . Wrapper target (T'I'II target e ee)) =>
 (forall e ee . Wrapper target (T'II'I target e ee)) =>
 (forall e ee . Wrapper target (T'I'II source e ee)) =>
 (forall e ee . Wrapper target (T'I'II t e ee)) =>
 target (t e (ttt a)) (target (source a (tt `L` tt `T` ll `L` ttt `T` l `T` o)) (t e (tt (ttt o))))
yio'yokl = fai fokl `compose` ho @source

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
--   `compose` fio @source (subtype @source @(ttt `L` ttt `T` lll `L` t `T` ll `T` _) `compose` subtype @source @(_ `L` _ `T` _ `T` _))
--   `compose` fokl @source @source @tt @ttt @ll @lll
--   `compose` fio @source (supertype @source @(_ `L` _ `T` _ `T` _)))
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
-- yio'yokl'yokl x = fai @(AR)
--  (fokl @(AR) @(AR) @t @ttt @ll @lll
--   `compose` fio @(AR) (subtype @(AR) @(_ `L` _ `T` ll `T` _) `compose` subtype @(AR) @(_ `L` _ `T` _ `T` _))
--   `compose` fukl @(AR) @tt @ttt @ll @lll
--   `compose` supertype @(AR) @(_ `L` _ `T` _ `T` _))
--  (yio @(AR) x)

-- ho'yokl'yokl = yio'yokl'yokl
-- ho_'yokl'yokl = yio'yokl'yokl
-- ho__'yokl'yokl = yio'yokl'yokl
-- ho___'yokl'yokl = yio'yokl'yokl
-- ho____'yokl'yokl = yio'yokl'yokl
-- ho_____'yokl'yokl = yio'yokl'yokl
-- ho______'yokl'yokl = yio'yokl'yokl
-- ho_______'yokl'yokl = yio'yokl'yokl
-- ho________'yokl'yokl = yio'yokl'yokl

yio'yokl'ut, ho'yokl'ut, ho_'yokl'ut, ho__'yokl'ut, ho___'yokl'ut, ho____'yokl'ut, ho_____'yokl'ut, ho______'yokl'ut, ho_______'yokl'ut, ho________'yokl'ut
 :: forall u t tt l ll a o e .
 Covariant Semi Functor (AR) (AR) (T'I'II u e) =>
 Covariant Endo Semi Functor (AR) tt =>
 Constant Endo Semi Functor (AR) t =>
 Component (AR) (t `T'TT'I` tt `L` tt `T` ll `L` t `T` l) (t `TT'T'I` tt) =>
 Covariant Endo Transformation Functor (AR) I (T'I'II (AR) a) =>
 Covariant Endo Yoneda Functor (AR) (T'I'II u e) =>
 (forall ee . Wrapper (AR) (t `T'TT'I` tt `L` tt `T` ll `L` t `T` l `T'I_` ee)) =>
 (forall ee . Wrapper (AR) ((t `T'TT'I` tt) ee)) =>
 (forall ee . Wrapper (AR) ((t `TT'T'I` tt) ee)) =>
 (forall ee . Wrapper (AR) (tt `L` tt `T` ll `L` t `T` l `T` ee)) =>
 (forall ee . Wrapper (AR) (tt `L` tt `T` ll `T` ee)) =>
 u e (t a) -> tt `L` tt `T` ll `L` t `T` l `T` o -> u e (tt (t o))
yio'yokl'ut x = fai fukl (ho @(AR) x)

ho'yokl'ut = yio'yokl'ut
ho_'yokl'ut = yio'yokl'ut
ho__'yokl'ut = yio'yokl'ut
ho___'yokl'ut = yio'yokl'ut
ho____'yokl'ut = yio'yokl'ut
ho_____'yokl'ut = yio'yokl'ut
ho______'yokl'ut = yio'yokl'ut
ho_______'yokl'ut = yio'yokl'ut
ho________'yokl'ut = yio'yokl'ut

yio'yoikl, ho'yoikl, ho_'yoikl, ho__'yoikl, ho___'yoikl, ho____'yoikl, ho_____'yoikl, ho______'yoikl, ho_______'yoikl, ho________'yoikl
 :: forall source t tt ttt l ll a o i ii .
 Covariant Semi Functor source (AR) (T'I'II t i) =>
 Covariant Endo Semi Functor source ttt =>
 Covariant Endo Semi Functor source (T'II'I tt ii) =>
 -- Covariant Endo Semi Functor source (T'II'I tt ii `T'TT'I` ttt `L` ttt `T` ll `L` T'II'I tt ii `T` l) =>
 Component source (T'II'I tt ii `T'TT'I` ttt `L` ttt `T` ll `L` T'II'I tt ii `T` l) (T'II'I tt ii `TT'T'I` ttt) =>
 Covariant Yoneda Functor source (AR) (T'I'II t i) =>
 (forall e . Wrapper source ((T'II'I tt ii `T'TT'I` ttt `L` ttt `T` ll `L` T'II'I tt ii `T` l) e)) =>
 (forall e . Wrapper source ((T'II'I tt ii `T'TT'I` ttt) e)) =>
 (forall e . Wrapper source ((T'II'I tt ii `TT'T'I` ttt) e)) =>
 (forall e . Wrapper source (ttt `L` ttt `T` ll `L` T'II'I tt ii `T` l `T` e)) =>
 (forall e . Wrapper source (ttt `L` ttt `T` ll `T` e)) =>
 (forall e . Wrapper source (T'II'I tt ii e)) =>
 t i (tt a ii) -> source a (ttt `L` ttt `T` ll `L` T'II'I tt ii `T` l `T` o) -> t i (ttt (tt o ii))
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

-- ha'yok :: forall source t tt a o e .
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
-- ha'yok = ha `compose` fuk @source @tt @t

hjd'dcpp, hjd_'dcpp, hjd__'dcpp, hjd___'dcpp, hjd____'dcpp, hjd_____'dcpp, hjd______'dcpp
 :: forall i ii t tt l .
 (forall e . Adjoint Functor (AR) (AR) (T'II'I (P) e) (T'I'II (AR) e)) =>
 (forall e ee . Mapping T'I'II T'I'II (AR) (AR) (Covariant Day (AR) (P) (P) t (tt `L` tt `T` l) e ee) t) =>
 (forall e . Covariant Yoneda Functor (AR) (AR) (T'I'II Product e)) =>
 (forall e . Covariant Yoneda Functor (AR) (AR) (T'II'I Product e)) =>
 t i -> (tt `L` tt `T` l) ii -> t (i `P` ii)
hjd'dcpp source_left r = dcpp @(AR) @i @ii @t @tt @l (hjd @AR @P @AR source_left r)

hjd_'dcpp = hjd'dcpp
hjd__'dcpp = hjd'dcpp
hjd___'dcpp = hjd'dcpp
hjd____'dcpp = hjd'dcpp
hjd_____'dcpp = hjd'dcpp
hjd______'dcpp= hjd'dcpp

hjd'dcpp'yo'eq, hjd_'dcpp'yo'eq, hjd__'dcpp'yo'eq, hjd___'dcpp'yo'eq, hjd____'dcpp'yo'eq, hjd_____'dcpp'yo'eq, hjd______'dcpp'yo'eq, hjd_______'dcpp'yo'eq
 :: forall i t tt l .
 (forall e . Adjoint Functor (AR) (AR) (T'II'I (P) e) (T'I'II (AR) e)) =>
 (forall e ee . Mapping T'I'II T'I'II (AR) (AR) (Covariant Day (AR) (P) P t (tt `L` tt `T` l) e ee) t) =>
 (forall e . Covariant Yoneda Functor (AR) (AR) (T'I'II Product e)) =>
 (forall e . Covariant Yoneda Functor (AR) (AR) (T'II'I Product e)) =>
 Setoid (AR) i =>
 t i -> (tt `L` tt `T` l) i -> t (i `P` i `S` i)
hjd'dcpp'yo'eq source_left r = dcpp'yo @i @i @_ @t @tt @l (hjd @AR @P source_left r) eq

hjd_'dcpp'yo'eq = hjd'dcpp'yo'eq
hjd__'dcpp'yo'eq = hjd'dcpp'yo'eq
hjd___'dcpp'yo'eq = hjd'dcpp'yo'eq
hjd____'dcpp'yo'eq = hjd'dcpp'yo'eq
hjd_____'dcpp'yo'eq = hjd'dcpp'yo'eq
hjd______'dcpp'yo'eq = hjd'dcpp'yo'eq
hjd_______'dcpp'yo'eq = hjd'dcpp'yo'eq

hjd'dcps, hjd_'dcps, hjd__'dcps, hjd___'dcps, hjd____'dcps, hjd_____'dcps, hjd______'dcps, hjd_______'dcps
 :: forall i ii t tt l .
 (forall e ee . Mapping T'I'II T'I'II (AR) (AR) (Covariant Day (AR) (P) (S) t (tt `L` tt `T` l) e ee) t) =>
 (forall e . Adjoint Functor (AR) (AR) (T'II'I (P) e) (T'I'II (AR) e)) =>
 Covariant Yoneda Functor (AR) (AR) (P'I'II (t i)) =>
 Covariant Yoneda Functor (AR) (AR) (T'II'I (P) ()) =>
 t i -> (tt `L` tt `T` l) ii -> t (i `S` ii)
hjd'dcps l r = dcps @(AR) @i @ii @t @tt @l (hjd @AR @P @AR @_ l r)

hjd_'dcps = hjd'dcps
hjd__'dcps = hjd'dcps
hjd___'dcps = hjd'dcps
hjd____'dcps = hjd'dcps
hjd_____'dcps = hjd'dcps
hjd______'dcps = hjd'dcps
hjd_______'dcps = hjd'dcps

{-
hjd'dcpp'dcpp :: forall o oo t tt l ll .
 Covariant Endo Semi Functor (AR) tt =>
 Covariant Transformation Functor (AR) (AR) (Covariant Day (AR) (P) P t (t `L` t `T` l) (tt o) (tt `L` tt `T` ll `T` oo)) t =>
 Covariant Transformation Functor (AR) (AR) (Covariant Day (AR) (P) P tt (tt `L` tt `T` ll) o oo) tt =>
 Adjoint Functor (AR) (AR) (T'II'I P (t `L` t `T` l `T` (tt `L` tt `T` ll `T` oo))) (T'I'II (AR) (t `L` t `T` l `T` (tt `L` tt `T` ll `T` oo))) =>
 Covariant Yoneda Functor (AR) (AR) (T'I'II Product (t (tt o))) =>
 Covariant Yoneda Functor (AR) (AR) (T'II'I Product Unit) =>
 t (tt o) -> (t `L` t `T` l) ((tt `L` tt `T` ll) oo) -> t (tt (o `P` oo))
hjd'dcpp'dcpp l r = dcpp'dcpp @(P) (hjd @AR @P @AR l r)
-}

hjd'dcpp'dcps
 :: forall t tt l ll i ii .
 Covariant Endo Semi Functor (AR) t =>
 (forall e ee . Adjoint Functor (AR) (AR) (T'II'I (P) e) (T'I'II (AR) ee)) =>
 (forall e ee . Covariant Endo Transformation Functor (AR) (Covariant Day (AR) (P) (P) t (t `L` t `T` l) e ee) t) =>
 (forall e ee . Covariant Endo Transformation Functor (AR) (Covariant Day (AR) (P) (S) tt (tt `L` tt `T` ll) e ee) tt) =>
 (forall e . Covariant Yoneda Functor (AR) (AR) (T'II'I Product e)) =>
 (forall e . Covariant Yoneda Functor (AR) (AR) (T'I'II Product e)) =>
 t (tt i) -> (t `L` t `T` l) ((tt `L` tt `T` ll) ii) -> t (tt (i `S` ii))
hjd'dcpp'dcps l r = dcpp'dcps @(P) @i @ii @t @tt @l @ll (hjd @AR @P @AR l r)

-- hjd'yip'dcpp
 -- :: forall t tt o oo e .
 -- Covariant Lax Monoidal Functor (AR) (AR) (P) P tt =>
 -- Covariant Monoidal Functor (AR) (AR) (P) P (T'I'II t e) =>
 -- Covariant Endo Semi Functor (AR) (T'I'II t e) =>
 -- Covariant Yoneda Functor (AR) (AR) (T'II'I Product ()) =>
 -- Covariant Yoneda Functor (AR) (AR) (T'I'II Product (t e (tt o))) =>
 -- t e (tt o) -> t e (tt oo) -> t e (tt (o `P` oo))
-- hjd'yip'dcpp l r = yip'dcpp (hjd l r)

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

hjd'dcpw, hjd_'dcpw, hjd__'dcpw, hjd___'dcpw, hjd____'dcpw, hjd_____'dcpw, hjd______'dcpw, hjd_______'dcpw
 :: forall o oo t tt l .
 (forall e . Adjoint Functor (AR) (AR) (T'II'I (P) e) (T'I'II (AR) e)) =>
 (forall e ee . Mapping T'I'II T'I'II (AR) (AR) (Covariant Day (AR) (P) (W) t (tt `L` tt `T` l) e ee) t) =>
 Covariant Yoneda Functor (AR) (AR) (T'II'I Product ()) =>
 Covariant Yoneda Functor (AR) (AR) (T'I'II Product (t o)) =>
 t o -> (tt `L` tt `T` l) oo -> t (o `W` oo)
hjd'dcpw l r = dcpw @(AR) @o @oo @t @tt @l (hjd @AR @P @AR l r)

hjd_'dcpw = hjd'dcpw
hjd__'dcpw = hjd'dcpw
hjd___'dcpw = hjd'dcpw
hjd____'dcpw = hjd'dcpw
hjd_____'dcpw = hjd'dcpw
hjd______'dcpw = hjd'dcpw
hjd_______'dcpw = hjd'dcpw

ydj :: forall target t tt i .
 Adjoint Functor target target t tt =>
 (forall e . Wrapper target (t `T'TT'I` tt `T'I_` e)) =>
 (forall eee . Wrapper target (I eee)) =>
 target (t (tt i)) i
ydj = supertype `compose` component @target @(t `T'TT'I` tt) @I `compose` subtype

yjd :: forall target t tt i .
 Adjoint Functor target target t tt =>
 (forall e . Wrapper target (tt `T'TT'I` t `T'I_` e)) =>
 (forall eee . Wrapper target (I eee)) =>
 target i (tt (t i))
yjd = supertype `compose` component @target @I @(tt `T'TT'I` t) `compose` subtype

hjd, hjd_, hjd__, hjd___, hjd____ :: forall target t tt i ii .
 (forall e . Adjoint Functor target target (T'II'I t e) (T'I'II tt e)) =>
 (forall e ee eee . Wrapper target (T'I'II tt e `T'TT'I` T'II'I t e `T'I_` eee)) =>
 (forall eee . Wrapper target (I eee)) =>
 (forall e eee . Wrapper target (T'II'I t e eee)) =>
 (forall ee eee . Wrapper target (T'I'II tt ee eee)) =>
 target i (tt ii (t i ii))
hjd = fio @target supertype `compose` supertype `compose` supertype `compose` component @target @I @(T'I'II tt ii `T'TT'I` T'II'I t ii) `compose` subtype

hjd_ = fio @target supertype `compose` supertype `compose` supertype `compose` component @target @I @(T'I'II tt ii `T'TT'I` T'II'I t ii) `compose` subtype
hjd__ = fio @target supertype `compose` supertype `compose` supertype `compose` component @target @I @(T'I'II tt ii `T'TT'I` T'II'I t ii) `compose` subtype
hjd___ = fio @target supertype `compose` supertype `compose` supertype `compose` component @target @I @(T'I'II tt ii `T'TT'I` T'II'I t ii) `compose` subtype
hjd____ = fio @target supertype `compose` supertype `compose` supertype `compose` component @target @I @(T'I'II tt ii `T'TT'I` T'II'I t ii) `compose` subtype

hjd'tb, hjd_'tb, hjd__'tb, hjd___'tb, hjd____'tb :: forall target tt i iii ii .
 (forall e . Adjoint Functor target target (T'II'I (P) e) (T'I'II tt e)) =>
 (forall e ee eee . Wrapper target (T'I'II tt ee `T'TT'I` T'II'I (P) e `T'I_` eee)) =>
 (forall e . Wrapper target (I e)) =>
 (forall e ee . Wrapper target (T'II'I (P) e ee)) =>
 (forall e ee . Wrapper target (T'I'II tt ee e)) =>
 Contravariant Objective target iii ((P) i ii) =>
 target i (tt ii iii)
hjd'tb = fio @target (objective @T'II'I @target @iii @((P) i ii) `compose` supertype) `compose` supertype `compose` supertype `compose` component @target @I @(T'I'II tt ii `T'TT'I` T'II'I (P) ii) `compose` subtype

hjd_'tb = fio @target (objective @T'II'I @target @iii @((P) i ii) `compose` supertype) `compose` supertype `compose` supertype `compose` component @target @I @(T'I'II tt ii `T'TT'I` T'II'I (P) ii) `compose` subtype
hjd__'tb = fio @target (objective @T'II'I @target @iii @((P) i ii) `compose` supertype) `compose` supertype `compose` supertype `compose` component @target @I @(T'I'II tt ii `T'TT'I` T'II'I (P) ii) `compose` subtype
hjd___'tb = fio @target (objective @T'II'I @target @iii @((P) i ii) `compose` supertype) `compose` supertype `compose` supertype `compose` component @target @I @(T'I'II tt ii `T'TT'I` T'II'I (P) ii) `compose` subtype
hjd____'tb = fio @target (objective @T'II'I @target @iii @((P) i ii) `compose` supertype) `compose` supertype `compose` supertype `compose` component @target @I @(T'I'II tt ii `T'TT'I` T'II'I (P) ii) `compose` subtype

st'hjd, st'hjd_, st'hjd__, st'hjd___, st'hjd____
 :: forall target t tt i ii iii .
 (forall e . Adjoint Functor target target (T'II'I t e) (T'I'II tt e)) =>
 (forall e ee eee . Wrapper target (T'I'II tt ee `T'TT'I` T'II'I t e `T'I_` eee)) =>
 (forall e . Wrapper target (I e)) =>
 Wrapper target i =>
 (forall e ee . Wrapper target (T'II'I t e ee)) =>
 (forall e ee . Wrapper target (T'I'II tt e ee)) =>
 target i (tt ii (t (Supertype i) ii))
st'hjd = fio @target (supertype) `compose` supertype `compose` supertype `compose` component @target @I @(T'I'II tt ii `T'TT'I` T'II'I t ii) `compose` subtype @_ @(I (Supertype i)) `compose` supertype

st'hjd_ = fio @target (supertype) `compose` supertype `compose` supertype `compose` component @target @I @(T'I'II tt ii `T'TT'I` T'II'I t ii) `compose` subtype @_ @(I (Supertype i)) `compose` supertype
st'hjd__ = fio @target (supertype) `compose` supertype `compose` supertype `compose` component @target @I @(T'I'II tt ii `T'TT'I` T'II'I t ii) `compose` subtype @_ @(I (Supertype i)) `compose` supertype
st'hjd___ = fio @target (supertype) `compose` supertype `compose` supertype `compose` component @target @I @(T'I'II tt ii `T'TT'I` T'II'I t ii) `compose` subtype @_ @(I (Supertype i)) `compose` supertype
st'hjd____ = fio @target (supertype) `compose` supertype `compose` supertype `compose` component @target @I @(T'I'II tt ii `T'TT'I` T'II'I t ii) `compose` subtype @_ @(I (Supertype i)) `compose` supertype

st'hjd'tb, st'hjd_'tb, st'hjd__'tb, st'hjd___'tb, st'hjd____'tb
 :: forall target tt i iii ii .
 (forall e . Adjoint Functor target target (T'II'I (P) e) (T'I'II tt e)) =>
 (forall e ee eee . Wrapper target (T'I'II tt ee `T'TT'I` T'II'I (P) e `T'I_` eee)) =>
 (forall e . Wrapper target (I e)) =>
 (forall e ee . Wrapper target (T'II'I (P) e ee)) =>
 (forall e ee . Wrapper target (T'I'II tt ee e)) =>
 Contravariant Objective target iii ((P) (Supertype i) ii) =>
 Wrapper target i =>
 target i (tt ii iii)
st'hjd'tb = fio @target (objective @T'II'I @target @iii @((P) (Supertype i) ii) `compose` supertype) `compose` supertype `compose` supertype `compose` component @target @I @(T'I'II tt ii `T'TT'I` T'II'I (P) ii) `compose` subtype @_ @(I (Supertype i)) `compose` supertype

st'hjd_'tb = fio @target (objective @T'II'I @target @iii @((P) (Supertype i) ii) `compose` supertype) `compose` supertype `compose` supertype `compose` component @target @I @(T'I'II tt ii `T'TT'I` T'II'I (P) ii) `compose` subtype @_ @(I (Supertype i)) `compose` supertype
st'hjd__'tb = fio @target (objective @T'II'I @target @iii @((P) (Supertype i) ii) `compose` supertype) `compose` supertype `compose` supertype `compose` component @target @I @(T'I'II tt ii `T'TT'I` T'II'I (P) ii) `compose` subtype @_ @(I (Supertype i)) `compose` supertype
st'hjd___'tb = fio @target (objective @T'II'I @target @iii @((P) (Supertype i) ii) `compose` supertype) `compose` supertype `compose` supertype `compose` component @target @I @(T'I'II tt ii `T'TT'I` T'II'I (P) ii) `compose` subtype @_ @(I (Supertype i)) `compose` supertype
st'hjd____'tb = fio @target (objective @T'II'I @target @iii @((P) (Supertype i) ii) `compose` supertype) `compose` supertype `compose` supertype `compose` component @target @I @(T'I'II tt ii `T'TT'I` T'II'I (P) ii) `compose` subtype @_ @(I (Supertype i)) `compose` supertype

yai'hjd, ha'hjd, ha_'hjd, ha__'hjd, ha___'hjd, ha____'hjd, ha_____'hjd, ha______'hjd, ha_______'hjd, ha________'hjd
 :: forall source target t tt ttt i ii iii a o .
 (forall e . Adjoint Functor source source (T'II'I tt e) (T'I'II ttt e)) =>
 Contravariant Yoneda Functor source target (T'II'I t i) =>
 (forall e . Contravariant Semi Functor source target (T'II'I target e)) =>
 (forall e . Contravariant Endo Semi Functor source (T'II'I source e)) =>
 Hom Functor target =>
 (forall e . Wrapper source (I e)) =>
 (forall e ee . Wrapper source (T'II'I tt e ee)) =>
 (forall e ee . Wrapper source (T'I'II ttt e ee)) =>
 (forall e ee . Wrapper target (T'II'I t e ee)) =>
 (forall e ee . Wrapper target (T'I'II target e ee)) =>
 (forall e ee . Wrapper target (T'II'I target e ee)) =>
 (forall e ee . Wrapper source (T'II'I source e ee)) =>
 (forall e ee . Wrapper target (T'II'I source e ee)) =>
 (forall e ee eee . Wrapper source (T'I'II ttt ee `T'TT'I` T'II'I tt e `T'I_` eee)) =>
 (forall e ee eee . Wrapper source (T'II'I tt ee `T'TT'I` T'I'II ttt e `T'I_` eee)) =>
 target (t a i) (target (source (ttt ii (tt o ii)) a) (t o i))
yai'hjd = fai @source (fai @source hjd) `compose` yai @source @target @t @i

ha'hjd = yai'hjd @source @target @t @tt @ttt @i @ii @iii
ha_'hjd = yai'hjd @source @target @t @tt @ttt @i @ii @iii
ha__'hjd = yai'hjd @source @target @t @tt @ttt @i @ii @iii
ha___'hjd = yai'hjd @source @target @t @tt @ttt @i @ii @iii
ha____'hjd = yai'hjd @source @target @t @tt @ttt @i @ii @iii
ha_____'hjd = yai'hjd @source @target @t @tt @ttt @i @ii @iii
ha______'hjd = yai'hjd @source @target @t @tt @ttt @i @ii @iii
ha_______'hjd = yai'hjd @source @target @t @tt @ttt @i @ii @iii
ha________'hjd = yai'hjd @source @target @t @tt @ttt @i @ii @iii

yai'hjd'eq, ha'hjd'eq, ha_'hjd'eq, ha__'hjd'eq, ha___'hjd'eq, ha____'hjd'eq, ha_____'hjd'eq, ha______'hjd'eq, ha_______'hjd'eq, ha________'hjd'eq
 :: forall target t i ii iiii a o .
 Contravariant Yoneda Functor (AR) target (T'II'I t i) =>
 (forall e . Covariant Endo Semi Functor target (T'I'II target e)) =>
 (forall e . Contravariant Semi Functor (AR) target (T'II'I target e)) =>
 Hom Functor target =>
 Adjoint Functor target target (T'II'I P ii) (T'I'II AR ii) =>
 (forall e . Wrapper target (T'I'II AR ii `T'TT'I` T'II'I P ii `T'I_` e)) =>
 (forall e . Wrapper target (I e)) =>
 (forall e . Wrapper target (T'II'I P ii e)) =>
 (forall e ee . Wrapper target (T'I'II t e ee)) =>
 (forall e ee . Wrapper target (T'II'I t e ee)) =>
 (forall e ee . Wrapper target (T'II'I AR e ee)) =>
 (forall e ee . Wrapper target (T'I'II target e ee)) =>
 (forall e ee . Wrapper target (T'II'I target e ee)) =>
 Setoid (AR) a =>
 target (t (a `P` a `S` a) i) (target a (t a i))
yai'hjd'eq = fai @AR (hjd'eq @(AR)) `compose` yai @AR @target @t @i

ha'hjd'eq = yai'hjd'eq @target @t @i @ii @iiii @a @o
ha_'hjd'eq = yai'hjd'eq @target @t @i @ii @iiii @a @o
ha__'hjd'eq = yai'hjd'eq @target @t @i @ii @iiii @a @o
ha___'hjd'eq = yai'hjd'eq @target @t @i @ii @iiii @a @o
ha____'hjd'eq = yai'hjd'eq @target @t @i @ii @iiii @a @o
ha_____'hjd'eq = yai'hjd'eq @target @t @i @ii @iiii @a @o
ha______'hjd'eq = yai'hjd'eq @target @t @i @ii @iiii @a @o
ha_______'hjd'eq = yai'hjd'eq @target @t @i @ii @iiii @a @o
ha________'hjd'eq = yai'hjd'eq @target @t @i @ii @iiii @a @o

yio'hjd, ho'hjd, ho_'hjd, ho__'hjd, ho___'hjd, ho____'hjd, ho_____'hjd, ho______'hjd, ho_______'hjd, ho________'hjd
 :: forall source target t tt ttt i ii iii a o .
 (forall e ee . Adjoint Functor source source (T'II'I tt e) (T'I'II ttt ee)) =>
 Covariant Yoneda Functor source target (T'I'II t i) =>
 (forall e . Contravariant Semi Functor source target (T'II'I target e)) =>
 (forall e . Contravariant Endo Semi Functor source (T'II'I source e)) =>
 Hom Functor target =>
 (forall e . Wrapper source (I e)) =>
 (forall e ee . Wrapper source (T'II'I tt e ee)) =>
 (forall e ee . Wrapper source (T'I'II ttt e ee)) =>
 (forall e ee . Wrapper target (T'I'II t e ee)) =>
 (forall e ee . Wrapper target (T'I'II target e ee)) =>
 (forall e ee . Wrapper target (T'II'I target e ee)) =>
 (forall e ee . Wrapper source (T'II'I source e ee)) =>
 (forall e ee . Wrapper target (T'I'II source e ee)) =>
 (forall e ee eee . Wrapper source (T'I'II ttt ee `T'TT'I` T'II'I tt e `T'I_` eee)) =>
 (forall e ee eee . Wrapper source (T'II'I tt ee `T'TT'I` T'I'II ttt e `T'I_` eee)) =>
 target (t i a) (target (source (ttt ii (tt a ii)) o) (t i o))
yio'hjd = fai @source (fai @source hjd) `compose` yio @source @target @t @i

ho'hjd = yio'hjd @source @target @t @tt @ttt @i @ii @iii
ho_'hjd = yio'hjd @source @target @t @tt @ttt @i @ii @iii
ho__'hjd = yio'hjd @source @target @t @tt @ttt @i @ii @iii
ho___'hjd = yio'hjd @source @target @t @tt @ttt @i @ii @iii
ho____'hjd = yio'hjd @source @target @t @tt @ttt @i @ii @iii
ho_____'hjd = yio'hjd @source @target @t @tt @ttt @i @ii @iii
ho______'hjd = yio'hjd @source @target @t @tt @ttt @i @ii @iii
ho_______'hjd = yio'hjd @source @target @t @tt @ttt @i @ii @iii
ho________'hjd = yio'hjd @source @target @t @tt @ttt @i @ii @iii

yio'hjd'eq, ho'hjd'eq, ho_'hjd'eq, ho__'hjd'eq, ho___'hjd'eq, ho____'hjd'eq, ho_____'hjd'eq, ho______'hjd'eq, ho_______'hjd'eq, ho________'hjd'eq
 :: forall target t a i .
 Setoid (AR) a =>
 Covariant Yoneda Functor (AR) target (T'I'II t i) =>
 (forall e . Covariant Endo Semi Functor target (T'I'II target e)) =>
 (forall e . Contravariant Semi Functor (AR) target (T'II'I target e)) =>
 Hom Functor target =>
 (forall e ee . Wrapper target (T'I'II target e ee)) =>
 (forall e ee . Wrapper target (T'II'I target e ee)) =>
 (forall e ee . Wrapper target (T'I'II (AR) e ee)) =>
 (forall e ee . Wrapper target (T'I'II t i e)) =>
 target (t i a) (target a (t i (a `P` a `S` a)))
yio'hjd'eq = fai @AR (hjd'eq @(AR)) `compose` yio @AR @target @t @i

ho'hjd'eq = yio'hjd'eq @target @t
ho_'hjd'eq = yio'hjd'eq @target @t
ho__'hjd'eq = yio'hjd'eq @target @t
ho___'hjd'eq = yio'hjd'eq @target @t
ho____'hjd'eq = yio'hjd'eq @target @t
ho_____'hjd'eq = yio'hjd'eq @target @t
ho______'hjd'eq = yio'hjd'eq @target @t
ho_______'hjd'eq = yio'hjd'eq @target @t
ho________'hjd'eq = yio'hjd'eq @target @t

hdj, hdj_, hdj__, hdj___, hdj____ :: forall target t tt i e ee .
 Adjoint Functor target target (T'II'I t e) (T'I'II tt ee) =>
 (forall eee . Wrapper target (T'II'I t e `T'TT'I` T'I'II tt ee `T'I_` eee)) =>
 (forall eee . Wrapper target (I eee)) =>
 (forall eee . Wrapper target (T'II'I t e eee)) =>
 (forall eee . Wrapper target (T'I'II tt ee eee)) =>
 target (t (tt ee i) e) i
hdj = supertype `compose` component @target @(T'II'I t e `T'TT'I` T'I'II tt ee) @I
 `compose` subtype `compose` subtype `compose` foi @target subtype

hdj_ = hdj
hdj__ = hdj
hdj___ = hdj
hdj____ = hdj

eq, eq_, eq__, eq___, eq____, eq_____, eq______, eq_______, eq________ ::
 forall target e .
 Setoid target e =>
 target (e `P` e) (e `P` e `S` e)
eq = equality

eq_ = eq
eq__ = eq
eq___ = eq
eq____ = eq
eq_____ = eq
eq______ = eq
eq_______ = eq
eq________ = eq

infixl 6 `yo'nt'yo`
infixl 5 `yo'nt_'yo`
infixl 4 `yo'nt__'yo`
infixl 3 `yo'nt___'yo`
infixl 2 `yo'nt____'yo`
infixl 1 `yo'nt_____'yo`

yo'nt'yo, yo'nt_'yo, yo'nt__'yo, yo'nt___'yo, yo'nt____'yo, yo'nt_____'yo
 :: forall source target t tt ll a o .
 Hom Functor source =>
 Hom Functor target =>
 Covariant Yoneda Functor source target t =>
 Component target (t `L` tt `T` ll) tt =>
 (forall e . Contravariant Functor source target (T'II'I target e)) =>
 (forall e ee . Wrapper source (T'I'II source e ee)) =>
 (forall e ee . Wrapper target (T'I'II source e ee)) =>
 (forall e ee . Wrapper target (T'II'I target e ee)) =>
 (forall e ee . Wrapper target (T'I'II target e ee)) =>
 (forall e . Wrapper source (I e)) =>
 (forall e . Wrapper source (I `L` tt `T` ll `T` e)) =>
 (forall e . Wrapper target (t `L` tt `T` ll `T` e)) =>
 target (t a) (target (source a (I `L` tt `T` ll `T` o)) (tt o))
yo'nt'yo = fio (component @target @(t `L` tt `T` ll) @tt `compose` subtype @target)
 `compose` (fai @source `compose` fio @source) (supertype `compose` supertype)
 `compose` yo

yo'nt_'yo = yo'nt'yo
yo'nt__'yo = yo'nt'yo
yo'nt___'yo = yo'nt'yo
yo'nt____'yo = yo'nt'yo
yo'nt_____'yo = yo'nt'yo

infixl 6 `ya'nt'ya`
infixl 5 `ya'nt_'ya`
infixl 4 `ya'nt__'ya`
infixl 3 `ya'nt___'ya`
infixl 2 `ya'nt____'ya`
infixl 1 `ya'nt_____'ya`

ya'nt'ya, ya'nt_'ya, ya'nt__'ya, ya'nt___'ya, ya'nt____'ya, ya'nt_____'ya
 :: forall source target t tt ll a o .
 Hom Functor source =>
 Hom Functor target =>
 Contravariant Yoneda Functor source target t =>
 Component target (t `L` tt `T` ll) tt =>
 (forall e . Contravariant Functor source target (T'II'I target e)) =>
 (forall e ee . Wrapper target (T'II'I source e ee)) =>
 (forall e ee . Wrapper source (T'I'II source e ee)) =>
 (forall e ee . Wrapper target (T'II'I target e ee)) =>
 (forall e ee . Wrapper target (T'I'II target e ee)) =>
 (forall e . Wrapper source (I e)) =>
 (forall e . Wrapper source (I `L` tt `T` ll `T` e)) =>
 (forall e . Wrapper target (t `L` tt `T` ll `T` e)) =>
 target (t a) (target (source o (I `L` tt `T` ll `T` a)) (tt o))
ya'nt'ya = fio (component @target @(t `L` tt `T` ll) @tt `compose` subtype @target)
 `compose` (fai @source `compose` fio @source) (supertype `compose` supertype)
 `compose` ya

ya'nt_'ya = ya'nt'ya
ya'nt__'ya = ya'nt'ya
ya'nt___'ya = ya'nt'ya
ya'nt____'ya = ya'nt'ya
ya'nt_____'ya = ya'nt'ya

infixl 5 `yio'nt'yo`

infixl 7 `ho'nt'yo`
infixl 6 `ho'nt_'yo`
infixl 5 `ho'nt__'yo`
infixl 3 `ho'nt___'yo`
infixl 2 `ho'nt____'yo`
infixl 1 `ho'nt_____'yo`

yio'nt'yo, ho'nt'yo, ho'nt_'yo, ho'nt__'yo, ho'nt___'yo, ho'nt____'yo, ho'nt_____'yo
 :: forall source target t tt ll a o i .
 Hom Functor source =>
 Hom Functor target =>
 (forall e . Covariant Yoneda Functor source target (T'I'II t e)) =>
 Component target (T'I'II t i `L` tt `T` ll) tt =>
 (forall e . Contravariant Functor source target (T'II'I target e)) =>
 (forall e ee . Wrapper target (T'I'II source e ee)) =>
 (forall e ee . Wrapper source (T'I'II source e ee)) =>
 (forall e ee . Wrapper target (T'II'I target e ee)) =>
 (forall e ee . Wrapper target (T'I'II target e ee)) =>
 (forall e ee . Wrapper target (T'I'II t e ee)) =>
 (forall e . Wrapper source (I e)) =>
 (forall e . Wrapper source (I `L` tt `T` ll `T` e)) =>
 (forall e ee . Wrapper target (T'I'II t ee `L` tt `T` ll `T` e)) =>
 target (t i a) (target (source a (I `L` tt `T` ll `T` o)) (tt o))
yio'nt'yo = fio (component @target @(T'I'II t i `L` tt `T` ll) @tt `compose` subtype @target)
 `compose` (fai @source `compose` fio @source) (supertype `compose` supertype)
 `compose` yo
 `compose` subtype

ho'nt'yo = yio'nt'yo
ho'nt_'yo = yio'nt'yo
ho'nt__'yo = yio'nt'yo
ho'nt___'yo = yio'nt'yo
ho'nt____'yo = yio'nt'yo
ho'nt_____'yo = yio'nt'yo

infixl 4 `yio'nt'yio`

yio'nt'yio
 :: forall source target t tt ll a o i ii .
 Hom Functor source =>
 Hom Functor target =>
 (forall e . Covariant Yoneda Functor source target (T'I'II t e)) =>
 Component target (T'I'II t i `L` T'I'II tt ii `T` ll) (T'I'II tt ii) =>
 (forall e . Contravariant Functor source target (T'II'I target e)) =>
 (forall e ee . Wrapper target (T'I'II source e ee)) =>
 (forall e ee . Wrapper source (T'I'II source e ee)) =>
 (forall e ee . Wrapper target (T'II'I target e ee)) =>
 (forall e ee . Wrapper target (T'I'II target e ee)) =>
 (forall e ee . Wrapper target (T'I'II t e ee)) =>
 (forall e ee . Wrapper target (T'I'II tt e ee)) =>
 (forall e . Wrapper source (I e)) =>
 (forall e . Wrapper source (I `L` T'I'II tt ii `T` ll `T` e)) =>
 (forall e ee . Wrapper target (T'I'II t ee `L` T'I'II tt ii `T` ll `T` e)) =>
 target (t i a) (target (source a (I `L` T'I'II tt ii `T` ll `T` o)) (tt ii o))
yio'nt'yio = fio (wrapped (component @target @(T'I'II t i `L` T'I'II tt ii `T` ll) @(T'I'II tt ii)))
 `compose` (fai @source `compose` fio @source) (supertype `compose` supertype)
 `compose` yo
 `compose` subtype

infixl 5 `yai'nt'ya`

infixl 7 `ha'nt'ya`
infixl 6 `ha'nt_'ya`
infixl 5 `ha'nt__'ya`
infixl 3 `ha'nt___'ya`
infixl 2 `ha'nt____'ya`
infixl 1 `ha'nt_____'ya`

yai'nt'ya, ha'nt'ya, ha'nt_'ya, ha'nt__'ya, ha'nt___'ya, ha'nt____'ya, ha'nt_____'ya
 :: forall source target t tt ll a o i .
 Hom Functor source =>
 Hom Functor target =>
 (forall e . Contravariant Yoneda Functor source target (T'II'I t e)) =>
 Component target (T'II'I t i `L` tt `T` ll) tt =>
 (forall e . Contravariant Functor source target (T'II'I target e)) =>
 (forall e ee . Wrapper target (T'II'I source e ee)) =>
 (forall e ee . Wrapper source (T'I'II source e ee)) =>
 (forall e ee . Wrapper target (T'II'I target e ee)) =>
 (forall e ee . Wrapper target (T'I'II target e ee)) =>
 (forall e ee . Wrapper target (T'II'I t e ee)) =>
 (forall e . Wrapper source (I e)) =>
 (forall e . Wrapper source (I `L` tt `T` ll `T` e)) =>
 (forall e ee . Wrapper target (T'II'I t ee `L` tt `T` ll `T` e)) =>
 target (t a i) (target (source o (I `L` tt `T` ll `T` a)) (tt o))
yai'nt'ya = fio (component @target @(T'II'I t i `L` tt `T` ll) @tt `compose` subtype @target)
 `compose` (fai @source `compose` fio @source) (supertype `compose` supertype)
 `compose` ya
 `compose` subtype

ha'nt'ya = yai'nt'ya
ha'nt_'ya = yai'nt'ya
ha'nt__'ya = yai'nt'ya
ha'nt___'ya = yai'nt'ya
ha'nt____'ya = yai'nt'ya
ha'nt_____'ya = yai'nt'ya

infixl 8 `ho'nt'ho`, `ho'nt'ho'st`
infixl 7 `ho'nt_'ho`, `ho'nt_'ho'st`
infixl 6 `ho'nt__'ho`, `ho'nt__'ho'st`
infixl 5 `ho'nt___'ho`, `ho'nt___'ho'st`
infixl 4 `ho'nt____'ho`, `ho'nt____'ho'st`
infixl 3 `ho'nt_____'ho`, `ho'nt_____'ho'st`
infixl 2 `ho'nt______'ho`, `ho'nt______'ho'st`

ho'nt'ho, ho'nt_'ho, ho'nt__'ho, ho'nt___'ho, ho'nt____'ho, ho'nt_____'ho, ho'nt______'ho
 :: forall target t tt o i ii .
 (forall e . Covariant Yoneda Functor target target (T'I'II t e)) =>
 Component target (T'I'II t i `L` T'I'II tt ii `T` (Void)) (T'I'II tt ii) =>
 (forall e ee . Wrapper target (T'I'II t e ee)) =>
 (forall e ee . Wrapper target (T'I'II tt e ee)) =>
 (forall e ee . Wrapper target (T'I'II t ee `L` T'I'II tt ii `T` (Void) `T` e)) =>
 target (t i o) (tt ii o)
ho'nt'ho = (wrapped (component @target @(T'I'II t i `L` T'I'II tt ii `T` (Void)) @(T'I'II tt ii))) `compose` subtype

ho'nt_'ho = ho'nt'ho
ho'nt__'ho = ho'nt'ho
ho'nt___'ho = ho'nt'ho
ho'nt____'ho = ho'nt'ho
ho'nt_____'ho = ho'nt'ho
ho'nt______'ho = ho'nt'ho

ho'nt'ho'st, ho'nt_'ho'st, ho'nt__'ho'st, ho'nt___'ho'st, ho'nt____'ho'st, ho'nt_____'ho'st, ho'nt______'ho'st
 :: forall target t tt o i ii .
 (forall e . Covariant Endo Yoneda Functor target (T'I'II t e)) =>
 (forall e . Covariant Endo Yoneda Functor target (T'I'II tt e)) =>
 Component target (T'I'II t i `L` T'I'II tt ii `T` (Void)) (T'I'II tt ii) =>
 (forall e ee . Wrapper target (T'I'II t e ee)) =>
 (forall e ee . Wrapper target (T'I'II tt e ee)) =>
 (forall e ee . Wrapper target (T'I'II t ee `L` T'I'II tt ii `T` (Void) `T` e)) =>
 Covariant Elicitable target o =>
 target (t i o) (tt ii (Supertype o))
ho'nt'ho'st = fio @target @target supertype `compose` (wrapped (component @target @(T'I'II t i `L` T'I'II tt ii `T` (Void)) @(T'I'II tt ii))) `compose` subtype

ho'nt_'ho'st = ho'nt'ho'st
ho'nt__'ho'st = ho'nt'ho'st
ho'nt___'ho'st = ho'nt'ho'st
ho'nt____'ho'st = ho'nt'ho'st
ho'nt_____'ho'st = ho'nt'ho'st
ho'nt______'ho'st = ho'nt'ho'st

infixl 8 `ha'nt'ha`, `ha'nt'ha'st`, `st'ha'nt'ha`, `st'ha'nt'ha'st`, `bt'ha'nt'ha`
infixl 7 `ha'nt_'ha`, `ha'nt_'ha'st`, `st'ha'nt_'ha`, `st'ha'nt_'ha'st`, `bt'ha'nt_'ha`
infixl 6 `ha'nt__'ha`, `ha'nt__'ha'st`, `st'ha'nt__'ha`, `st'ha'nt__'ha'st`, `bt'ha'nt__'ha`
infixl 5 `ha'nt___'ha`, `ha'nt___'ha'st`, `st'ha'nt___'ha`, `st'ha'nt___'ha'st`, `bt'ha'nt___'ha`
infixl 4 `ha'nt____'ha`, `ha'nt____'ha'st`, `st'ha'nt____'ha`, `st'ha'nt____'ha'st`, `bt'ha'nt____'ha`
infixl 3 `ha'nt_____'ha`, `ha'nt_____'ha'st`, `st'ha'nt_____'ha`, `st'ha'nt_____'ha'st`, `bt'ha'nt_____'ha`
infixl 2 `ha'nt______'ha`, `ha'nt______'ha'st`, `st'ha'nt______'ha`, `st'ha'nt______'ha'st`, `bt'ha'nt______'ha`

ha'nt'ha, ha'nt_'ha, ha'nt__'ha, ha'nt___'ha, ha'nt____'ha, ha'nt_____'ha, ha'nt______'ha
 :: forall target t tt a i ii .
 (forall e . Contravariant Yoneda Functor target target (T'II'I t e)) =>
 Component target (T'II'I t i `L` T'II'I tt ii `T` (Void)) (T'II'I tt ii) =>
 (forall e ee . Wrapper target (T'II'I t e ee)) =>
 (forall e ee . Wrapper target (T'II'I tt e ee)) =>
 (forall e ee . Wrapper target (T'II'I t ee `L` T'II'I tt ii `T` (Void) `T` e)) =>
 target (t a i) (tt a ii)
ha'nt'ha = (wrapped (component @target @(T'II'I t i `L` T'II'I tt ii `T` (Void)) @(T'II'I tt ii))) `compose` subtype

ha'nt_'ha = ha'nt'ha
ha'nt__'ha = ha'nt'ha
ha'nt___'ha = ha'nt'ha
ha'nt____'ha = ha'nt'ha
ha'nt_____'ha = ha'nt'ha
ha'nt______'ha = ha'nt'ha

ha'nt'ha'st, ha'nt_'ha'st, ha'nt__'ha'st, ha'nt___'ha'st, ha'nt____'ha'st, ha'nt_____'ha'st, ha'nt______'ha'st
 :: forall target t tt a i ii .
 (forall e . Contravariant Endo Yoneda Functor target (T'II'I t e)) =>
 (forall e . Contravariant Endo Yoneda Functor target (T'II'I tt e)) =>
 Component target (T'II'I t i `L` T'II'I tt ii `T` (Void)) (T'II'I tt ii) =>
 (forall e ee . Wrapper target (T'II'I t e ee)) =>
 (forall e ee . Wrapper target (T'II'I tt e ee)) =>
 (forall e ee . Wrapper target (T'II'I t ee `L` T'II'I tt ii `T` (Void) `T` e)) =>
 Covariant Elicitable target a =>
 target (t (Supertype a) i) (tt a ii)
ha'nt'ha'st = fai @target @target supertype `compose` (wrapped (component @target @(T'II'I t i `L` T'II'I tt ii `T` (Void)) @(T'II'I tt ii))) `compose` subtype

ha'nt_'ha'st = ha'nt'ha'st
ha'nt__'ha'st = ha'nt'ha'st
ha'nt___'ha'st = ha'nt'ha'st
ha'nt____'ha'st = ha'nt'ha'st
ha'nt_____'ha'st = ha'nt'ha'st
ha'nt______'ha'st = ha'nt'ha'st

st'ha'nt'ha, st'ha'nt_'ha, st'ha'nt__'ha, st'ha'nt___'ha, st'ha'nt____'ha, st'ha'nt_____'ha, st'ha'nt______'ha
 :: forall target e t tt a i ii .
 (forall e . Contravariant Yoneda Functor target target (T'II'I t e)) =>
 Component target (T'II'I t i `L` T'II'I tt ii `T` (Void)) (T'II'I tt ii) =>
 (forall e ee . Wrapper target (T'II'I t e ee)) =>
 (forall e ee . Wrapper target (T'II'I tt e ee)) =>
 (forall e ee . Wrapper target (T'II'I t ee `L` T'II'I tt ii `T` (Void) `T` e)) =>
 Covariant Elicitable target e =>
 (Supertype e ~ t a i) =>
 target e (tt a ii)
st'ha'nt'ha = wrapped (component @target @(T'II'I t i `L` T'II'I tt ii `T` (Void)) @(T'II'I tt ii)) `compose` subtype `compose` supertype

st'ha'nt_'ha = st'ha'nt'ha
st'ha'nt__'ha = st'ha'nt'ha
st'ha'nt___'ha = st'ha'nt'ha
st'ha'nt____'ha = st'ha'nt'ha
st'ha'nt_____'ha = st'ha'nt'ha
st'ha'nt______'ha = st'ha'nt'ha

st'ha'nt'ha'st, st'ha'nt_'ha'st, st'ha'nt__'ha'st, st'ha'nt___'ha'st, st'ha'nt____'ha'st, st'ha'nt_____'ha'st, st'ha'nt______'ha'st
 :: forall target e t tt a i ii .
 (forall e . Contravariant Endo Yoneda Functor target (T'II'I t e)) =>
 (forall e . Contravariant Endo Yoneda Functor target (T'II'I tt e)) =>
 Component target (T'II'I t i `L` T'II'I tt ii `T` (Void)) (T'II'I tt ii) =>
 (forall e ee . Wrapper target (T'II'I t e ee)) =>
 (forall e ee . Wrapper target (T'II'I tt e ee)) =>
 (forall e ee . Wrapper target (T'II'I t ee `L` T'II'I tt ii `T` (Void) `T` e)) =>
 Covariant Elicitable target e =>
 Covariant Elicitable target a =>
 (Supertype e ~ t (Supertype a) i) =>
 target e (tt a ii)
st'ha'nt'ha'st = fai @target @target supertype `compose` wrapped (component @target @(T'II'I t i `L` T'II'I tt ii `T` (Void)) @(T'II'I tt ii)) `compose` subtype `compose` supertype

st'ha'nt_'ha'st = st'ha'nt'ha'st
st'ha'nt__'ha'st = st'ha'nt'ha'st
st'ha'nt___'ha'st = st'ha'nt'ha'st
st'ha'nt____'ha'st = st'ha'nt'ha'st
st'ha'nt_____'ha'st = st'ha'nt'ha'st
st'ha'nt______'ha'st = st'ha'nt'ha'st

bt'ha'nt'ha, bt'ha'nt_'ha, bt'ha'nt__'ha, bt'ha'nt___'ha, bt'ha'nt____'ha, bt'ha'nt_____'ha, bt'ha'nt______'ha
 :: forall target e t tt a i ii .
 (forall e . Contravariant Yoneda Functor target target (T'II'I t e)) =>
 Component target (T'II'I t i `L` T'II'I tt ii `T` (Void)) (T'II'I tt ii) =>
 (forall e ee . Wrapper target (T'II'I t e ee)) =>
 (forall e ee . Wrapper target (T'II'I tt e ee)) =>
 (forall e ee . Wrapper target (T'II'I t ee `L` T'II'I tt ii `T` (Void) `T` e)) =>
 Covariant Objective target e (t a i) =>
 (Basetype e ~ t a i) =>
 target e (tt a ii)
bt'ha'nt'ha = wrapped (component @target @(T'II'I t i `L` T'II'I tt ii `T` (Void)) @(T'II'I tt ii)) `compose` subtype `compose` basetype

bt'ha'nt_'ha = bt'ha'nt'ha
bt'ha'nt__'ha = bt'ha'nt'ha
bt'ha'nt___'ha = bt'ha'nt'ha
bt'ha'nt____'ha = bt'ha'nt'ha
bt'ha'nt_____'ha = bt'ha'nt'ha
bt'ha'nt______'ha = bt'ha'nt'ha
