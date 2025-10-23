{-# LANGUAGE AllowAmbiguousTypes #-}
module Ya.Operators.Generated.XX where

import Ya.Algebra.Abstract
import Ya.Algebra.Definition
import Ya.Algebra.Instances ()

import Ya.Operators.Mappings
import Ya.Operators.Handcraft

infixl 2 `ha_______'yo`, `ha_______'ya`, `ha_______'yoi`, `ha_______'ha`, `ha_______'ho`, `ha_______'yia`, `ho_______'yo`, `ho_______'ya`, `ho_______'yoi`, `ho_______'ha`, `ho_______'ho`, `ho_______'yia`
infixl 3 `ha______'yo`, `ha______'ya`, `ha______'yoi`, `ha______'ha`, `ha______'ho`, `ha______'yia`, `ho______'yo`, `ho______'ya`, `ho______'yoi`, `ho______'ha`, `ho______'ho`, `ho______'yia`
infixl 4 `ha_____'yo`, `ha_____'ya`, `ha_____'yoi`, `ha_____'ha`, `ha_____'ho`, `ha_____'yia`, `ho_____'yo`, `ho_____'ya`, `ho_____'yoi`, `ho_____'ha`, `ho_____'ho`, `ho_____'yia`
infixl 5 `ha____'yo`, `ha____'ya`, `ha____'yoi`, `ha____'ha`, `ha____'ho`, `ha____'yia`, `ho____'yo`, `ho____'ya`, `ho____'yoi`, `ho____'ha`, `ho____'ho`, `ho____'yia`
infixl 6 `ha___'yo`, `ha___'ya`, `ha___'yoi`, `ha___'ha`, `ha___'ho`, `ha___'yia`, `ho___'yo`, `ho___'ya`, `ho___'yoi`, `ho___'ha`, `ho___'ho`, `ho___'yia`
infixl 7 `yoi'yo`, `yoi'ya`, `yoi'yoi`, `yoi'yai`, `yoi'ha`, `yoi'yio`, `yoi'ho`, `yoi'yia`, `yai'yo`, `ha__'yo`, `yai'ya`, `ha__'ya`, `yai'yoi`, `ha__'yoi`, `yai'yai`, `ha__'ha`, `yai'yio`, `ha__'ho`, `yai'yia`, `ha__'yia`, `yio'yo`, `ho__'yo`, `yio'ya`, `ho__'ya`, `yio'yoi`, `ho__'yoi`, `yio'yai`, `ho__'ha`, `yio'yio`, `ho__'ho`, `yio'yia`, `ho__'yia`, `yia'yo`, `yia'ya`, `yia'yoi`, `yia'yai`, `yia'ha`, `yia'yio`, `yia'ho`, `yia'yia`
infixl 8 `yo'yo`, `yo'ya`, `yo'yoi`, `yo'yai`, `yo'ha`, `yo'yio`, `yo'ho`, `yo'yia`, `ya'yo`, `ya'ya`, `ya'yoi`, `ya'yai`, `ya'ha`, `ya'yio`, `ya'ho`, `ya'yia`, `ha_'yo`, `ha_'ya`, `ha_'yoi`, `ha_'ha`, `ha_'ho`, `ha_'yia`, `ho_'yo`, `ho_'ya`, `ho_'yoi`, `ho_'ha`, `ho_'ho`, `ho_'yia`
infixl 9 `ha'yo`, `ha'ya`, `ha'yoi`, `ha'ha`, `ha'ho`, `ha'yia`, `ho'yo`, `ho'ya`, `ho'yoi`, `ho'ha`, `ho'ho`, `ho'yia`

yo'yo
 :: forall source into t tt a o .
 Covariant Endo Semi Functor source tt =>
 Covariant Yoneda Functor source into t =>
 Contravariant Endo Semi Functor (AR) (T'II'I into (t (tt o))) =>
 (forall e ee . Wrapper into (T'I'II source e ee)) =>
 (t (tt a)) -> into (source (a) o) (t (tt o))
yo'yo = fai (fo @source @source @tt) `compose` yo @source @into

yo'ya
 :: forall source into t tt a o .
 Contravariant Endo Semi Functor source tt =>
 Covariant Yoneda Functor source into t =>
 Contravariant Endo Semi Functor (AR) (T'II'I into (t (tt a))) =>
 (forall e ee . Wrapper into (T'I'II source e ee)) =>
 (t (tt o)) -> into (source (a) o) (t (tt a))
yo'ya x = fai (fa @source @source @tt) (yo @source @into x)

yo'yoi
 :: forall source into t tt ii a o .
 Covariant Endo Semi Functor source (T'II'I tt ii) =>
 (forall e ee . Wrapper source (T'II'I tt e ee)) =>
 Covariant Yoneda Functor source into t =>
 Contravariant Endo Semi Functor (AR) (T'II'I into (t (tt o ii))) =>
 (forall e ee . Wrapper into (T'I'II source e ee)) =>
 (t (tt a ii)) -> into (source (a) o) (t (tt o ii))
yo'yoi x = fai (foi @source @source @tt) (yo @source @into x)

yo'yai, yo'ha
 :: forall source into t tt ii a o .
 Contravariant Endo Semi Functor source (T'II'I tt ii) =>
 (forall e ee . Wrapper source (T'II'I tt e ee)) =>
 Covariant Yoneda Functor source into t =>
 Contravariant Endo Semi Functor (AR) (T'II'I into (t (tt a ii))) =>
 (forall e ee . Wrapper into (T'I'II source e ee)) =>
 (t (tt o ii)) -> into (source (a) o) (t (tt a ii))
yo'yai x = fai (fai @source @source @tt) (yo @source @into x)
yo'ha = yo'yai

yo'yio, yo'ho
 :: forall source into t tt ii a o .
 Covariant Endo Semi Functor source (T'I'II tt ii) =>
 (forall e ee . Wrapper source (T'I'II tt e ee)) =>
 Covariant Yoneda Functor source into t =>
 Contravariant Endo Semi Functor (AR) (T'II'I into (t (tt ii (o)))) =>
 (forall e ee . Wrapper into (T'I'II source e ee)) =>
 (t (tt ii (a))) -> into (source (a) o) (t (tt ii (o)))
yo'yio x = fai (fio @source @source @tt) (yo @source @into x)
yo'ho = yo'yio

yo'yia
 :: forall source into t tt ii a o .
 Contravariant Endo Semi Functor source (T'I'II tt ii) =>
 (forall e ee . Wrapper source (T'I'II tt e ee)) =>
 Covariant Yoneda Functor source into t =>
 Contravariant Endo Semi Functor (AR) (T'II'I into (t (tt ii (a)))) =>
 (forall e ee . Wrapper into (T'I'II source e ee)) =>
 (t (tt ii (o))) -> into (source (a) o) (t (tt ii (a)))
yo'yia x = fai (fia @source @source @tt) (yo @source @into x)

ya'yo
 :: forall source into t tt a o .
 Covariant Endo Semi Functor source tt =>
 Contravariant Yoneda Functor source into t =>
 Contravariant Endo Semi Functor (AR) (T'II'I into (t (tt a))) =>
 (forall e ee . Wrapper into (T'II'I source e ee)) =>
 (t (tt o)) -> into (source (a) o) (t (tt a))
ya'yo x = fai (fo @source @source @tt) (ya @source @into x)

ya'ya
 :: forall source into t tt a o .
 Contravariant Endo Semi Functor source tt =>
 Contravariant Yoneda Functor source into t =>
 Contravariant Endo Semi Functor (AR) (T'II'I into (t (tt o))) =>
 (forall e ee . Wrapper into (T'II'I source e ee)) =>
 (t (tt a)) -> into (source (a) o) (t (tt o))
ya'ya x = fai (fa @source @source @tt) (ya @source @into x)

ya'yoi
 :: forall source into t tt ii a o .
 Covariant Endo Semi Functor source (T'II'I tt ii) =>
 (forall e ee . Wrapper source (T'II'I tt e ee)) =>
 Contravariant Yoneda Functor source into t =>
 Contravariant Endo Semi Functor (AR) (T'II'I into (t (tt a ii))) =>
 (forall e ee . Wrapper into (T'II'I source e ee)) =>
 (t (tt o ii)) -> into (source (a) o) (t (tt a ii))
ya'yoi x = fai (foi @source @source @tt) (ya @source @into x)

ya'yai, ya'ha
 :: forall source into t tt ii a o .
 Contravariant Endo Semi Functor source (T'II'I tt ii) =>
 (forall e ee . Wrapper source (T'II'I tt e ee)) =>
 Contravariant Yoneda Functor source into t =>
 Contravariant Endo Semi Functor (AR) (T'II'I into (t (tt o ii))) =>
 (forall e ee . Wrapper into (T'II'I source e ee)) =>
 (t (tt a ii)) -> into (source (a) o) (t (tt o ii))
ya'yai x = fai (fai @source @source @tt) (ya @source @into x)
ya'ha = ya'yai

ya'yio, ya'ho
 :: forall source into t tt ii a o .
 Covariant Endo Semi Functor source (T'I'II tt ii) =>
 (forall e ee . Wrapper source (T'I'II tt e ee)) =>
 Contravariant Yoneda Functor source into t =>
 Contravariant Endo Semi Functor (AR) (T'II'I into (t (tt ii (a)))) =>
 (forall e ee . Wrapper into (T'II'I source e ee)) =>
 (t (tt ii (o))) -> into (source (a) o) (t (tt ii (a)))
ya'yio x = fai (fio @source @source @tt) (ya @source @into x)
ya'ho = ya'yio

ya'yia
 :: forall source into t tt ii a o .
 Contravariant Endo Semi Functor source (T'I'II tt ii) =>
 (forall e ee . Wrapper source (T'I'II tt e ee)) =>
 Contravariant Yoneda Functor source into t =>
 Contravariant Endo Semi Functor (AR) (T'II'I into (t (tt ii (o)))) =>
 (forall e ee . Wrapper into (T'II'I source e ee)) =>
 (t (tt ii (a))) -> into (source (a) o) (t (tt ii (o)))
ya'yia x = fai (fia @source @source @tt) (ya @source @into x)

yoi'yo
 :: forall source into t i tt a o .
 Covariant Endo Semi Functor source tt =>
 Covariant Yoneda Functor source into (T'II'I t i) =>
 (forall e ee . Wrapper into (T'II'I t e ee)) =>
 Contravariant Endo Semi Functor (AR) (T'II'I into (t (tt o) i)) =>
 (forall e ee . Wrapper into (T'I'II source e ee)) =>
 (t (tt a) i) -> into (source (a) o) (t (tt o) i)
yoi'yo x = fai (fo @source @source @tt) (yoi @source @into x)

yoi'ya
 :: forall source into t i tt a o .
 Contravariant Endo Semi Functor source tt =>
 Covariant Yoneda Functor source into (T'II'I t i) =>
 (forall e ee . Wrapper into (T'II'I t e ee)) =>
 Contravariant Endo Semi Functor (AR) (T'II'I into (t (tt a) i)) =>
 (forall e ee . Wrapper into (T'I'II source e ee)) =>
 (t (tt o) i) -> into (source (a) o) (t (tt a) i)
yoi'ya x = fai (fa @source @source @tt) (yoi @source @into x)

yoi'yoi
 :: forall source into t i tt ii a o .
 Covariant Endo Semi Functor source (T'II'I tt ii) =>
 (forall e ee . Wrapper source (T'II'I tt e ee)) =>
 Covariant Yoneda Functor source into (T'II'I t i) =>
 (forall e ee . Wrapper into (T'II'I t e ee)) =>
 Contravariant Endo Semi Functor (AR) (T'II'I into (t (tt o ii) i)) =>
 (forall e ee . Wrapper into (T'I'II source e ee)) =>
 (t (tt a ii) i) -> into (source (a) o) (t (tt o ii) i)
yoi'yoi x = fai (foi @source @source @tt) (yoi @source @into x)

yoi'yai, yoi'ha
 :: forall source into t i tt ii a o .
 Contravariant Endo Semi Functor source (T'II'I tt ii) =>
 (forall e ee . Wrapper source (T'II'I tt e ee)) =>
 Covariant Yoneda Functor source into (T'II'I t i) =>
 (forall e ee . Wrapper into (T'II'I t e ee)) =>
 Contravariant Endo Semi Functor (AR) (T'II'I into (t (tt a ii) i)) =>
 (forall e ee . Wrapper into (T'I'II source e ee)) =>
 (t (tt o ii) i) -> into (source (a) o) (t (tt a ii) i)
yoi'yai x = fai (fai @source @source @tt) (yoi @source @into x)
yoi'ha = yoi'yai

yoi'yio, yoi'ho
 :: forall source into t i tt ii a o .
 Covariant Endo Semi Functor source (T'I'II tt ii) =>
 (forall e ee . Wrapper source (T'I'II tt e ee)) =>
 Covariant Yoneda Functor source into (T'II'I t i) =>
 (forall e ee . Wrapper into (T'II'I t e ee)) =>
 Contravariant Endo Semi Functor (AR) (T'II'I into (t (tt ii (o)) i)) =>
 (forall e ee . Wrapper into (T'I'II source e ee)) =>
 (t (tt ii (a)) i) -> into (source (a) o) (t (tt ii (o)) i)
yoi'yio x = fai (fio @source @source @tt) (yoi @source @into x)
yoi'ho = yoi'yio

yoi'yia
 :: forall source into t i tt ii a o .
 Contravariant Endo Semi Functor source (T'I'II tt ii) =>
 (forall e ee . Wrapper source (T'I'II tt e ee)) =>
 Covariant Yoneda Functor source into (T'II'I t i) =>
 (forall e ee . Wrapper into (T'II'I t e ee)) =>
 Contravariant Endo Semi Functor (AR) (T'II'I into (t (tt ii (a)) i)) =>
 (forall e ee . Wrapper into (T'I'II source e ee)) =>
 (t (tt ii (o)) i) -> into (source (a) o) (t (tt ii (a)) i)
yoi'yia x = fai (fia @source @source @tt) (yoi @source @into x)

yai'yo, ha'yo, ha_'yo, ha__'yo, ha___'yo, ha____'yo, ha_____'yo, ha______'yo, ha_______'yo
 :: forall source into t i tt a o .
 Covariant Endo Semi Functor source tt =>
 Contravariant Yoneda Functor source into (T'II'I t i) =>
 (forall e ee . Wrapper into (T'II'I t e ee)) =>
 Contravariant Endo Semi Functor (AR) (T'II'I into (t (tt a) i)) =>
 (forall e ee . Wrapper into (T'II'I source e ee)) =>
 (t (tt o) i) -> into (source (a) o) (t (tt a) i)
yai'yo x = fai (fo @source @source @tt) (yai @source @into x)
ha'yo = yai'yo
ha_'yo = yai'yo
ha__'yo = yai'yo
ha___'yo = yai'yo
ha____'yo = yai'yo
ha_____'yo = yai'yo
ha______'yo = yai'yo
ha_______'yo = yai'yo

yai'ya, ha'ya, ha_'ya, ha__'ya, ha___'ya, ha____'ya, ha_____'ya, ha______'ya, ha_______'ya
 :: forall source into t i tt a o .
 Contravariant Endo Semi Functor source tt =>
 Contravariant Yoneda Functor source into (T'II'I t i) =>
 (forall e ee . Wrapper into (T'II'I t e ee)) =>
 Contravariant Endo Semi Functor (AR) (T'II'I into (t (tt o) i)) =>
 (forall e ee . Wrapper into (T'II'I source e ee)) =>
 (t (tt a) i) -> into (source (a) o) (t (tt o) i)
yai'ya x = fai (fa @source @source @tt) (yai @source @into x)
ha'ya = yai'ya
ha_'ya = yai'ya
ha__'ya = yai'ya
ha___'ya = yai'ya
ha____'ya = yai'ya
ha_____'ya = yai'ya
ha______'ya = yai'ya
ha_______'ya = yai'ya

yai'yoi, ha'yoi, ha_'yoi, ha__'yoi, ha___'yoi, ha____'yoi, ha_____'yoi, ha______'yoi, ha_______'yoi
 :: forall source into t i tt ii a o .
 Covariant Endo Semi Functor source (T'II'I tt ii) =>
 (forall e ee . Wrapper source (T'II'I tt e ee)) =>
 Contravariant Yoneda Functor source into (T'II'I t i) =>
 (forall e ee . Wrapper into (T'II'I t e ee)) =>
 Contravariant Endo Semi Functor (AR) (T'II'I into (t (tt a ii) i)) =>
 (forall e ee . Wrapper into (T'II'I source e ee)) =>
 (t (tt o ii) i) -> into (source (a) o) (t (tt a ii) i)
yai'yoi x = fai (foi @source @source @tt) (yai @source @into x)
ha'yoi = yai'yoi
ha_'yoi = yai'yoi
ha__'yoi = yai'yoi
ha___'yoi = yai'yoi
ha____'yoi = yai'yoi
ha_____'yoi = yai'yoi
ha______'yoi = yai'yoi
ha_______'yoi = yai'yoi

yai'yai, ha'ha, ha_'ha, ha__'ha, ha___'ha, ha____'ha, ha_____'ha, ha______'ha, ha_______'ha
 :: forall source into t i tt ii a o .
 Contravariant Endo Semi Functor source (T'II'I tt ii) =>
 (forall e ee . Wrapper source (T'II'I tt e ee)) =>
 Contravariant Yoneda Functor source into (T'II'I t i) =>
 (forall e ee . Wrapper into (T'II'I t e ee)) =>
 Contravariant Endo Semi Functor (AR) (T'II'I into (t (tt o ii) i)) =>
 (forall e ee . Wrapper into (T'II'I source e ee)) =>
 (t (tt a ii) i) -> into (source (a) o) (t (tt o ii) i)
yai'yai x = fai (fai @source @source @tt) (yai @source @into x)
ha'ha = yai'yai
ha_'ha = yai'yai
ha__'ha = yai'yai
ha___'ha = yai'yai
ha____'ha = yai'yai
ha_____'ha = yai'yai
ha______'ha = yai'yai
ha_______'ha = yai'yai

yai'yio, ha'ho, ha_'ho, ha__'ho, ha___'ho, ha____'ho, ha_____'ho, ha______'ho, ha_______'ho
 :: forall source into t i tt ii a o .
 Covariant Endo Semi Functor source (T'I'II tt ii) =>
 (forall e ee . Wrapper source (T'I'II tt e ee)) =>
 Contravariant Yoneda Functor source into (T'II'I t i) =>
 (forall e ee . Wrapper into (T'II'I t e ee)) =>
 Contravariant Endo Semi Functor (AR) (T'II'I into (t (tt ii (a)) i)) =>
 (forall e ee . Wrapper into (T'II'I source e ee)) =>
 (t (tt ii (o)) i) -> into (source (a) o) (t (tt ii (a)) i)
yai'yio x = fai (fio @source @source @tt) (yai @source @into x)
ha'ho = yai'yio
ha_'ho = yai'yio
ha__'ho = yai'yio
ha___'ho = yai'yio
ha____'ho = yai'yio
ha_____'ho = yai'yio
ha______'ho = yai'yio
ha_______'ho = yai'yio

yai'yia, ha'yia, ha_'yia, ha__'yia, ha___'yia, ha____'yia, ha_____'yia, ha______'yia, ha_______'yia
 :: forall source into t i tt ii a o .
 Contravariant Endo Semi Functor source (T'I'II tt ii) =>
 (forall e ee . Wrapper source (T'I'II tt e ee)) =>
 Contravariant Yoneda Functor source into (T'II'I t i) =>
 (forall e ee . Wrapper into (T'II'I t e ee)) =>
 Contravariant Endo Semi Functor (AR) (T'II'I into (t (tt ii (o)) i)) =>
 (forall e ee . Wrapper into (T'II'I source e ee)) =>
 (t (tt ii (a)) i) -> into (source (a) o) (t (tt ii (o)) i)
yai'yia x = fai (fia @source @source @tt) (yai @source @into x)
ha'yia = yai'yia
ha_'yia = yai'yia
ha__'yia = yai'yia
ha___'yia = yai'yia
ha____'yia = yai'yia
ha_____'yia = yai'yia
ha______'yia = yai'yia
ha_______'yia = yai'yia

yio'yo, ho'yo, ho_'yo, ho__'yo, ho___'yo, ho____'yo, ho_____'yo, ho______'yo, ho_______'yo
 :: forall source into t i tt a o .
 Covariant Endo Semi Functor source tt =>
 Covariant Yoneda Functor source into (T'I'II t i) =>
 (forall e ee . Wrapper into (T'I'II t e ee)) =>
 Contravariant Endo Semi Functor (AR) (T'II'I into (t i ((tt o)))) =>
 (forall e ee . Wrapper into (T'I'II source e ee)) =>
 (t i ((tt a))) -> into (source (a) o) (t i ((tt o)))
yio'yo x = fai (fo @source @source @tt) (yio @source @into x)
ho'yo = yio'yo
ho_'yo = yio'yo
ho__'yo = yio'yo
ho___'yo = yio'yo
ho____'yo = yio'yo
ho_____'yo = yio'yo
ho______'yo = yio'yo
ho_______'yo = yio'yo

yio'ya, ho'ya, ho_'ya, ho__'ya, ho___'ya, ho____'ya, ho_____'ya, ho______'ya, ho_______'ya
 :: forall source into t i tt a o .
 Contravariant Endo Semi Functor source tt =>
 Covariant Yoneda Functor source into (T'I'II t i) =>
 (forall e ee . Wrapper into (T'I'II t e ee)) =>
 Contravariant Endo Semi Functor (AR) (T'II'I into (t i ((tt a)))) =>
 (forall e ee . Wrapper into (T'I'II source e ee)) =>
 (t i ((tt o))) -> into (source (a) o) (t i ((tt a)))
yio'ya x = fai (fa @source @source @tt) (yio @source @into x)
ho'ya = yio'ya
ho_'ya = yio'ya
ho__'ya = yio'ya
ho___'ya = yio'ya
ho____'ya = yio'ya
ho_____'ya = yio'ya
ho______'ya = yio'ya
ho_______'ya = yio'ya

yio'yoi, ho'yoi, ho_'yoi, ho__'yoi, ho___'yoi, ho____'yoi, ho_____'yoi, ho______'yoi, ho_______'yoi
 :: forall source into t i tt ii a o .
 Covariant Endo Semi Functor source (T'II'I tt ii) =>
 (forall e ee . Wrapper source (T'II'I tt e ee)) =>
 Covariant Yoneda Functor source into (T'I'II t i) =>
 (forall e ee . Wrapper into (T'I'II t e ee)) =>
 Contravariant Endo Semi Functor (AR) (T'II'I into (t i ((tt o ii)))) =>
 (forall e ee . Wrapper into (T'I'II source e ee)) =>
 (t i ((tt a ii))) -> into (source (a) o) (t i ((tt o ii)))
yio'yoi x = fai (foi @source @source @tt) (yio @source @into x)
ho'yoi = yio'yoi
ho_'yoi = yio'yoi
ho__'yoi = yio'yoi
ho___'yoi = yio'yoi
ho____'yoi = yio'yoi
ho_____'yoi = yio'yoi
ho______'yoi = yio'yoi
ho_______'yoi = yio'yoi

yio'yai, ho'ha, ho_'ha, ho__'ha, ho___'ha, ho____'ha, ho_____'ha, ho______'ha, ho_______'ha
 :: forall source into t i tt ii a o .
 Contravariant Endo Semi Functor source (T'II'I tt ii) =>
 (forall e ee . Wrapper source (T'II'I tt e ee)) =>
 Covariant Yoneda Functor source into (T'I'II t i) =>
 (forall e ee . Wrapper into (T'I'II t e ee)) =>
 Contravariant Endo Semi Functor (AR) (T'II'I into (t i ((tt a ii)))) =>
 (forall e ee . Wrapper into (T'I'II source e ee)) =>
 (t i ((tt o ii))) -> into (source (a) o) (t i ((tt a ii)))
yio'yai x = fai (fai @source @source @tt) (yio @source @into x)
ho'ha = yio'yai
ho_'ha = yio'yai
ho__'ha = yio'yai
ho___'ha = yio'yai
ho____'ha = yio'yai
ho_____'ha = yio'yai
ho______'ha = yio'yai
ho_______'ha = yio'yai

yio'yio, ho'ho, ho_'ho, ho__'ho, ho___'ho, ho____'ho, ho_____'ho, ho______'ho, ho_______'ho
 :: forall source into t i tt ii a o .
 Covariant Endo Semi Functor source (T'I'II tt ii) =>
 (forall e ee . Wrapper source (T'I'II tt e ee)) =>
 Covariant Yoneda Functor source into (T'I'II t i) =>
 (forall e ee . Wrapper into (T'I'II t e ee)) =>
 Contravariant Endo Semi Functor (AR) (T'II'I into (t i ((tt ii (o))))) =>
 (forall e ee . Wrapper into (T'I'II source e ee)) =>
 (t i ((tt ii (a)))) -> into (source (a) o) (t i ((tt ii (o))))
yio'yio x = fai (fio @source @source @tt) (yio @source @into x)
ho'ho = yio'yio
ho_'ho = yio'yio
ho__'ho = yio'yio
ho___'ho = yio'yio
ho____'ho = yio'yio
ho_____'ho = yio'yio
ho______'ho = yio'yio
ho_______'ho = yio'yio

yio'yia, ho'yia, ho_'yia, ho__'yia, ho___'yia, ho____'yia, ho_____'yia, ho______'yia, ho_______'yia
 :: forall source into t i tt ii a o .
 Contravariant Endo Semi Functor source (T'I'II tt ii) =>
 (forall e ee . Wrapper source (T'I'II tt e ee)) =>
 Covariant Yoneda Functor source into (T'I'II t i) =>
 (forall e ee . Wrapper into (T'I'II t e ee)) =>
 Contravariant Endo Semi Functor (AR) (T'II'I into (t i ((tt ii (a))))) =>
 (forall e ee . Wrapper into (T'I'II source e ee)) =>
 (t i ((tt ii (o)))) -> into (source (a) o) (t i ((tt ii (a))))
yio'yia x = fai (fia @source @source @tt) (yio @source @into x)
ho'yia = yio'yia
ho_'yia = yio'yia
ho__'yia = yio'yia
ho___'yia = yio'yia
ho____'yia = yio'yia
ho_____'yia = yio'yia
ho______'yia = yio'yia
ho_______'yia = yio'yia

yia'yo
 :: forall source into t i tt a o .
 Covariant Endo Semi Functor source tt =>
 Contravariant Yoneda Functor source into (T'I'II t i) =>
 (forall e ee . Wrapper into (T'I'II t e ee)) =>
 Contravariant Endo Semi Functor (AR) (T'II'I into (t i ((tt a)))) =>
 (forall e ee . Wrapper into (T'II'I source e ee)) =>
 (t i ((tt o))) -> into (source (a) o) (t i ((tt a)))
yia'yo x = fai (fo @source @source @tt) (yia @source @into x)

yia'ya
 :: forall source into t i tt a o .
 Contravariant Endo Semi Functor source tt =>
 Contravariant Yoneda Functor source into (T'I'II t i) =>
 (forall e ee . Wrapper into (T'I'II t e ee)) =>
 Contravariant Endo Semi Functor (AR) (T'II'I into (t i ((tt o)))) =>
 (forall e ee . Wrapper into (T'II'I source e ee)) =>
 (t i ((tt a))) -> into (source (a) o) (t i ((tt o)))
yia'ya x = fai (fa @source @source @tt) (yia @source @into x)

yia'yoi
 :: forall source into t i tt ii a o .
 Covariant Endo Semi Functor source (T'II'I tt ii) =>
 (forall e ee . Wrapper source (T'II'I tt e ee)) =>
 Contravariant Yoneda Functor source into (T'I'II t i) =>
 (forall e ee . Wrapper into (T'I'II t e ee)) =>
 Contravariant Endo Semi Functor (AR) (T'II'I into (t i ((tt a ii)))) =>
 (forall e ee . Wrapper into (T'II'I source e ee)) =>
 (t i ((tt o ii))) -> into (source (a) o) (t i ((tt a ii)))
yia'yoi x = fai (foi @source @source @tt) (yia @source @into x)

yia'yai, yia'ha
 :: forall source into t i tt ii a o .
 Contravariant Endo Semi Functor source (T'II'I tt ii) =>
 (forall e ee . Wrapper source (T'II'I tt e ee)) =>
 Contravariant Yoneda Functor source into (T'I'II t i) =>
 (forall e ee . Wrapper into (T'I'II t e ee)) =>
 Contravariant Endo Semi Functor (AR) (T'II'I into (t i ((tt o ii)))) =>
 (forall e ee . Wrapper into (T'II'I source e ee)) =>
 (t i ((tt a ii))) -> into (source (a) o) (t i ((tt o ii)))
yia'yai x = fai (fai @source @source @tt) (yia @source @into x)
yia'ha = yia'yai

yia'yio, yia'ho
 :: forall source into t i tt ii a o .
 Covariant Endo Semi Functor source (T'I'II tt ii) =>
 (forall e ee . Wrapper source (T'I'II tt e ee)) =>
 Contravariant Yoneda Functor source into (T'I'II t i) =>
 (forall e ee . Wrapper into (T'I'II t e ee)) =>
 Contravariant Endo Semi Functor (AR) (T'II'I into (t i ((tt ii (a))))) =>
 (forall e ee . Wrapper into (T'II'I source e ee)) =>
 (t i ((tt ii (o)))) -> into (source (a) o) (t i ((tt ii (a))))
yia'yio x = fai (fio @source @source @tt) (yia @source @into x)
yia'ho = yia'yio

yia'yia
 :: forall source into t i tt ii a o .
 Contravariant Endo Semi Functor source (T'I'II tt ii) =>
 (forall e ee . Wrapper source (T'I'II tt e ee)) =>
 Contravariant Yoneda Functor source into (T'I'II t i) =>
 (forall e ee . Wrapper into (T'I'II t e ee)) =>
 Contravariant Endo Semi Functor (AR) (T'II'I into (t i ((tt ii (o))))) =>
 (forall e ee . Wrapper into (T'II'I source e ee)) =>
 (t i ((tt ii (a)))) -> into (source (a) o) (t i ((tt ii (o))))
yia'yia x = fai (fia @source @source @tt) (yia @source @into x)
