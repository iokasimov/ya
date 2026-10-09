{-# OPTIONS_GHC -fno-warn-orphans #-}
{-# LANGUAGE AllowAmbiguousTypes #-}
module Ya.Algebra.Mappings where

import Ya.Algebra.Abstract
import Ya.Algebra.Definition

instance
 ( Covariant Semi Functor source target t
 , forall e . Wrapper target (t `L` tt `T` ll `T` e)
 ) => Mapping T'I'II T'I'II source target (t `L` tt `T` ll) (t `L` tt `T` ll) where
 mapping = rewrap `identity` (rewrap `compose` map @T'I'II @T'I'II @source @target @t @t)

instance Mapping T'I'II T'I'II (AR) (AR) (T'I'II (AR) i) (T'I'II (AR) i) where
 mapping (T'I'II g) = T'I'II `identity` \(T'I'II f) -> T'I'II (\x -> g (f x))

instance Mapping T'II'I T'I'II (AR) (AR) (T'II'I (AR) i) (T'II'I (AR) i) where
 mapping (T'II'I g) = T'I'II `identity` \(T'II'I f) -> T'II'I (\x -> f (g x))

instance Category (AR) where
 identity = \x -> x

instance Mapping T'I'II T'I'II (AT) (AR) (T'I'II (AT) i) (T'I'II (AT) i) where
 mapping = rewrap `identity` \target -> rewrap `compose` rewrap `identity` \source x ->
  let These i i_origin = source x in
  let These ii ii_i = supertype target i in
  These ii (i_origin `compose` ii_i)

instance Mapping T'II'I T'I'II (AT) (AR) (T'II'I (AT) i) (T'II'I (AT) i) where
 mapping = rewrap `identity` \source -> rewrap `compose` rewrap `identity` \target x ->
  let These i i_origin = supertype source x in
  let These ii ii_i = target i in
  These ii (i_origin `compose` ii_i)

instance Category (AT) where
 identity = T'I'TT'II'T'II'I `identity` \x -> These x identity

instance Mapping T'I'II T'I'II (AR) (AR) (T'I'II (TR) e) (T'I'II (TR) e) where
 mapping = rewrap `identity` \source -> rewrap `compose` rewrap `identity` \f x ->
  i_ (map @T'I'II @T'I'II source) (f x)

instance Mapping T'I'II T'I'II (TR) (AR) (T'I'II (TR) i) (T'I'II (TR) i) where
 mapping = rewrap `identity` \(T'I'TT'II'I source)
  -> rewrap `compose` rewrap `identity` \origin i ->
   let These a ii = origin i in
   let These o _a = source a in
   These o ii

instance Mapping T'II'I T'I'II (TR) (AR) (T'II'I (TR) i) (T'II'I (TR) i) where
 mapping = rewrap `identity` \(T'I'TT'II'I source)
  -> rewrap `compose` rewrap `identity` \origin o ->
   let These a oo = source o in
   let These i _a = origin a in
   These i oo

instance Mapping T'I'II T'I'II (AR) (AR) (T'I'II (P) i) (T'I'II (P) i) where
 mapping = rewrap `identity` \source -> rewrap `identity` \case
  These e x -> These e (source x)

instance Mapping T'I'II T'I'II (AT) (AT) (T'I'II (P) i) (T'I'II (P) i) where
 mapping = rewrap `compose` rewrap `identity` \source (T'I'II (These e x)) ->
  let s = source x in These (T'I'II (These e (this s))) (map @T'I'II @T'I'II (that s))

instance Mapping T'I'II T'I'II (AR) (AR) (T'II'I (P) i) (T'II'I (P) i) where
 mapping = rewrap `identity` \source -> rewrap `identity` \case
  These x e -> These (source x) e

instance Mapping T'I'II T'I'II (AT) (AT) (T'II'I (P) i) (T'II'I (P) i) where
 mapping = rewrap `compose` rewrap `identity` \source (T'II'I (These x e)) ->
  let s = source x in These (T'II'I (These (this s) e)) (map @T'I'II @T'I'II (that s))

instance Mapping T'I'II T'I'II (AR) (AR) (T'I'II (S) i) (T'I'II (S) i) where
 mapping = rewrap `identity` \source -> rewrap `identity` \case
  That x -> That (source x)
  This e -> This e

instance Mapping T'I'II T'I'II (AT) (AT) (T'I'II (S) i) (T'I'II (S) i) where
 mapping = rewrap `identity` \(T'I'TT'II'T'II'I source) ->
  T'I'TT'II'T'II'I `identity` \case
   T'I'II (This i) -> These (T'I'II (This i)) (\_ -> T'I'II (This i))
   T'I'II (That x) -> These (T'I'II (That (this (source x)))) (map @T'I'II @T'I'II (that (source x)))

{- TODO:
instance Mapping T'I'II T'I'II (TR) (TR) (T'I'II (S) i) (T'I'II (S) i) where
-}

instance Mapping T'I'II T'I'II (AR) (AR) (T'II'I (S) i) (T'II'I (S) i) where
 mapping = rewrap `identity` \source -> rewrap `identity` \case
  This x -> This (source x)
  That e -> That e

instance Mapping T'I'II T'I'II (AT) (AT) (T'II'I (S) i) (T'II'I (S) i) where
 mapping = rewrap `identity` \(T'I'TT'II'T'II'I source) ->
  T'I'TT'II'T'II'I `identity` \case
   T'II'I (That i) -> These (T'II'I (That i)) (\_ -> T'II'I (That i))
   T'II'I (This x) -> These (T'II'I (This (this (source x)))) (map @T'I'II @T'I'II (that (source x)))

instance
 ( forall i . Covariant Semi Functor source target (T'I'II u i `T'TT'I` t)
 , forall i . Covariant Endo Semi Functor source (T'I'II u i `T'TT'I` t)
 , forall i . Covariant Endo Semi Functor source (T'II'I u (t i))
 , forall i . Covariant Semi Functor source target (T'II'I u (t i))
 , forall e . Wrapper source (F'T'I'TT (T'I'II u) t e)
 , forall e . Wrapper target (F'T'I'TT (T'I'II u) t e)
 , forall i . Wrapper source (Recursive (T'I'II u i `T'TT'I` t))
 , forall i . Wrapper target (Recursive (T'I'II u i `T'TT'I` t))
 , forall i ii . Wrapper source (T'II'I u i ii)
 , forall i ii . Wrapper target (T'II'I u i ii)
 , forall i ii . Wrapper source (T'I'II u i ii)
 , forall i ii . Wrapper target (T'I'II u i ii)
 , forall i ii . Wrapper source ((T'I'II u i `T'TT'I` t) ii)
 , forall i ii . Wrapper target ((T'I'II u i `T'TT'I` t) ii)
 ) => Mapping T'I'II T'I'II source target (F'T'I'TT (T'I'II u) t) (F'T'I'TT (T'I'II u) t) where
 mapping = rewrap `identity` \source -> rewrap `compose` rewrap `identity`
  ((rewrap `compose` rewrap) (wrapped (map @T'I'II @T'I'II @_ @_ @(T'II'I u (t _)) @(T'II'I u (t _)) source))
  `compose` map @T'I'II @T'I'II @source @target @(T'I'II u _ `T'TT'I` t) @(T'I'II u _ `T'TT'I` t)
   (wrapped (map @T'I'II @T'I'II @source @_ @(F'T'I'TT (T'I'II u) t) @(F'T'I'TT (T'I'II u) t) source))
  )

instance
 ( forall i . Covariant Semi Functor source target (T'II'I u i `T'TT'I` t)
 , forall i . Covariant Endo Semi Functor source (T'II'I u i `T'TT'I` t)
 , forall i . Covariant Endo Semi Functor source (T'I'II u (t i))
 , forall i . Covariant Semi Functor source target (T'I'II u (t i))
 , forall e . Wrapper source (F'T'I'TT (T'II'I u) t e)
 , forall e . Wrapper target (F'T'I'TT (T'II'I u) t e)
 , forall i . Wrapper source (Recursive (T'II'I u i `T'TT'I` t))
 , forall i . Wrapper target (Recursive (T'II'I u i `T'TT'I` t))
 , forall i ii . Wrapper source (T'II'I u i ii)
 , forall i ii . Wrapper target (T'II'I u i ii)
 , forall i ii . Wrapper source (T'I'II u i ii)
 , forall i ii . Wrapper target (T'I'II u i ii)
 , forall i ii . Wrapper source ((T'II'I u i `T'TT'I` t) ii)
 , forall i ii . Wrapper target ((T'II'I u i `T'TT'I` t) ii)
 ) => Mapping T'I'II T'I'II source target (F'T'I'TT (T'II'I u) t) (F'T'I'TT (T'II'I u) t) where
 mapping = rewrap `identity` \source -> rewrap `compose` rewrap `identity`
  ((rewrap `compose` rewrap) (wrapped (map @T'I'II @T'I'II @_ @_ @(T'I'II u (t _)) @(T'I'II u (t _)) source))
  `compose` map @T'I'II @T'I'II @source @target @(T'II'I u _ `T'TT'I` t) @(T'II'I u _ `T'TT'I` t)
   (wrapped (map @T'I'II @T'I'II @source @_ @(F'T'I'TT (T'II'I u) t) @(F'T'I'TT (T'II'I u) t) source))
  )
