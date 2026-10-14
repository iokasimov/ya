{-# OPTIONS_GHC -fno-warn-orphans #-}
{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE UndecidableInstances #-}
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

instance Mapping T'I'II T'I'II (AR) (AR) (T'I'I (S)) (T'I'I (S)) where
 mapping = rewrap `identity` \source -> rewrap `identity` \case
  This x -> This (source x)
  That x -> That (source x)

instance Mapping T'I'II T'I'II (AT) (AT) (T'I'I (S)) (T'I'I (S)) where
 mapping = rewrap `identity` \(T'I'TT'II'T'II'I source) ->
  T'I'TT'II'T'II'I `identity` \case
   T'I'I (This x) -> These (T'I'I (This (this (source x)))) (map @T'I'II @T'I'II (that (source x)))
   T'I'I (That x) -> These (T'I'I (That (this (source x)))) (map @T'I'II @T'I'II (that (source x)))

instance Mapping T'I'II T'I'II (AR) (AR) (T'II'I (W) i) (T'II'I (W) i) where
 mapping = rewrap `identity` \source -> rewrap `compose` rewrap `identity` \case
  This (This x) -> This (This (source x))
  That (These x i) -> That (These (source x) i)

instance Mapping T'I'II T'I'II (AR) (AR) (T'I'II (W) i) (T'I'II (W) i) where
 mapping = rewrap `identity` \source -> rewrap `compose` rewrap `identity` \case
  This (That x) -> This (That (source x))
  That (These i x) -> That (These i (source x))

instance
 ( Covariant Semi Functor source target tt
 , Covariant Endo Semi Functor target t
 , forall e . Wrapper target (t `T'TT'I` tt `T'I_` e)
 ) => Mapping T'I'II T'I'II source target (t `T'TT'I` tt) (t `T'TT'I` tt) where
 mapping = rewrap `identity` \source -> subtype @target `compose` (map @T'I'II @T'I'II @target @target `compose` map @T'I'II @T'I'II @source @target) source `compose` supertype @target

instance
 ( Covariant Semi Functor source target t
 , Covariant Endo Semi Functor target tt
 , forall e . Wrapper target (t `TT'T'I` tt `T'I_` e)
 ) => Mapping T'I'II T'I'II source target (t `TT'T'I` tt) (t `TT'T'I` tt) where
 mapping = rewrap `identity` \source -> subtype @target `compose` (map @T'I'II @T'I'II @target @target `compose` map @T'I'II @T'I'II @source @target) source `compose` supertype @target

-- TODO: generalise up to any categories
instance
 ( Covariant Endo Semi Functor (AR) t
 , Covariant Endo Semi Functor (AR) tt
 , Covariant Endo Semi Functor (AR) ttt
 , Covariant Transformation Functor (AR) (AR) (t `T'TT'I` ttt `L` ttt `T` lll `L` t `T` ll) (t `TT'T'I` ttt)
 , Covariant Transformation Functor (AR) (AR) (tt `T'TT'I` ttt `L` ttt `T` lll `L` tt `T` ll) (tt `TT'T'I` ttt)
 ) => Mapping T'I'II T'I'II (AR) (AR) ((t `T'TT'I` tt) `T'TT'I` ttt `L` ttt `T` lll `L` (t `T'TT'I` tt) `T` ll) ((t `T'TT'I` tt) `TT'T'I` ttt) where
 mapping = rewrap `identity` \source -> rewrap (
  map @T'I'II @T'I'II @(AR) @(AR) @ttt @ttt (subtype @(AR) @(t `T'TT'I` tt `T'I_` _))
  `compose` wrapped (map @T'I'II @T'I'II @(AR) @(AR) @(t `T'TT'I` ttt `L` ttt `T` lll `L` t `T` ll) @(t `TT'T'I` ttt) identity)
  `compose` map @T'I'II @T'I'II @(AR) @(AR) @t @t
   (subtype @(AR) @(ttt `L` ttt `T` lll `L` t `T` ll `T` _)
   `compose` subtype @(AR) @(ttt `L` ttt `T` lll `T` _)
   `compose` wrapped (map @T'I'II @T'I'II @(AR) @(AR) @(tt `T'TT'I` ttt `L` ttt `T` lll `L` tt `T` ll) @(tt `TT'T'I` ttt) source)
   `compose` map @T'I'II @T'I'II @(AR) @(AR) @tt @tt
    (rewrap @(AR) @(ttt `L` ttt `T` lll `L` (t `T'TT'I` tt) `T` ll `T` _) @(ttt `L` ttt `T` lll `L` tt `T` ll `T` _) identity)
   )
  `compose` supertype)

instance
 ( Covariant Semi Functor source target t
 , forall ee . Covariant Endo Semi Functor target (T'I'II u ee)
 , forall ee . Wrapper target (T'I'II (T'I'TT'II u t) e ee)
 , forall ee . Wrapper target (T'I'TT'II u t e ee)
 , forall ee . Wrapper target (T'I'II u e (t ee))
 ) => Mapping T'I'II T'I'II source target (T'I'II (T'I'TT'II u t) e) (T'I'II (T'I'TT'II u t) e) where
 mapping = rewrap `identity` \source ->
  subtype @target @(T'I'II _ _ _)
  `compose` subtype @target @(T'I'TT'II _ _ _ _)
  `compose` supertype @target @(T'I'II _ _ _)
  `compose` map @T'I'II @T'I'II @target @target (map @T'I'II @T'I'II @source @target source)
  `compose` subtype @target @(T'I'II _ _ _)
  `compose` supertype @target @(T'I'TT'II _ _ _ _)
  `compose` supertype @target @(T'I'II _ _ _)

instance
 ( forall ee . Covariant Semi Functor source target (T'II'I u ee)
 , forall ee . Wrapper target (T'II'I (T'I'TT'II u t) e ee)
 , forall ee . Wrapper target (T'I'TT'II u t ee e)
 , forall ee . Wrapper target (T'II'I u (t e) ee)
 ) => Mapping T'I'II T'I'II source target (T'II'I (T'I'TT'II u t) e) (T'II'I (T'I'TT'II u t) e) where
 mapping = rewrap `identity` \source ->
  subtype @target @(T'II'I _ _ _)
  `compose` subtype @target @(T'I'TT'II _ _ _ _)
  `compose` supertype @target @(T'II'I _ _ _)
  `compose` map @T'I'II @T'I'II @source @target source
  `compose` subtype @target @(T'II'I _ _ _)
  `compose` supertype @target @(T'I'TT'II _ _ _ _)
  `compose` supertype @target @(T'II'I _ _ _)

instance
 ( Covariant Semi Functor source target h
 , Covariant Endo Semi Functor target tt
 , Covariant Endo Semi Functor target t
 , forall e . Wrapper target (T'TTT'TT'I t h tt e)
 ) => Mapping T'I'II T'I'II source target (T'TTT'TT'I t h tt) (T'TTT'TT'I t h tt) where
 mapping = rewrap `identity` \source -> subtype @target
  `compose` (map @T'I'II @T'I'II @target @target
   `compose` map @T'I'II @T'I'II @target @target
   `compose` map @T'I'II @T'I'II @source @target
   ) source
  `compose` supertype @target

instance
 ( forall e . Covariant Endo Semi Functor target (T'I'II u (t e))
 , forall e . Covariant Endo Semi Functor target (T'II'I u (tt e))
 , Covariant Semi Functor source target tt
 , Covariant Semi Functor source target t
 , forall e . Wrapper target (T'TT'I'TTT'I u t tt e)
 , forall e ee . Wrapper target (T'I'II u (t e) (tt ee))
 , forall e ee . Wrapper target (T'II'I u (tt e) (t ee))
 ) => Mapping T'I'II T'I'II source target (T'TT'I'TTT'I u t tt) (T'TT'I'TTT'I u t tt) where
 mapping = rewrap `identity` \source -> rewrap (
  i_ (map @T'I'II @T'I'II @target @target `compose` map @T'I'II @T'I'II @source @target @t @t `identity`source) `compose`
  _i (map @T'I'II @T'I'II @target @target `compose` map @T'I'II @T'I'II @source @target @tt @tt `identity`source))

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
