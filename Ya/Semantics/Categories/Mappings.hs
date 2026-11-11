{-# OPTIONS_GHC -fno-warn-orphans #-}
{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE UndecidableInstances #-}
module Ya.Semantics.Categories.Mappings where

import Ya.Semantics.Structures
import Ya.Semantics.Denotation

instance Mapping T'I'II (AR) (AR) (T'I'II (AR) i) where
 mapping ~(T'I'II source) ~(T'I'II x) = T'I'II (\i -> source (x i))

instance Mapping T'I'II (AT) (AR) (T'I'II (AR) i) where
 mapping ~(T'I'II source) ~(T'I'II x) = T'I'II (\i -> this (supertype source (x i)))

instance Mapping T'II'I (AR) (AR) (T'II'I (AR) i) where
 mapping ~(T'II'I source) ~(T'II'I x) = T'II'I (\i -> x (source i))

instance Mapping T'II'I (AT) (AR) (T'II'I (AR) i) where
 mapping ~(T'II'I source) ~(T'II'I x) = T'II'I (\i -> x (this (supertype source i)))

instance Category (AR) where
 identity = \i -> i

instance Mapping T'I'II (AT) (AR) (T'I'II (AT) i) where
 mapping ~(T'I'II source) = rewrap `compose` rewrap `identity` \x i ->
  let These iii iiii = x i in
  let These ii iiiii = supertype source iii in
  These ii (iiii `compose` iiiii)

instance Mapping T'II'I (AT) (AR) (T'II'I (AT) i) where
 mapping ~(T'II'I source) = rewrap `compose` rewrap `identity` \x i ->
  let These iii iiii = supertype source i in
  let These ii iiiii = x iii in
  These ii (iiii `compose` iiiii)

instance Mapping T'I'II (AR) (AR) (T'I'II (TR) i) where
 mapping ~(T'I'II source) = rewrap `compose` rewrap `identity` \x i ->
  wrapped (map @T'I'II @(AR) @(AR) @(T'II'I (P) i) source) (x i)

{-
instance Mapping T'II'I T'I'II (AT) (AR) (T'II'I (TR) i) (T'II'I (TR) i) where
 mapping = rewrap `identity` \source -> rewrap `compose` rewrap `identity` \f x ->
  let These a ao = supertype source x in
  let These i aa = f a in
  These i (ao aa)
-}

instance (Semicategory target, forall e . Wrapper target (I e))
 => Mapping T'I'II target target I where
 mapping ~(T'I'II source) = rewrap source

instance Mapping T'I'II (AR) (AR) (T'I'II (P) i) where
 mapping ~(T'I'II source) = rewrap `identity` \case
  These i ii -> These i (source ii)

instance Mapping T'I'II (AT) (AT) (T'I'II (P) i) where
 mapping ~(T'I'II ~(T'I'TT'II'T'II'I source)) = rewrap `compose` T'I'TT'II'T'II'I `identity` \case
  These i ii -> let x = source ii in These (These i (this x)) (wrapped (map @T'I'II @(AR) @(AR) @(T'I'II (P) _) (that x)))

instance Mapping T'I'II (AR) (AR) (T'II'I (P) i) where
 mapping ~(T'I'II source) = rewrap `identity` \case
  These i ii -> These (source i) ii

instance Mapping T'I'II (AT) (AT) (T'II'I (P) i) where
 mapping ~(T'I'II ~(T'I'TT'II'T'II'I source)) = rewrap `compose` T'I'TT'II'T'II'I `identity` \case
  These i ii -> let x = source i in These (These (this x) ii) (wrapped (map @T'I'II @(AR) @(AR) @(T'II'I (P) _) (that x)))

instance Mapping T'I'II (AR) (AR) (T'I'I (P)) where
 mapping ~(T'I'II source) = rewrap `identity` \case
  These i ii -> These (source i) (source ii)

instance Mapping T'I'II (AR) (AR) (T'I'II (S) i) where
 mapping ~(T'I'II source) = rewrap `identity` \case
  That ii -> That (source ii)
  This i -> This i

instance Mapping T'I'II (AT) (AT) (T'I'II (S) i) where
 mapping ~(T'I'II ~(T'I'TT'II'T'II'I source)) = rewrap `compose` T'I'TT'II'T'II'I `identity` \case
  That ii -> These (That (this (source ii))) (wrapped (map @T'I'II @(AR) @(AR) @(T'I'II (S) _) (that (source ii))))
  This i -> These (This i) (\_ -> This i)

instance Mapping T'I'II (AR) (AR) (T'II'I (S) i) where
 mapping ~(T'I'II source) = rewrap `identity` \case
  This i -> This (source i)
  That ii -> That ii

instance Mapping T'I'II (AT) (AT) (T'II'I (S) i) where
 mapping ~(T'I'II ~(T'I'TT'II'T'II'I source)) = rewrap `compose` T'I'TT'II'T'II'I `identity` \case
  That i -> These (That i) (\_ -> That i)
  This ii -> These (This (this (source ii))) (wrapped (map @T'I'II @(AR) @(AR) @(T'II'I (S) _) (that (source ii))))

instance Mapping T'I'II (AR) (AR) (T'I'I (S)) where
 mapping ~(T'I'II source) = rewrap `identity` \case
  This i -> This (source i)
  That ii -> That (source ii)

instance Mapping T'I'II (AT) (AT) (T'I'I (S)) where
 mapping ~(T'I'II ~(T'I'TT'II'T'II'I source)) = rewrap `compose` T'I'TT'II'T'II'I `identity` \case
   This x -> These (This (this (source x))) (wrapped (map @T'I'II @(AR) @(AR) @(T'I'I (S)) (that (source x))))
   That x -> These (That (this (source x))) (wrapped (map @T'I'II @(AR) @(AR) @(T'I'I (S)) (that (source x))))

instance Mapping T'I'II (AR) (AR) (T'II'I (W) i) where
 mapping ~(T'I'II source) = rewrap `compose` rewrap `identity` \case
  This (This x) -> This (This (source x))
  That (These x i) -> That (These (source x) i)

instance Mapping T'I'II (AR) (AR) (T'I'II (W) i) where
 mapping ~(T'I'II source) = rewrap `compose` rewrap `identity` \case
  This (That x) -> This (That (source x))
  That (These i x) -> That (These i (source x))

instance
 ( Covariant Semi Functor source target t
 , forall e . Wrapper target (t `L` tt `T` ll `T` e)
 ) => Mapping T'I'II source target (t `L` tt `T` ll) where
 mapping = rewrap `compose` map @T'I'II @source @target @t `compose` supertype

instance
 ( Covariant Semi Functor source target tt
 , Covariant Endo Semi Functor target t
 , forall e . Wrapper target (t `T'TT'I` tt `T'I_` e)
 ) => Mapping T'I'II source target (T'TT'I t tt) where
 mapping ~(T'I'II source) = rewrap `identity` (map @T'I'II @target @target `compose` map @T'I'II @source @target) source

instance
 ( Covariant Semi Functor source target t
 , Covariant Endo Semi Functor target tt
 , forall e . Wrapper target (t `TT'T'I` tt `T'I_` e)
 ) => Mapping T'I'II source target (TT'T'I t tt) where
 mapping ~(T'I'II source) = rewrap `identity` (map @T'I'II @target @target `compose` map @T'I'II @source @target) source

instance
 ( forall i . Covariant Semi Functor source target (T'I'II tt i `T'TT'I` t)
 , forall i . Covariant Endo Semi Functor source (T'I'II tt i `T'TT'I` t)
 , forall i . Covariant Endo Semi Functor source (T'II'I tt (t i))
 , forall i . Covariant Semi Functor source target (T'II'I tt (t i))
 , forall e . Wrapper source (F'T'I'TT (T'I'II tt) t e)
 , forall e . Wrapper target (F'T'I'TT (T'I'II tt) t e)
 , forall i . Wrapper source (Recursive (T'I'II tt i `T'TT'I` t))
 , forall i . Wrapper target (Recursive (T'I'II tt i `T'TT'I` t))
 , forall i ii . Wrapper source (T'II'I tt i ii)
 , forall i ii . Wrapper target (T'II'I tt i ii)
 , forall i ii . Wrapper source (T'I'II tt i ii)
 , forall i ii . Wrapper target (T'I'II tt i ii)
 , forall i ii . Wrapper source ((T'I'II tt i `T'TT'I` t) ii)
 , forall i ii . Wrapper target ((T'I'II tt i `T'TT'I` t) ii)
 ) => Mapping T'I'II source target (F'T'I'TT (T'I'II tt) t) where
 mapping ~(T'I'II source) = rewrap `compose` rewrap `identity`
  ((rewrap `compose` rewrap) (wrapped (map @T'I'II @_ @_ @(T'II'I tt (t _)) source))
  `compose` map @T'I'II @source @target @(T'I'II tt _ `T'TT'I` t)
   (wrapped (map @T'I'II @source @_ @(F'T'I'TT (T'I'II tt) t) source))
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
 ) => Mapping T'I'II source target (F'T'I'TT (T'II'I u) t) where
 mapping ~(T'I'II source) = rewrap `compose` rewrap `identity`
  ((rewrap `compose` rewrap) (wrapped (map @T'I'II @_ @_ @(T'I'II u (t _)) source))
  `compose` map @T'I'II @source @target @(T'II'I u _ `T'TT'I` t)
   (wrapped (map @T'I'II @source @_ @(F'T'I'TT (T'II'I u) t) source))
  )
