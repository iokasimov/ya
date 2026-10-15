{-# OPTIONS_GHC -fno-warn-orphans #-}
{-# LANGUAGE AllowAmbiguousTypes #-}
module Ya.Algebra.Components where

import Ya.Algebra.Abstract
import Ya.Algebra.Definition
import Ya.Algebra.Mappings ()
import Ya.Operators.Mappings

instance Component (AR) (T'I'II (AT) i) (T'I'II (AR) i) where
 component = rewrap `identity` \origin -> this `compose` supertype origin

instance Component (AR) (T'II'I (AT) i) (T'II'I (AR) i) where
 component = rewrap `identity` \origin -> this `compose` supertype origin

instance Component (AR) (T'I'II (P) i `L` T'I'II (AR) Unit `T` (Void)) (T'I'II (AR) Unit) where
 component = rewrap `identity` \(T'I'II (These _ x)) _ -> x

instance Component (AR) (T'II'I (P) i `L` T'I'II (AR) Unit `T` (Void)) (T'I'II (AR) Unit) where
 component = rewrap `identity` \(T'II'I (These x _)) _ -> x

instance Component (AR) (T'I'I (P) `L` T'I'II (AR) (Unit `S` Unit) `T` (Void)) (T'I'II (AR) (Unit `S` Unit)) where
 component = rewrap `identity` \(T'I'I (These x xx)) -> \case { This _ -> x; That _ -> xx }

instance Component (AR) (T'I'II (AR) (Unit `S` Unit) `L` T'I'I (P) `T` (Void)) (T'I'I (P)) where
 component = rewrap `identity` \(T'I'II x) -> These (x (This Unit)) (x (That Unit))

instance Component (AR) (T'I'II (AR) Unit `L` T'I'II (S) i `T` (Void)) (T'I'II (S) i) where
 component = rewrap `identity` \(T'I'II f) -> That (f Unit)

instance Component (AR) (T'I'II (AR) Unit `L` T'II'I (S) i `T` (Void)) (T'II'I (S) i) where
 component = rewrap `identity` \(T'I'II f) -> This (f Unit)

instance Component (AR) (T'I'II (AR) Void `L` T'I'II (S) Unit `T` (Void)) (T'I'II (S) Unit) where
 component = rewrap `identity` \_ -> This Unit

instance Component (AR) (T'I'I (S) `L` T'I'II (AR) Unit `T` (Void)) (T'I'II (AR) Unit) where
 component = rewrap `identity` \(T'I'I x) -> case x of
  This i -> \_ -> i
  That i -> \_ -> i

instance Component (AR) (T'I'II (S) i `T'TT'I` T'I'II (S) i `L` T'I'II (S) i `T` (Void)) (T'I'II (S) i) where
 component = rewrap `identity` \case
  T'I'II (This x) -> This x
  T'I'II (That (Label (T'I'II (This x)))) -> This x
  T'I'II (That (Label (T'I'II (That x)))) -> That x

instance Component (AR) (T'II'I (S) i `T'TT'I` T'II'I (S) i `L` T'II'I (S) i `T` (Void)) (T'II'I (S) i) where
 component = rewrap `identity` \case
  T'II'I (That x) -> That x
  T'II'I (This (Label (T'II'I (That x)))) -> That x
  T'II'I (This (Label (T'II'I (This x)))) -> This x

-- TODO: `Match` doesn't fit here
instance
 ( forall e . Wrapper target (I e)
 , forall e . Wrapper target (t `L` t `T` l `L` I `T` ll `T` e)
 , forall e . Wrapper target (t `L` t `T` l `T` e)
 , forall e . Wrapper target (I `TT'T'I` t `T'I_` e)
 , forall e . Wrapper target (I `T'TT'I` t `L` t `T` l `L` I `T` ll `T'I_` e)
 , Covariant Endo Semi Functor target t
 ) => Mapping T'I'II T'I'II target target (I `T'TT'I` t `L` t `T` l `L` I `T` ll) (I `TT'T'I` t) where
 mapping = rewrap `identity` \source -> rewrap (
  map @T'I'II @T'I'II @target @target (subtype @target @(I _) `compose` source)
   `compose` supertype @target @(t `L` t `T` l `T` _)
   `compose` supertype @target @(t `L` t `T` l `L` I `T` ll `T` _)
   `compose` supertype @target @(I _))

instance Covariant Endo Semi Functor (AR) tt =>
 Component (AR) (T'I'II (P) i `T'TT'I` tt `L` tt `T` (Void) `L` T'I'II (P) i `T` (Void)) (T'I'II (P) i `TT'T'I` tt) where
 component = rewrap `identity` \(T'I'II (These i x)) -> T'I'II `compose` (i `These`) `fo` supertype (supertype x)

instance Covariant Endo Semi Functor (AR) tt =>
 Component (AR) (T'II'I (P) i `T'TT'I` tt `L` tt `T` (Void) `L` T'II'I (P) i `T` (Void)) (T'II'I (P) i `TT'T'I` tt) where
 component = rewrap `identity` \(T'II'I (These x i)) -> T'II'I `compose` (`These` i) `fo` supertype (supertype x)

instance
 ( Covariant Endo Semi Functor (AR) tt
 , Component (AR) (T'I'II (AR) Unit `L` tt `T` (Void)) tt
 ) => Component (AR) (T'I'II (S) i `T'TT'I` tt `L` tt `T` (Void) `L` T'I'II (S) i `T` (Void)) (T'I'II (S) i `TT'T'I` tt) where
 component = rewrap `identity` \case
  T'I'II (This x) -> component @(AR) @(T'I'II (AR) Unit `L` tt `T` (Void)) (Label (T'I'II (\_ -> T'I'II (This x))))
  T'I'II (That x) -> T'I'II `compose` That `fo` supertype (supertype x)

instance
 ( Covariant Endo Semi Functor (AR) tt
 , Component (AR) (T'I'II (AR) Unit `L` tt `T` (Void)) tt
 ) => Component (AR) (T'II'I (S) i `T'TT'I` tt `L` tt `T` (Void) `L` T'II'I (S) i `T` (Void)) (T'II'I (S) i `TT'T'I` tt) where
 component = rewrap `identity` \case
  -- T'II'I (This x) -> T'II'I `compose` This `fo` supertype (supertype x)
  T'II'I (That x) -> component @(AR) @(T'I'II (AR) Unit `L` tt `T` (Void)) (Label (T'I'II (\_ -> T'II'I (That x))))
