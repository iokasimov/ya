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

instance Component (AR) (T'I'II (AR) Unit `L` T'I'II (S) i `T` (Void)) (T'I'II (S) i) where
 component = rewrap `identity` \(T'I'II f) -> That (f Unit)

instance Component (AR) (T'I'II (AR) Unit `L` T'II'I (S) i `T` (Void)) (T'II'I (S) i) where
 component = rewrap `identity` \(T'I'II f) -> This (f Unit)

instance Component (AR) (T'I'II (AR) Void `L` T'I'II (S) Unit `T` (Void)) (T'I'II (S) Unit) where
 component = rewrap `identity` \_ -> This Unit

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
