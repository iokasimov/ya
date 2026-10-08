{-# OPTIONS_GHC -fno-warn-orphans #-}
{-# LANGUAGE AllowAmbiguousTypes #-}
module Ya.Algebra.Components where

import Ya.Algebra.Abstract
import Ya.Algebra.Definition
import Ya.Algebra.Mappings ()

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
