{-# OPTIONS_GHC -fno-warn-orphans #-}
{-# LANGUAGE UndecidableInstances #-}
module Ya.Interface.Instances where

import Ya.Semantics
import Ya.Operators

instance
 ( Covariant Endo Semi Functor (AR) t
 , Covariant Endo Semi Functor (AR) tt
 , Component (AR) (t `T'TT'I` tt `L` tt `T` ll `L` t `T` Void) (t `TT'T'I` tt)
 , forall e ee . Component (AR) ((T'I'II (AR) ((P) e ee) `P'T'I'TT'I` T'I' ((P) (tt e) (tt ee))) `L` T'I'I (P) `T` ll `L` tt `T` (Void)) tt
 ) => Component (AR) (F'T'I'TT (T'II'I P) t `T'TT'I` tt `L` tt `T` ll `L` F'T'I'TT (T'II'I P) t `T` (Void `P` Void)) (F'T'I'TT (T'II'I P) t `TT'T'I` tt) where
 component = rewrap `identity` \(F'T'I'TT (Recursive (T'TT'I (T'II'I (These xs x))))) ->
  wrapped (component @(AR) @(t `T'TT'I` tt `L` tt `T` ll `L` t `T` (Void)) @(t `TT'T'I` tt))
  ((xs
   `yo` subtype @(AR) @(F'T'I'TT _ _ _)
   `ho` wrapped (component @(AR) @(F'T'I'TT (T'II'I P) t `T'TT'I` tt `L` tt `T` ll `L` F'T'I'TT (T'II'I P) t `T` (Void `P` Void)) @(F'T'I'TT (T'II'I P) t `TT'T'I` tt))
   `ho` subtype @(AR) @(tt `L` tt `T` ll `T` _)
   `ho` subtype @(AR) @(tt `L` tt `T` ll `L` t `T` (Void) `T` _)
  ) `yo'yo` supertype @(AR) @(F'T'I'TT _ _ _))
  `These` supertype (supertype x)
  `yo'dc'yo'nt'yo` boundtype @(AR) @(I `L` T'I'I (P) `T` ll `L` tt `T` (Void) `T` _)

instance
 ( Covariant Endo Semi Functor (AR) t
 , Covariant Endo Semi Functor (AR) tt
 , Component (AR) (t `T'TT'I` tt `L` tt `T` ll `L` t `T` Void) (t `TT'T'I` tt)
 , forall e ee . Component (AR) ((T'I'II (AR) ((P) e ee) `P'T'I'TT'I` T'I' ((P) (tt e) (tt ee))) `L` T'I'I (P) `T` ll `L` tt `T` (Void)) tt
 ) => Component (AR) (F'T'I'TT (T'II'I P) t `T'TT'I` tt `L` tt `T` ll `L` F'T'I'TT (T'II'I P) t `T` (Void)) (F'T'I'TT (T'II'I P) t `TT'T'I` tt) where
 component = rewrap `identity` \(F'T'I'TT (Recursive (T'TT'I (T'II'I (These xs x))))) ->
  supertype (supertype x) `These`
  wrapped (component @(AR) @(t `T'TT'I` tt `L` tt `T` ll `L` t `T` (Void)) @(t `TT'T'I` tt))
  ((xs
   `yo` subtype @(AR) @(F'T'I'TT _ _ _)
   `ho` wrapped (component @(AR) @(F'T'I'TT (T'II'I P) t `T'TT'I` tt `L` tt `T` ll `L` F'T'I'TT (T'II'I P) t `T` (Void)) @(F'T'I'TT (T'II'I P) t `TT'T'I` tt))
   `ho` subtype @(AR) @(tt `L` tt `T` ll `T` _)
   `ho` subtype @(AR) @(tt `L` tt `T` ll `L` t `T` (Void) `T` _)
  ) `yo'yo` supertype @(AR) @(F'T'I'TT _ _ _))
  `yo'dc'yo'nt'yo` boundtype @(AR) @(I `L` T'I'I (P) `T` ll `L` tt `T` (Void) `T` _) `compose` (\(These i ii) -> These ii i)

-- instance
 -- ( Mapping T'I'II T'I'II (AR) (AR) (T'I'II (AR) i `L` (Maybe `T'TT'I` F'T'I'TT (T'II'I P) Maybe) `T` (Void `P` Void)) (Maybe `T'TT'I` F'T'I'TT (T'II'I P) Maybe)
 -- ) => Mapping T'I'II T'I'II (AR) (AR) (T'I'II (AR) (i `S` Unit) `L` (Maybe `T'TT'I` F'T'I'TT (T'II'I P) Maybe) `T` (Void)) (Maybe `T'TT'I` F'T'I'TT (T'II'I P) Maybe) where
 -- mapping = rewrap `identity` \source (Label (T'I'II f)) ->
  -- that (source `ha` f `ha` This `ho'nt'yo` Stack @List `yokl_` Forth `ha` Apply `ha` State `ha___` Event `ha` Push `ho__'ha` Scope `ha'nt'ha` within `ha` Fresh `bt'ha'nt___'ha` source `ha` f `ha` That `ho'nt'yo` Stack)
