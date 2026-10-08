{-# OPTIONS_GHC -fno-warn-orphans #-}
{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE UndecidableInstances #-}
module Ya.Algebra.Instances where

import Ya.Algebra.Abstract
import Ya.Algebra.Definition
import Ya.Algebra.Mappings

instance Component (AR) (T'I'II (AT) i) (T'I'II (AR) i) where
 component = rewrap `identity` \origin -> this `compose` supertype origin

instance Component (AR) (T'II'I (AT) i) (T'II'I (AR) i) where
 component = rewrap `identity` \origin -> this `compose` supertype origin

-- TODO: Mapping T'II'I T'I'II (AT) (AR) (T'II'I (TR) i) (T'II'I (TR) i) where

{-
instance Mapping T'II'I T'I'II (AT) (AR) (T'II'I (TR) i) (T'II'I (AT) i) where
 mapping = rewrap `identity` \source -> rewrap `compose` rewrap `identity` \origin x ->
  let These a ao = supertype source x in
  let These i aa = origin a in
  These i (\_ -> ao aa)
-}

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

{-
instance Component (AR) (T'I'II (P) i `L` T'I'II (AR) Unit `T` (Void)) (T'I'II (AR) Unit) where
 component = rewrap `identity` \(T'I'II (These _ x)) _ -> x

instance Component (AR) (T'II'I (P) i `L` T'I'II (AR) Unit `T` (Void)) (T'I'II (AR) Unit) where
 component = rewrap `identity` \(T'I'II (These x _)) _ -> x
-}

-- CONTINUE HERE!

{-
instance Component (AR) (T'I'II P i `L` T'I'II (AR) Unit `T` (Void)) (T'I'II (AR) Unit) where
 component = rewrap `identity` \(T'I'II (These _ x)) _ -> x

instance Component (AR) (T'II'I P i `L` T'I'II (AR) Unit `T` (Void)) (T'I'II (AR) Unit) where
 component = rewrap `identity` \(T'II'I (These x _)) _ -> x
-}

{-
instance
 ( Covariant Semi Functor source target t
 , forall e . Wrapper target (t `L` t `T` l `T` e)
 , forall e . Wrapper target (t `T'TT'I` ttt `L` ttt `T` lll `T'I_` e)
 , forall e . Wrapper target (t `L` t `T` l `T'TT'I` ttt `L` ttt `T` lll `T'I_` e)
 , Mapping T'I'II T'I'II source target (t `T'TT'I` ttt `L` ttt `T` lll) t
 ) => Mapping T'I'II T'I'II source target (t `L` t `T` l `T'TT'I` ttt `L` ttt `T` lll) (t `L` t `T` l) where
 mapping = rewrap `identity`((`compose` supertype) `compose` rewrap `compose` (`compose` subtype) `compose` (map @T'I'II @T'I'II @source @target @(t `T'TT'I` ttt `L` ttt `T` lll) @t))
-}

instance (Precategory target, forall e . Wrapper target (I e))
 => Mapping T'I'II T'I'II target target I I where
 mapping = rewrap rewrap

instance Component (AR) (T'I'II (AR) Unit `L` I `T` (Void)) I where
 component = rewrap (\(T'I'II f) -> f Unit)

instance Component (AR) (I `L` T'I'II (AR) Unit `T` (Void)) (T'I'II (AR) Unit) where
 component = rewrap (\(Identity x) -> (\_ -> x))

instance
 ( Precategory target
 , forall e . Wrapper target (I `T` e)
 , forall e . Wrapper target (I `L` I `T` (Void) `T` e)
 , forall e . Wrapper target (I `T'TT'I` I `L` I `T` (Void) `T'I_` e)
 ) => Component target (I `T'TT'I` I `L` I `T` (Void)) I where
 component = rewrap (supertype `compose` supertype `compose` supertype)

instance
 ( Precategory target
 , forall e . Wrapper target (I `T` e)
 , forall e . Wrapper target (I `L` I `T` (Void) `T` e)
 , forall e . Wrapper target (I `T'TT'I` I `L` I `T` (Void) `T'I_` e)
 ) => Component target I (I `T'TT'I` I `L` I `T` (Void)) where
 component = rewrap (subtype `compose` subtype `compose` subtype)

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

instance
 Component (AR) ((T'I'II (AR) (i `P` ii) `P'T'I'TT'I` T'I' (I i `P` I ii)) `L` T'I'I (P) `T` (Void) `L` I `T` (Void)) I where
 component (supertype `compose` supertype `compose` supertype -> These (T'I'II f) (T'I' (These (Identity i) (Identity ii)))) = Identity (f (These i ii))

{-
instance
 ( Precategory target
 , forall e . Contravariant Elicitable target (T'I' i e)
 , forall e . Wrapper target (T'I' i (t `L` t `T` (Void) `T` e))
 ) => Component target (T'I' i `T'TT'I` t `L` t `T` (Void)) (T'I' i) where
 component = rewrap @target @((T'I' i `T'TT'I` t `L` t `T` (Void)) _) @(T'I' i _) (supertype @target @(T'I' i _))
-}

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

-- instance
 -- ( forall e . Covariant Endo Semi Functor (AR) (T'I'II u e)
 -- , forall e . Covariant Endo Semi Functor (AR) (T'II'I u e)
 -- , Covariant Monoidal Functor source (AR) u u Unit ttt
 -- , Covariant Transformation Functor source (AR) (t `T'TT'I` ttt) (t `TT'T'I` ttt)
 -- , Covariant Transformation Functor source (AR) (tt `T'TT'I` ttt) (tt `TT'T'I` ttt)
 -- , forall e . Wrapper source (T'TT'I'TTT'I u t tt e)
 -- , forall e . Wrapper (AR) (TT'T'I (T'TT'I'TTT'I u t tt) ttt e)
 -- , forall e . Wrapper (AR) (T'TT'I (T'TT'I'TTT'I u t tt) ttt e)
 -- ) => Mapping T'I'II T'I'II source (AR) (T'TT'I'TTT'I u t tt `T'TT'I` ttt) (T'TT'I'TTT'I u t tt `TT'T'I` ttt) where
 -- mapping = rewrap `identity` \source -> rewrap `identity`
  -- day @T'I'II @source @Unit @ttt @u @u (subtype @_ @(T'TT'I'TTT'I u t tt _)) identity
   -- `compose` i_ (map @T'I'II @T'I'II @(AR) @(AR) (wrapped (map @T'I'II @T'I'II @source @(AR) @(t `T'TT'I` ttt) @(t `TT'T'I` ttt) source)))
   -- `compose` _i (map @T'I'II @T'I'II @(AR) @(AR) (wrapped (map @T'I'II @T'I'II @source @(AR) @(tt `T'TT'I` ttt) @(tt `TT'T'I` ttt) source)))
   -- `compose` supertype @(AR) @(T'TT'I'TTT'I u t tt _)

-- TODO: here should be a generalized version of an instance above
-- instance
 -- ( forall e . Covariant Endo Semi Functor target (T'I'II (u :: * -> * -> *) (t e))
 -- , forall e . Wrapper target (T'TT'I'TTT'I u t tt e)
 -- , forall e . Wrapper target (TT'T'I (T'TT'I'TTT'I u t tt) ttt e)
 -- , forall e . Wrapper target (T'TT'I (T'TT'I'TTT'I u t tt) ttt e)
 -- ) => Mapping T'I'II T'I'II source target (T'TT'I'TTT'I u t tt `T'TT'I` ttt) (T'TT'I'TTT'I u t tt `TT'T'I` ttt where
 -- mapping = rewrap `identity` \source -> rewrap `identity`
  -- day_ @T'I'II @source @source @ttt @u @u (subtype @_ @(T'TT'I'TTT'I u t tt _)) identity `compose`
   -- wrapped (map @T'I'II @target @target @(T'II'I u _)
    -- (wrapped (map @T'I'II @T'I'II @source @target @(t `T'TT'I` ttt) @(t `TT'T'I` ttt) source))) `compose`
   -- wrapped (map @T'I'II @target @target @(T'I'II u _)
    -- (wrapped (map @T'I'II @T'I'II @source @target @(tt `T'TT'I` ttt) @(tt `TT'T'I` ttt) source))) `compose`
   -- supertype @target @(T'TT'I'TTT'I u t tt _)

-- TODO: add a label
instance Mapping T'I'II T'I'II (AR) (AR) (P'I'II e `T'TT'I` T'I'II (AR) e) I where
 mapping = rewrap `identity` \source -> rewrap `identity` \(T'I'II (These e (T'I'II f))) -> source (f e)

-- TODO: add a label
instance Mapping T'I'II T'I'II (AR) (AR) I (T'I'II (AR) e `T'TT'I` P'I'II e) where
 mapping = rewrap `identity` \source -> rewrap `identity` \x -> T'I'II `identity` \e -> T'I'II (These e (source x))

-- TODO: remove
instance Mapping T'I'II T'I'II (AR) (AR) I (T'I'II (AR) e `T'TT'I` T'II'I (P) e) where
 mapping = rewrap `identity` \source -> rewrap `identity` \x -> T'I'II `identity` \e -> T'II'I (These (source x) e)

instance Mapping T'I'II T'I'II (AR) (AR) (I `L` (T'I'II (AR) e `T'TT'I` T'II'I (P) e) `T` (Void)) (T'I'II (AR) e `T'TT'I` T'II'I (P) e) where
 mapping = rewrap `identity` \source -> rewrap `compose` rewrap `identity` \x -> \e -> T'II'I (These (source x) e)

instance Mapping T'I'II T'I'II (AR) (AR) (T'I'II (AR) Unit `L` (T'I'II (AR) e `T'TT'I` T'II'I (P) e) `T` (Void)) (T'I'II (AR) e `T'TT'I` T'II'I (P) e) where
 mapping = rewrap `identity` \source -> rewrap `compose` rewrap `identity` \f -> \e -> T'II'I (These (source (f Unit)) e)

-- TODO: remove
instance Mapping T'I'II T'I'II (AR) (AR) (T'II'I (P) e `T'TT'I` T'I'II (AR) e) I where
 mapping = rewrap `identity` \source -> rewrap `identity` \(T'II'I (These (T'I'II f) e)) -> source (f e)

instance Mapping T'I'II T'I'II (AR) (AR) ((T'II'I (P) e `T'TT'I` T'I'II (AR) e) `L` I `T` (Void)) I where
 mapping = rewrap `identity` \source -> rewrap `identity` \(T'TT'I (T'II'I (These (T'I'II f) e))) -> source (f e)

instance {-# OVERLAPS #-} Mapping T'I'II T'I'II (AR) (AR) (T'II'I (P) e) (T'II'I (P) e `T'TT'I` T'II'I (P) e `L` T'II'I (P) e `T` Void) where
 mapping = rewrap `identity` \source -> rewrap `identity` \(These xx x) -> T'II'I (These (Label (T'II'I (These (source xx) x))) x)

instance
 ( forall e . Mapping T'I'II T'I'II (AR) (AR) (T'I'II t e) (T'I'II t e)
 , forall e . Mapping T'I'II T'I'II (AR) (AR) (T'II'I t e) (T'II'I t e)
 ) => Mapping T'I'II T'I'II (AR) (AR) (T'I'I t) (T'I'I t) where
 mapping = rewrap `identity` \source ->
  subtype `compose` supertype
  `compose` map @T'I'II @T'I'II @AR @AR @(T'I'II t _) @(T'I'II t _) source `compose` subtype `compose` supertype
  `compose` map @T'I'II @T'I'II @AR @AR @(T'II'I t _) @(T'II'I t _) source `compose` subtype `compose` supertype

{-
instance
 ( Covariant Endo Semi Functor (AR) tt
 , Covariant Endo Semi Functor (AR) (T'I'I t)
 , forall i . Covariant Endo Semi Functor (AR) (T'I'II t i)
 , forall i . Covariant Endo Semi Functor (AR) (T'II'I t i)
 , forall e ee . Covariant Transformation Functor (AR) (AR) (Covariant Day (AR) t t tt (tt `L` tt `T` l) e ee) tt
 , forall i . Wrapper (AR) (T'I'I t i)
 ) => Mapping T'I'II T'I'II (AR) (AR) (T'I'I t `T'TT'I` tt `L` tt `T` l `L` T'I'I t `T` Void) (T'I'I t `TT'T'I` tt) where
 mapping = rewrap `identity` \source -> rewrap `identity`
  (day @T'I'II @(AR) @l @tt @tt @t @t identity
   (map @T'I'II @T'I'II source `compose` subtype @(AR) @(T'I'I t _))
  `compose` i_ (map @T'I'II @T'I'II (supertype @(AR) @(tt `L` tt `T` l `T` _) `compose` supertype @(AR) @(tt `L` tt `T` l `L` T'I'I t `T` Void `T` _)))
  `compose` _i (map @T'I'II @T'I'II (supertype @(AR) @(tt `L` tt `T` l `L` T'I'I t `T` Void `T` _)))
  `compose` supertype @(AR) @(T'I'I t _)
  )
-}

-- instance
 -- ( Covariant Semi Functor (AR) (AR) t
 -- , Covariant Functor (AR) (AR) (T'I'I u)
 -- , Covariant Endo Monoidal Functor (AR) u u tt
 -- , Mapping T'I'II T'I'II (AR) (AR) (t `T'TT'I` tt) (t `TT'T'I` tt)
 -- ) => Mapping T'I'II T'I'II (AR) (AR)
  -- ((T'I'I u `T'TT'I` t) `T'TT'I` tt)
  -- ((T'I'I u `T'TT'I` t) `TT'T'I` tt) where
 -- mapping = rewrap `identity` \source -> rewrap `identity`
  -- map @T'I'II @T'I'II @(AR) @(AR) (subtype @_ @(T'I'I u `T'TT'I` t `T'I` _)) `compose`
  -- wrapped (component @(AR) @(T'I'I u `T'TT'I` tt) @(T'I'I u `TT'T'I` tt)) `compose`
  -- map @T'I'II @T'I'II @(AR) @(AR) @(T'I'I u)
   -- (wrapped `identity`map @T'I'II @T'I'II @(AR) @(AR) @(t `T'TT'I` tt) @(t `TT'T'I` tt) source) `compose`
  -- supertype @(AR)

-- instance Covariant Yoneda (AR) (AR) tt =>
--  Mapping T'I'II T'I'II (AR) (AR) (T'II'I (P) e `T'TT'I` tt) (T'II'I (P) e `TT'T'I` tt) where
--  mapping = rewrap `identity` \source -> rewrap `identity` \(T'II'I (These x e)) ->
--   yoneda @T'I'II x (T'II'I `compose` (\x_ -> These (source x_) e))

-- instance
 -- Covariant Endo Semi Functor (AR) t =>
 -- Mapping T'I'II T'I'II (TR) (TR) t t where
 -- mapping = rewrap `identity` \(T'I'TT'II'I source) ->
  -- T'I'TT'II'I `identity` \x -> x `yo` this `ha` source `lu_` x `yo` that `ha` source

{-
instance Mapping T'I'II T'I'II (AR) (AR) (T'I'II (AS) i) (T'I'II (AS) i) where
 mapping = rewrap `identity` \source -> rewrap `compose` rewrap `identity` \(These between x) -> (These (source `compose` between) x)
-}

-- instance Mapping T'II'I T'I'II (AT) (AR) (T'II'I (AS) i) (T'II'I (AS) i) where
 -- mapping = rewrap `identity` \source -> rewrap `compose` rewrap `identity` \(These between x) ->
  -- let These a ao = source `supertype` between x in
  -- (These (source `compose` between) a)

 -- source : (o `AT` a) ~ (o `AR` a `P` (a `AR` o))
-- between : a `AR` i
      -- x : a

instance Mapping T'I'II T'I'II (AR) (AR)
 (Covariant Embedding (AR) (AR) t e)
 (Covariant Embedding (AR) (AR) t e) where
 mapping = rewrap `identity` \source ->
  rewrap (`compose` (rewrap (`compose` source)))

instance Mapping T'II'I T'I'II (AR) (AR)
 (Contravariant Embedding (AR) (AR) t e)
 (Contravariant Embedding (AR) (AR) t e) where
 mapping = rewrap `identity` \source ->
  rewrap (`compose` (rewrap (source `compose`)))

instance
 ( Covariant Semi Functor source (AR) t
 , forall e . Covariant Semi Functor target (AR) (T'I'II source e)
 ) => Mapping T'I'II T'I'II source (AR) t (Covariant Embedding target (AR) t r) where
 mapping = rewrap `identity` \source x ->
  Embedding `identity` \e -> map @T'I'II @T'I'II @source
   (wrapped (map @T'I'II @T'I'II @target @(AR) @(T'I'II source _) @(T'I'II source _) (supertype e)) source) x

{-
instance
 ( Covariant Endo Semi Functor (AR) t
 , forall e . Covariant Endo Semi Functor (AR) (T'I'II (AR) e)
 ) => Mapping U_1_I T'I'II (AR) (AR) t (Embedding U_1_I (AR) (AR) t r) where
 mapping = rewrap `identity` \_ x ->
  Embedding (\(U_1_I e) -> map @T'I'II @T'I'II (\_ -> e Unit) x)
-}

instance
 ( Contravariant Semi Functor source (AR) t
 , forall e . Contravariant Semi Functor target (AR) (T'II'I source e)
 ) => Mapping T'II'I T'I'II source (AR) t (Contravariant Embedding target (AR) t r) where
 mapping = rewrap `identity` \source x ->
  Embedding `identity` \e -> map @T'II'I @T'I'II @source
   (wrapped (map @T'II'I @T'I'II @target @(AR) @(T'II'I source _) @(T'II'I source _) (supertype e)) source) x


-- TODO: implement `mapping` method
-- instance Mapping T'I'II T'I'II (W_I_II_II (U_I_UU_III_T'II'I (AR) (P))) (AR)
--  (UU_V_T'I'II_T_II T'I'II (W_I_II_II (U_I_UU_III_T'II'I (AR) (P))) (AR) (T'I'II (W_I_II_II (U_I_UU_III_T'II'I (AR) (P))) ee) e)
--  (UU_V_T'I'II_T_II T'I'II (W_I_II_II (U_I_UU_III_T'II'I (AR) (P))) (AR) (T'I'II (W_I_II_II (U_I_UU_III_T'II'I (AR) (P))) ee) e)

-- TODO: implement `mapping` method
-- instance Mapping T'II'I T'I'II (T'I'TT'II'I (AR) (P))) (AR)
--  (UU_V_T'I'II_T_II T'II'I (W_I_II_II (U_I_UU_III_T'II'I (AR) (P))) (AR) (T'II'I (T'I'TT'II'I (AR) (P))) ee) e)
--  (UU_V_T'I'II_T_II T'II'I (W_I_II_II (U_I_UU_III_T'II'I (AR) (P))) (AR) (T'II'I (T'I'TT'II'I (AR) (P))) ee) e)

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

{-
instance Mapping T'I'II T'I'II (AR) target t tt
 => Mapping U_1_I T'I'II (AR) target t tt where
  mapping (U_1_I f) = mapping (T'I'II (f `compose` terminal))
-}

-- instance Mapping T'I'II T'I'II (AR) (AR) (U_1_I (AR) e) (U_1_I (AR) e) where
--  mapping = rewrap `identity` \source (U_1_I x) -> U_1_I `identity`source x

-- TODO: remove everything related to constant
instance Mapping T'I'II T'I'II (AR) (AR) I (T'I'II (AR) e) where
 mapping = rewrap `identity` \source (Identity x) -> T'I'II `identity` \_ -> source x

instance Mapping T'I'II T'I'II (AR) (AR) I (T'I'I (P)) where
 mapping (T'I'II source) = T'I'II `identity` \(Identity x) -> T'I'I (These (source x) (source x))

instance Mapping T'I'II T'I'II (AR) (AR) (P'I'II e) I where
 mapping (T'I'II source) = T'I'II `identity` \(T'I'II (These _ x)) -> Identity (source x)

-- TODO: add a label
instance Mapping T'I'II T'I'II (AR) (AR) (T'II'I (P) e) I where
 mapping (T'I'II source) = T'I'II `identity` \(T'II'I (These x _)) -> Identity (source x)

instance Mapping T'I'II T'I'II (AR) (AR) (T'I'I (S)) I where
 mapping (T'I'II source) = T'I'II `identity` \case
  T'I'I (This x) -> Identity (source x)
  T'I'I (That x) -> Identity (source x)

{-
instance Mapping T'I'II T'I'II (AR) (AR) I (S'I'II e) where
 mapping (T'I'II source) = T'I'II `identity` \(Identity x) -> T'I'II (That (source x))

instance Mapping T'I'II T'I'II (AR) (AR) I (T'II'I (S) e) where
 mapping (T'I'II source) = T'I'II `identity` \(Identity x) -> T'II'I (This (source x))
-}

-- instance Mapping T'I'II T'I'II
 -- (W_I_II_II (U_I_UU_III_T'II'I (AR) (P)))
 -- (W_I_II_II (U_I_UU_III_T'II'I (AR) (P)))
 -- (This (P) e) Identity where
 -- mapping = rewrap `compose` rewrap `compose` rewrap `identity`
  -- \source (T'II'I (These old e)) -> These 
   -- (Identity (wrapped (left @T'I'II @(AR) identity) (source old)))
   -- (\(Identity new) -> T'II'I (These ((wrapped (right @T'I'II @(AR) identity) (source old)) new) e))

-- instance Mapping T'I'II T'I'II
 -- (W_I_II_II (U_I_UU_III_T'II'I (AR) (P)))
 -- (W_I_II_II (U_I_UU_III_T'II'I (AR) (P)))
 -- (That (P) e) Identity where
 -- mapping = rewrap `compose` rewrap `compose` rewrap `identity`
  -- -- \source (T'I'II (These e old)) -> These 
   -- `identity`Identity (wrapped (left @T'I'II @(AR) identity) (source old))
   -- `identity` \(Identity new) -> T'I'II (These e ((wrapped (right @T'I'II @(AR) identity) (source old)) new))

-- instance Mapping T'I'II T'I'II (W_I_II_II (U_I_UU_III_T'II'I (AR) (P))) (AR) Identity (T'I'I (P)) where
 -- mapping = rewrap `identity` \(W_I_II_II (U_I_UU_III_T'II'I source)) (Identity old) -> T'I'I `identity`These
  -- (wrapped (left @T'I'II @(AR) identity) (source old))
  -- (wrapped (left @T'I'II @(AR) identity) (source old))

-- instance Mapping T'II'I T'I'II (W_I_II_II (U_I_UU_III_T'II'I (AR) (P))) (AR) (This (AR) e) (This (AR) e) where
 -- mapping = rewrap `identity` \(W_I_II_II (U_I_UU_III_T'II'I source)) ->
  -- map @T'II'I @T'I'II `identity`(\(These x _) -> x) `compose` source

-- T'I' (t (ttt i) (tttt ii)) `P'T'I'TT'I` T'I'II (AR) (tt i ii)

instance Covariant Endo Semi Functor (AR) t =>
 Component (AR) ((T'I'II (AR) (i `S` ii) `P'T'I'TT'I` T'I' (t i `S` t ii)) `L` T'I'I (S) `T` (Void) `L` t `T` (Void)) t where
 component (supertype `compose` supertype `compose` supertype -> These (T'I'II f) x) = case supertype x of
  This xx -> map @T'I'II @T'I'II @AR @AR @t (f `compose` This) `identity` xx
  That xx -> map @T'I'II @T'I'II @AR @AR @t (f `compose` That) `identity` xx

{-
instance
 Component (AR) ((T'II'I (AR) (i `P` ii) `P'T'I'TT'I` T'I'II (AR) e) `L` T'I'I (P) `T` (Void) `L` T'II'I (AR) e `T` (Void)) (T'I' (T'I'II (AR) e i `P` T'I'II (AR) e ii)) where
 -- Component (AR) ((T'II'I (AR) (i `P` ii) `P'T'I'TT'I` T'I' (T'I'II (AR) e i `P` T'I'II (AR) e ii)) `L` T'I'I (P) `T` (Void) `L` T'I'II (AR) e `T` (Void)) (T'I'II (AR) e) where
 component (supertype `compose` supertype `compose` supertype -> These (T'I'II f) x) = case supertype x of
  These (T'I'II g) (T'I'II h) -> T'I'II (\e -> f (These (g e) (h e)))

-- o `AR` i `P` ii

-- e `AR` o

-- (e `AR` i) `P` (e `AR` ii)
-}

instance
 Component (AR) ((T'I'II (AR) (i `S` ii) `P'T'I'TT'I` T'II'I (AR) e) `L` T'I'I (S) `T` (Void) `L` T'II'I (AR) e `T` (Void)) (T'I' (T'II'I (AR) e i `P` T'II'I (AR) e ii)) where
 component (supertype `compose` supertype `compose` supertype -> These (T'I'II f) (T'II'I g)) = T'I' (These (T'II'I (\i -> g (f (This i)))) (T'II'I (\ii -> g (f (That ii)))))

instance
 Component (AR) ((T'I'II (AR) (i `P` ii) `P'T'I'TT'I` T'I' (T'I'II (AR) e i `P` T'I'II (AR) e ii)) `L` T'I'I (P) `T` (Void) `L` T'I'II (AR) e `T` (Void)) (T'I'II (AR) e) where
 component (supertype `compose` supertype `compose` supertype -> These (T'I'II f) x) = case supertype x of
  These (T'I'II g) (T'I'II h) -> T'I'II (\e -> f (These (g e) (h e)))

instance
 Component (AR) ((T'II'I (AR) (i `S` ii) `P'T'I'TT'I` T'I' (T'II'I (AR) e i `P` T'II'I (AR) e ii)) `L` T'I'I (S) `T` (Void) `L` T'II'I (AR) e `T` (Void)) (T'II'I (AR) e) where
 component (supertype `compose` supertype `compose` supertype -> These (T'II'I f) x) = case supertype x of
  These (T'II'I g) (T'II'I h) -> T'II'I ((\case { This i -> g i; That ii -> h ii; }) `compose` f)

{-
instance
 Component (AR) ((T'I'II (AR) (i `S` ii) `P'T'I'TT'I` T'II'I (AR) e) `L` T'I'I (S) `T` (Void) `L` T'II'I (AR) e `T` (Void)) (T'I' (T'II'I (AR) e i `P` T'II'I (AR) e ii)) where
 component (supertype `compose` supertype `compose` supertype -> These (T'I'II f) (T'II'I g)) = T'I' (These (T'II'I (\i -> g (f (This i)))) (T'II'I (\ii -> g (f (That ii)))))
-}

instance
 Component (AR) ((T'I'II (AR) (i `P` ii) `P'T'I'TT'I` T'I' (T'I'II (S) e i `P` T'I'II (S) e ii)) `L` T'I'I (P) `T` (Void) `L` T'I'II (S) e `T` (Void)) (T'I'II (S) e) where
 component (supertype `compose` supertype `compose` supertype -> These (T'I'II f) x) = case supertype x of
  These (T'I'II (That ii)) (T'I'II (That iii)) -> T'I'II (That (f (These ii iii)))
  These (T'I'II (This i)) _ -> T'I'II (This i)
  These _ (T'I'II (This i)) -> T'I'II (This i)

instance
 Component (AR) ((T'I'II (AR) (i `S` ii) `P'T'I'TT'I` T'I' (T'I'II (S) e i `P` T'I'II (S) e ii)) `L` T'I'I (S) `T` (Void) `L` T'I'II (S) e `T` (Void)) (T'I'II (S) e) where
 component (supertype `compose` supertype `compose` supertype -> These (T'I'II f) x) = case supertype x of
  These (T'I'II (This i)) (T'I'II (This ii)) -> T'I'II (This i)
  These (T'I'II (This i)) (T'I'II (That ii)) -> T'I'II (That (f (That ii)))
  These (T'I'II (That i)) _ -> T'I'II (That (f (This i)))

instance
 Component (AR) ((T'I'II (AR) (i `W` ii) `P'T'I'TT'I` T'I' (T'I'II (S) e i `P` T'I'II (S) e ii)) `L` T'I'I (W) `T` (Void) `L` T'I'II (S) e `T` (Void)) (T'I'II (S) e) where
 component (supertype `compose` supertype `compose` supertype -> These (T'I'II f) x) = case supertype x of
  These (T'I'II (That ee)) (T'I'II (That eee)) -> T'I'II (That (f (T'T'I'II'TT'I'II (That (These ee eee)))))
  These (T'I'II (That ee)) (T'I'II (This e)) -> T'I'II (That (f (T'T'I'II'TT'I'II (This (This ee)))))
  These (T'I'II (This i)) (T'I'II (That ii)) -> T'I'II (That (f (T'T'I'II'TT'I'II (This (That ii)))))
  These (T'I'II (This i)) (T'I'II (This _)) -> T'I'II (This i)

instance
 Component (AR) ((T'II'I (AR) (i `P` ii) `P'T'I'TT'I` T'I'II (S) e) `L` T'I'I (P) `T` (Void) `L` T'I'II (S) e `T` (Void)) (T'I' (T'I'II (S) e i `P` T'I'II (S) e ii)) where
 component (supertype `compose` supertype `compose` supertype -> These (T'II'I f) x) = T'I' (These (map @T'I'II @T'I'II (this `compose` f) x) (map @T'I'II @T'I'II (that `compose` f) x))

{-
instance Component (AR) (TTTTT'V'M'T'TT'TTT'TTTT'I'II'III T'I'II (AR) (P) (S) (T'I'II (S) e) (T'I'II (S) e) ee eee `L` T'I'I (S) `T` (Void) `L` T'I'II (S) e `T` (Void)) (T'I'II (S) e) where
 component = rewrap `identity` \case
  Label (TTTTT'V'M'T'TT'TTT'TTTT'I'II'III (These (These (T'I'II (That ee)) _) (T'I'II f))) -> That (f (This ee))
  Label (TTTTT'V'M'T'TT'TTT'TTTT'I'II'III (These (These (T'I'II (This e)) _) _)) -> This e
  Label (TTTTT'V'M'T'TT'TTT'TTTT'I'II'III (These (These _ (T'I'II (That eee))) (T'I'II f))) -> That (f (That eee))
-}

{-
instance Component (AR) (T'I'II (S) e `L` T'I'I (P) `T` (Void) `L` T'I'II (S) e `T` (Void)) (TTTTT'V'M'T'TT'TTT'TTTT'I'II'III T'II'I (AR) (P) (P) (T'I'II (S) e) (T'I'II (S) e) ee eee) where
 component = rewrap `identity` \case
  Label x -> These (These (T'I'II (That ee)) _) (T'I'II f)
-}

-- TODO: make one `Plain` and another one `Stack`?

instance
 Component (AR) (T'I'II (AR) Unit `L` (T'I'II (AR) i `T'TT'I` T'II'I (P) i) `T` (Void)) (T'I'II (AR) i `T'TT'I` T'II'I (P) i) where
 component = rewrap `compose` rewrap `identity` \f x -> T'II'I (These (f Unit) x)

instance
 Component (AR) (T'I'II (AR) Unit `L` (T'I'II (AR) i `T'TT'I` T'I'II (P) i) `T` (Void)) (T'I'II (AR) i `T'TT'I` T'I'II (P) i) where
 component = rewrap `compose` rewrap `identity` \f x -> T'I'II (These x (f Unit))

instance
 Component (AR) ((T'I'II (AR) i `TT'T'I` T'II'I (P) i) `L` I `T` (Void)) I where
 component = rewrap `identity` \(TT'T'I (T'II'I (These f x))) -> supertype f x

instance
 Component (AR) (T'I'II (AR) Unit `L` t `T` l) t =>
 Component (AR) (I `L` t `T` l) t where
 component (Label (Identity x)) = component @(AR) @(T'I'II (AR) Unit `L` t `T` l) @t (Label (T'I'II (\_ -> x)))

-- instance Mapping T'I'II T'I'II
 -- (W_I_II_II (U_I_UU_III_T'II'I (AR) (P)))
 -- (W_I_II_II (U_I_UU_III_T'II'I (AR) (P)))
 -- (T'I'I (P)) (T'I'II (AR) (S Unit Unit)) where
 -- mapping = rewrap `compose` rewrap `compose` rewrap `identity` \source (T'I'I (These x y)) -> These
  -- `identity`T'I'II (\case { This Unit -> this (source x); That Unit -> this (source y) })
  -- `identity` \(T'I'II f) -> T'I'I (These
   -- `identity`that (source x) (f (This Unit))
   -- `identity`that (source x) (f (That Unit))
   -- )

-- instance Mapping T'I'II T'I'II
 -- (W_I_II_II (U_I_UU_III_T'II'I (AR) (P)))
 -- (W_I_II_II (U_I_UU_III_T'II'I (AR) (P)))
 -- (T'I'II (AR) (S Unit Unit)) (T'I'I (P)) where
 -- mapping = rewrap `compose` rewrap `compose` rewrap `identity` \source (T'I'II f) -> These
  -- `identity`T'I'I (These `identity`this (source (f (This Unit))) `identity`this (source (f (That Unit))))
  -- `identity` \(T'I'I (These x y)) -> T'I'II `identity` \case
   -- This Unit -> that (source (f (This Unit))) x
   -- That Unit -> that (source (f (That Unit))) y

-- instance Mapping T'I'II T'I'II (AR) (AR)
  -- (Day T'I'II (AR) (P) (S) (T'I'I (P) `T'TT'I` t) (T'I'I (P) `T'TT'I` t) ee eee) (T'I'I (P) `T'TT'I` t)

-- instance Monoidal T'I'II Functor (AR) (P) (S) t
 -- => Mapping T'I'II T'I'II (AR) (AR) (T'I'II (AR) Void) (T'I'I (P) `T'TT'I` t) where
 -- mapping = rewrap `identity` \_ _ -> T'TT'I `compose` T'I'I `identity`These
  -- (map @T'I'II @T'I'II @(AR) @(AR) @t @t initial empty)
  -- (map @T'I'II @T'I'II @(AR) @(AR) @t @t initial empty)

{-
instance (forall e ee . Mapping T'I'II T'I'II (AR) (AR) (Day T'I'II (AR) (P) (P) t (t `L` t `T` Void) e ee) t)
 => Mapping T'I'II T'I'II (AR) (AR) (Day T'I'II (AR) (P) (P) (T'I'II (AR) e `T'TT'I` t) ((T'I'II (AR) e `T'TT'I` t) `L` (T'I'II (AR) e `T'TT'I` t) `T` Void) ee eee) (T'I'II (AR) e `T'TT'I` t) where
 mapping = rewrap `identity` \source -> rewrap `identity` \case
  These (These (T'TT'I x) (Label (T'TT'I xx))) (T'I'II f) -> (T'I'II (\e ->
   day @T'I'II @(AR) @Void @t @t @(P) @(P) identity (source `compose` f) `identity` These (supertype x e) (subtype (supertype xx e))))
-}

-- 0: (S'I'II e `TT'T'I` t `T'TT'I_` Void `L`  (S'I'II e `TT'T'I` t)) _
-- 1: (S'I'II e `TT'T'I` t) (Void `L` ((S'I'II e `TT'T'I` t) _))
-- 2: t ((S'I'II e) (Void `L` (S'I'II e `TT'T'I` t) _))
-- 3: t ((S'I'II e) (t (S'I'II e) _))
-- 4: t (t ((S'I'II e) (S'I'II e) _))
-- 5: t ((S'I'II e) (S'I'II e) _)
-- 6: t ((S'I'II e) _)

instance {-# OVERLAPS #-}
 ( Covariant Endo Semi Functor AR t
 , Covariant Endo Semi Functor AR (tt `T'TT'I` t)
 , Covariant Transformation Functor (AR) (AR) (t `T'TT'I` t `L` t `T` Void) t
 , Covariant Transformation Functor (AR) (AR) (tt `T'TT'I` t `L` t `T` Void `L` tt `T` Void) (tt `TT'T'I` t)
 , Covariant Transformation Functor (AR) (AR) (tt `T'TT'I` tt `L` tt `T` Void) (tt)
 ) => Mapping T'I'II T'I'II (AR) (AR) ((tt `TT'T'I` t) `T'TT'I` (tt `TT'T'I` t) `L` (tt `TT'T'I` t) `T` Void) (tt `TT'T'I` t) where
 mapping = rewrap `identity` \source -> rewrap `identity` \x ->
  map @T'I'II @T'I'II @(AR) @(AR) @(t `T'TT'I` t `L` t `T` Void) @t
   (map @T'I'II @T'I'II @(AR) @(AR) @(tt `T'TT'I` tt `L` tt `T` Void) @(tt) source
   `compose` subtype @(AR) @(tt `T'TT'I` tt `L` tt `T` Void `T'I_` _)
   `compose` map  @T'I'II @T'I'II @(AR) @(AR) @(tt) @(tt) (subtype @(AR) @(tt `L` tt `T` Void `T'I` _))
   ) `compose` subtype @(AR) @(t `T'TT'I` t `L` t `T` Void `T'I_` _)
     `compose` map @T'I'II @T'I'II @(AR) @(AR) @t @t
   (subtype @(AR) @(t `L` t `T` Void `T'I` _)
   `compose` wrapped (map @T'I'II @T'I'II @(AR) @(AR) @(tt `T'TT'I` t `L` t `T` Void `L` tt `T` Void) @(tt `TT'T'I` t) identity)
   `compose` map @T'I'II @T'I'II @(AR) @(AR) @(tt) @(tt) (Label `compose` Label `compose` supertype `compose` supertype)
   ) `identity`supertype x

instance Adjoint Functor (AR) (AR) (T'II'I (P) i) (T'I'II (AR) i)
instance Adjoint Functor (AR) (AR) (T'I'II (P) i) (T'I'II (AR) i)

instance Mapping T'I'II T'I'II (AR) (AR) (T'I'II (AR) (Unit `S` Unit)) (T'I'I (P)) where
 mapping = rewrap `identity` \source -> rewrap `identity` \f -> These
  (source `compose` f `identity` This Unit)
  (source `compose` f `identity` That Unit)

instance Mapping T'I'II T'I'II (AR) (AR) (T'I'I (P)) (T'I'II (AR) (Unit `S` Unit)) where
 mapping = rewrap `identity` \source -> rewrap `identity` \(These x y) -> \case
  This _ -> source x
  That _ -> source y

instance Mapping T'I'II T'I'II (AR) (AR) (T'I'I (P)) (T'I'I (P) `T'TT'I` T'II'I (P) (Unit `S` Unit) `L` T'II'I (P) (Unit `S` Unit) `T` (Void)) where
 mapping = rewrap `identity` \source -> rewrap `identity` \(These x xx) -> T'I'I (These (Label (T'II'I (These (source x) (This Unit)))) (Label (T'II'I (These (source xx) (That Unit)))))

-- TODO: remove
instance
 ( Mapping T'I'II T'I'II (AR) (AR) (T'I'II (AR) i) t
 , Mapping T'I'II T'I'II (AR) (AR) (T'I'II (AR) ii) tt
 ) => Mapping T'I'II T'I'II (AR) (AR) (T'I'II (AR) (i `S` ii)) (t `P'T'I'TT'I` tt) where
 mapping = rewrap `identity` \source -> rewrap `identity` \f -> These
  (map @T'I'II @T'I'II @AR @AR @(T'I'II (AR) i) @t source `identity` T'I'II (f `compose` This))
  (map @T'I'II @T'I'II @AR @AR @(T'I'II (AR) ii) @tt source `identity` T'I'II (f `compose` That))

-- TODO: remove
instance
 ( iii ~ i `S` ii
 , Mapping T'I'II T'I'II (AR) (AR) t (T'I'II (AR) i)
 , Mapping T'I'II T'I'II (AR) (AR) tt (T'I'II (AR) ii)
 ) => Mapping T'I'II T'I'II (AR) (AR) (t `P'T'I'TT'I` tt) (T'I'II (AR) (iii)) where
 mapping = rewrap `identity` \source -> rewrap `identity` \(These x y) -> \case
  This i -> map @T'I'II @T'I'II @AR @AR @t @(T'I'II (AR) _) source x `supertype` i
  That ii -> map @T'I'II @T'I'II @AR @AR @tt @(T'I'II (AR) _) source y `supertype` ii

-- TODO: remove
instance
 ( Mapping T'I'II T'I'II (AR) (AR) (T'I'II (AR) i) t
 , Mapping T'I'II T'I'II (AR) (AR) (T'I'II (AR) ii) tt
 ) => Mapping T'I'II T'I'II (AR) (AR) (T'I'II (AR) (i `P` ii)) (t `T'TT'I` tt) where
 mapping = rewrap `identity` \source -> rewrap `identity`
  (let currying i ii iii = i (These ii iii) in
   map @T'I'II @T'I'II @AR @AR @(T'I'II (AR) i) @t
    (map @T'I'II @T'I'II @AR @AR @(T'I'II (AR) ii) @tt source `compose` T'I'II)
   `compose` T'I'II
   `compose` currying)

-- TODO: remove
instance
 ( Mapping T'I'II T'I'II (AR) (AR) (T'I'II (AR) i) t
 , Mapping T'I'II T'I'II (AR) (AR) (T'I'II (AR) ii) tt
 ) => Mapping T'I'II T'I'II (AR) (AR) (T'I'II (AR) (ii `P` i)) (t `TT'T'I` tt) where
 mapping = rewrap `identity` \source -> rewrap `identity`
  (let currying i ii iii = i (These ii iii) in
   map @T'I'II @T'I'II @AR @AR @(T'I'II (AR) ii) @tt
    (map @T'I'II @T'I'II @AR @AR @(T'I'II (AR) i) @t source `compose` T'I'II)
   `compose` T'I'II
   `compose` currying)

-- TODO: remove
instance
 ( Mapping T'I'II T'I'II (AR) (AR) t (T'I'II (AR) i)
 , Mapping T'I'II T'I'II (AR) (AR) tt (T'I'II (AR) ii)
 ) => Mapping T'I'II T'I'II (AR) (AR) (t `T'TT'I` tt) (T'I'II (AR) (i `P` ii)) where
 mapping = rewrap `identity` \source -> rewrap `identity`
  (let uncurrying i (These ii iii) = i ii iii in
  uncurrying `compose` supertype @(AR) `compose` map @T'I'II @T'I'II @AR @AR @t @(T'I'II (AR) i)
    (supertype @(AR) `compose` map @T'I'II @T'I'II @AR @AR @tt @(T'I'II (AR) ii) source))

instance
 ( Mapping T'I'II T'I'II (AR) (AR) t (T'I'II (AR) i)
 , Mapping T'I'II T'I'II (AR) (AR) tt (T'I'II (AR) ii)
 ) => Mapping T'I'II T'I'II (AR) (AR) (t `TT'T'I` tt) (T'I'II (AR) (ii `P` i)) where
 mapping = rewrap `identity` \source -> rewrap `identity`
  (let uncurrying i (These ii iii) = i ii iii in
  uncurrying `compose` supertype @(AR) `compose` map @T'I'II @T'I'II @AR @AR @tt @(T'I'II (AR) ii)
    (supertype @(AR) `compose` map @T'I'II @T'I'II @AR @AR @t @(T'I'II (AR) i) source))
