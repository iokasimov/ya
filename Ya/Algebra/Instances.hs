{-# OPTIONS_GHC -fno-warn-orphans #-}
{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE UndecidableInstances #-}
module Ya.Algebra.Instances where

import Ya.Algebra.Abstract
import Ya.Algebra.Definition

instance Mapping T'I'II T'I'II AR target t tt
 => Mapping T''II T'I'II AR target t tt where
  mapping = rewrap `identity` (map @T'I'II @T'I'II @AR @target `compose` constant)

instance
 ( Covariant Semi Functor source target t
 , forall e . Wrapper target (t `L` tt `T` ll `T` e)
 ) => Mapping T'I'II T'I'II source target (t `L` tt `T` ll) (t `L` tt `T` ll) where
 mapping = rewrap `identity` (rewrap `compose` map @T'I'II @T'I'II @source @target @t @t)

instance
 ( Covariant Semi Functor source target t
 , forall e . Wrapper target (t `L` t `T` l `T` e)
 , forall e . Wrapper target (t `T'TT'I` ttt `L` ttt `T` lll `T'I_` e)
 , forall e . Wrapper target (t `L` t `T` l `T'TT'I` ttt `L` ttt `T` lll `T'I_` e)
 , Mapping T'I'II T'I'II source target (t `T'TT'I` ttt `L` ttt `T` lll) t
 ) => Mapping T'I'II T'I'II source target (t `L` t `T` l `T'TT'I` ttt `L` ttt `T` lll) (t `L` t `T` l) where
 mapping = rewrap `identity` ((`compose` unwrap) `compose` rewrap `compose` (`compose` wrap) `compose` (map @T'I'II @T'I'II @source @target @(t `T'TT'I` ttt `L` ttt `T` lll) @t))

instance (Precategory target, forall e . Wrapper target (I e))
 => Mapping T'I'II T'I'II target target I I where
 mapping = rewrap rewrap

instance (Precategory target, forall i ii . Wrapper target (T'I' i ii))
 => Mapping T'I'II T'I'II target (AR) (T'I' i) (T'I' i) where
 mapping = rewrap `identity` \_ (T'I' x) -> (T'I' x)

instance
 ( Precategory target
 , forall i ii . Wrapper target (T'I' i ii)
 , Covariant Lax Monoidal Functor (AR) (AR) (P) P Void t
 ) => Mapping T'I'II T'I'II target (AR) (T'I' i `T'TT'I` t `L` t `T` l `L` T'I' i `T` ll) (T'I' i `TT'T'I` t) where
 mapping = rewrap `identity` \_ -> rewrap `identity` \(T'I' x) -> intro (T'I' x)

instance
 ( forall e . Wrapper target (I e)
 , forall e . Wrapper target (t `L` t `T` l `L` I `T` ll `T` e)
 , forall e . Wrapper target (t `L` t `T` l `T` e)
 , forall e . Wrapper target (I `TT'T'I` t `T'I_` e)
 , forall e . Wrapper target (I `T'TT'I` t `L` t `T` l `L` I `T` ll `T'I_` e)
 , Covariant Endo Semi Functor target t
 ) => Mapping T'I'II T'I'II target target (I `T'TT'I` t `L` t `T` l `L` I `T` ll) (I `TT'T'I` t) where
 mapping = rewrap `identity` \source -> rewrap (
  map @T'I'II @T'I'II @target @target (wrap @target @(I _) `compose` source)
   `compose` unwrap @target @(t `L` t `T` l `T` _)
   `compose` unwrap @target @(t `L` t `T` l `L` I `T` ll `T` _)
   `compose` unwrap @target @(I _))

instance
 ( Covariant Semi Functor source target tt
 , Covariant Endo Semi Functor target t
 , forall e . Wrapper target (t `T'TT'I` tt `T'I_` e)
 ) => Mapping T'I'II T'I'II source target (t `T'TT'I` tt) (t `T'TT'I` tt) where
 mapping = rewrap `identity` \source -> wrap @target `compose` (map @T'I'II @T'I'II @target @target `compose` map @T'I'II @T'I'II @source @target) source `compose` unwrap @target

instance
 ( Covariant Semi Functor source target t
 , Covariant Endo Semi Functor target tt
 , forall e . Wrapper target (t `TT'T'I` tt `T'I_` e)
 ) => Mapping T'I'II T'I'II source target (t `TT'T'I` tt) (t `TT'T'I` tt) where
 mapping = rewrap `identity` \source -> wrap @target `compose` (map @T'I'II @T'I'II @target @target `compose` map @T'I'II @T'I'II @source @target) source `compose` unwrap @target

instance
 ( Covariant Semi Functor source target t
 , forall ee . Covariant Endo Semi Functor target (T'I'II u ee)
 , forall ee . Wrapper target (T'I'II (T'I'TT'II u t) e ee)
 , forall ee . Wrapper target (T'I'TT'II u t e ee)
 , forall ee . Wrapper target (T'I'II u e (t ee))
 ) => Mapping T'I'II T'I'II source target (T'I'II (T'I'TT'II u t) e) (T'I'II (T'I'TT'II u t) e) where
 mapping = rewrap `identity` \source ->
  wrap @target @(T'I'II _ _ _)
  `compose` wrap @target @(T'I'TT'II _ _ _ _)
  `compose` unwrap @target @(T'I'II _ _ _)
  `compose` map @T'I'II @T'I'II @target @target (map @T'I'II @T'I'II @source @target source)
  `compose` wrap @target @(T'I'II _ _ _)
  `compose` unwrap @target @(T'I'TT'II _ _ _ _)
  `compose` unwrap @target @(T'I'II _ _ _)

instance
 ( forall ee . Covariant Semi Functor source target (T'II'I u ee)
 , forall ee . Wrapper target (T'II'I (T'I'TT'II u t) e ee)
 , forall ee . Wrapper target (T'I'TT'II u t ee e)
 , forall ee . Wrapper target (T'II'I u (t e) ee)
 ) => Mapping T'I'II T'I'II source target (T'II'I (T'I'TT'II u t) e) (T'II'I (T'I'TT'II u t) e) where
 mapping = rewrap `identity` \source ->
  wrap @target @(T'II'I _ _ _)
  `compose` wrap @target @(T'I'TT'II _ _ _ _)
  `compose` unwrap @target @(T'II'I _ _ _)
  `compose` map @T'I'II @T'I'II @source @target source
  `compose` wrap @target @(T'II'I _ _ _)
  `compose` unwrap @target @(T'I'TT'II _ _ _ _)
  `compose` unwrap @target @(T'II'I _ _ _)

instance
 ( Covariant Semi Functor source target h
 , Covariant Endo Semi Functor target tt
 , Covariant Endo Semi Functor target t
 , forall e . Wrapper target (T'TTT'TT'I t h tt e)
 ) => Mapping T'I'II T'I'II source target (T'TTT'TT'I t h tt) (T'TTT'TT'I t h tt) where
 mapping = rewrap `identity` \source -> wrap @target
  `compose` (map @T'I'II @T'I'II @target @target
   `compose` map @T'I'II @T'I'II @target @target
   `compose` map @T'I'II @T'I'II @source @target
   ) source
  `compose` unwrap @target

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
  i_ (map @T'I'II @T'I'II @target @target `compose` map @T'I'II @T'I'II @source @target @t @t `identity` source) `compose`
  _i (map @T'I'II @T'I'II @target @target `compose` map @T'I'II @T'I'II @source @target @tt @tt `identity` source))

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
  -- day @T'I'II @source @Unit @ttt @u @u (wrap @_ @(T'TT'I'TTT'I u t tt _)) identity
   -- `compose` i_ (map @T'I'II @T'I'II @(AR) @(AR) (wrapped (map @T'I'II @T'I'II @source @(AR) @(t `T'TT'I` ttt) @(t `TT'T'I` ttt) source)))
   -- `compose` _i (map @T'I'II @T'I'II @(AR) @(AR) (wrapped (map @T'I'II @T'I'II @source @(AR) @(tt `T'TT'I` ttt) @(tt `TT'T'I` ttt) source)))
   -- `compose` unwrap @(AR) @(T'TT'I'TTT'I u t tt _)

-- TODO: here should be a generalized version of an instance above
-- instance
 -- ( forall e . Covariant Endo Semi Functor target (T'I'II (u :: * -> * -> *) (t e))
 -- , forall e . Wrapper target (T'TT'I'TTT'I u t tt e)
 -- , forall e . Wrapper target (TT'T'I (T'TT'I'TTT'I u t tt) ttt e)
 -- , forall e . Wrapper target (T'TT'I (T'TT'I'TTT'I u t tt) ttt e)
 -- ) => Mapping T'I'II T'I'II source target (T'TT'I'TTT'I u t tt `T'TT'I` ttt) (T'TT'I'TTT'I u t tt `TT'T'I` ttt where
 -- mapping = rewrap `identity` \source -> rewrap `identity`
  -- day_ @T'I'II @source @source @ttt @u @u (wrap @_ @(T'TT'I'TTT'I u t tt _)) identity `compose`
   -- wrapped (map @T'I'II @target @target @(T'II'I u _)
    -- (wrapped (map @T'I'II @T'I'II @source @target @(t `T'TT'I` ttt) @(t `TT'T'I` ttt) source))) `compose`
   -- wrapped (map @T'I'II @target @target @(T'I'II u _)
    -- (wrapped (map @T'I'II @T'I'II @source @target @(tt `T'TT'I` ttt) @(tt `TT'T'I` ttt) source))) `compose`
   -- unwrap @target @(T'TT'I'TTT'I u t tt _)

instance Mapping T'I'II T'I'II (AR) (AR) (P'I'II e `T'TT'I` T'I'II (AR) e) I where
 mapping = rewrap `identity` \source -> rewrap `identity` \(T'I'II (These e (T'I'II f))) -> source (f e)

instance Mapping T'I'II T'I'II (AR) (AR) I (T'I'II (AR) e `T'TT'I` P'I'II e) where
 mapping = rewrap `identity` \source -> rewrap `identity` \x -> T'I'II `identity` \e -> T'I'II (These e (source x))

instance Mapping T'I'II T'I'II (AR) (AR) I (T'I'II (AR) e `T'TT'I` T'II'I (P) e) where
 mapping = rewrap `identity` \source -> rewrap `identity` \x -> T'I'II `identity` \e -> T'II'I (These (source x) e)

instance Mapping T'I'II T'I'II (AR) (AR) (T'II'I (P) e `T'TT'I` T'I'II (AR) e) I where
 mapping = rewrap `identity` \source -> rewrap `identity` \(T'II'I (These (T'I'II f) e)) -> source (f e)

instance Mapping T'I'II T'I'II (AR) (AR) (T'I'II (P) i) (T'I'II (P) i) where
 mapping = rewrap `identity` \source -> rewrap `identity` \case
  These e x -> These e (source x)

instance Mapping T'I'II T'I'II (AR) (AR) (T'II'I (P) i) (T'II'I (P) i) where
 mapping = rewrap `identity` \source -> rewrap `identity` \case
  These x e -> These (source x) e

instance Mapping T'I'II T'I'II (AR) (AR) (T'I'II (S) i) (T'I'II (S) i) where
 mapping = rewrap `identity` \source -> rewrap `identity` \case
  That x -> That (source x)
  This e -> This e

instance Mapping T'I'II T'I'II (AT) (AT) (T'I'II (S) i) (T'I'II (S) i) where
 mapping = rewrap `identity` \(T'I'TT'II'T'II'I source) ->
  T'I'TT'II'T'II'I `identity` \case
   T'I'II (This i) -> These (T'I'II (This i)) (\_ -> T'I'II (This i))
   T'I'II (That x) -> These (T'I'II (That (this (source x)))) (map @T'I'II @T'I'II (that (source x)))

instance Mapping T'I'II T'I'II (AR) (AR) (T'II'I (S) o) (T'II'I (S) o) where
 mapping = rewrap `identity` \source -> rewrap `identity` \case
  This x -> This (source x)
  That e -> That e

instance
 ( Covariant Endo Semi Functor (AR) tt
 , Covariant Endo Semi Functor (AR) (T'I'I t)
 , forall i . Covariant Endo Semi Functor (AR) (T'I'II t i)
 , forall i . Covariant Endo Semi Functor (AR) (T'II'I t i)
 , Covariant Lax Monoidal Functor (AR) (AR) t t l tt
 , forall i . Wrapper (AR) (T'I'I t i)
 ) => Mapping T'I'II T'I'II (AR) (AR) (T'I'I t `T'TT'I` tt `L` tt `T` l `L` T'I'I t `T` Void) (T'I'I t `TT'T'I` tt) where
 mapping = rewrap `identity` \source -> rewrap `identity`
  (day @T'I'II @(AR) @l @tt @tt @t @t identity
   (map @T'I'II @T'I'II source `compose` wrap @(AR) @(T'I'I t _))
  `compose` i_ (map @T'I'II @T'I'II (unwrap @(AR) @(tt `L` tt `T` l `T` _) `compose` unwrap @(AR) @(tt `L` tt `T` l `L` T'I'I t `T` Void `T` _)))
  `compose` _i (map @T'I'II @T'I'II (unwrap @(AR) @(tt `L` tt `T` l `L` T'I'I t `T` Void `T` _)))
  `compose` unwrap @(AR) @(T'I'I t _)
  )

-- instance
 -- ( Covariant Semi Functor (AR) (AR) t
 -- , Covariant Functor (AR) (AR) (T'I'I u)
 -- , Covariant Endo Monoidal Functor (AR) u u tt
 -- , Mapping T'I'II T'I'II (AR) (AR) (t `T'TT'I` tt) (t `TT'T'I` tt)
 -- ) => Mapping T'I'II T'I'II (AR) (AR)
  -- ((T'I'I u `T'TT'I` t) `T'TT'I` tt)
  -- ((T'I'I u `T'TT'I` t) `TT'T'I` tt) where
 -- mapping = rewrap `identity` \source -> rewrap `identity`
  -- map @T'I'II @T'I'II @(AR) @(AR) (wrap @_ @(T'I'I u `T'TT'I` t `T'I` _)) `compose`
  -- wrapped (component @(AR) @(T'I'I u `T'TT'I` tt) @(T'I'I u `TT'T'I` tt)) `compose`
  -- map @T'I'II @T'I'II @(AR) @(AR) @(T'I'I u)
   -- (wrapped `identity` map @T'I'II @T'I'II @(AR) @(AR) @(t `T'TT'I` tt) @(t `TT'T'I` tt) source) `compose`
  -- unwrap @(AR)

-- instance Covariant Yoneda (AR) (AR) tt =>
--  Mapping T'I'II T'I'II (AR) (AR) (T'II'I (P) e `T'TT'I` tt) (T'II'I (P) e `TT'T'I` tt) where
--  mapping = rewrap `identity` \source -> rewrap `identity` \(T'II'I (These x e)) ->
--   yoneda @T'I'II x (T'II'I `compose` (\x_ -> These (source x_) e))

-- TODO: to fix
instance Mapping T'I'II T'I'II (AR) (AR)
 (T'I'II (T'I'TT'II'I (AR) (P)) e)
 (T'I'II (T'I'TT'II'I (AR) (P)) e) where
 mapping = rewrap `identity` \source -> rewrap `compose` rewrap `identity` \f x ->
  i_ (map @T'I'II @T'I'II source) (f x)

instance Mapping T'I'II T'I'II
 (T'I'TT'II'I (AR) (P)) (AR)
 (T'I'II (T'I'TT'II'I (AR) (P)) i)
 (T'I'II (T'I'TT'II'I (AR) (P)) i) where
 mapping = rewrap `identity` \(T'I'TT'II'I source)
  -> rewrap `compose` rewrap `identity` \origin i ->
   let These result ii = origin i in
   let These update _ = source result in
   These update i

instance Mapping T'II'I T'I'II
 (T'I'TT'II'I (AR) (P)) (AR)
 (T'II'I (T'I'TT'II'I (AR) (P)) i)
 (T'II'I (T'I'TT'II'I (AR) (P)) i) where
 mapping = rewrap `identity` \(T'I'TT'II'I source)
  -> rewrap `compose` rewrap `identity` \origin o ->
   let These a oo = source o in
   let These i _ = origin a in
   These i oo

instance
 Covariant Endo Semi Functor (AR) t =>
 Mapping T'I'II T'I'II (TR) (TR) t t where
 mapping = rewrap `identity` \(T'I'TT'II'I source) ->
  T'I'TT'II'I `identity` \x -> x `yo` this `ha` source `lu_` x `yo` that `ha` source

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
   (wrapped (map @T'I'II @T'I'II @target @(AR) @(T'I'II source _) @(T'I'II source _) (unwrap e)) source) x

instance
 ( Covariant Endo Semi Functor (AR) t
 , forall e . Covariant Endo Semi Functor (AR) (T'I'II (AR) e)
 ) => Mapping U_1_I T'I'II (AR) (AR) t (Embedding U_1_I (AR) (AR) t r) where
 mapping = rewrap `identity` \_ x ->
  Embedding (\(U_1_I e) -> map @T'I'II @T'I'II (\_ -> e Unit) x)

instance
 ( Contravariant Semi Functor source (AR) t
 , forall e . Contravariant Semi Functor target (AR) (T'II'I source e)
 ) => Mapping T'II'I T'I'II source (AR) t (Contravariant Embedding target (AR) t r) where
 mapping = rewrap `identity` \source x ->
  Embedding `identity` \e -> map @T'II'I @T'I'II @source
   (wrapped (map @T'II'I @T'I'II @target @(AR) @(T'II'I source _) @(T'II'I source _) (unwrap e)) source) x


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
 , forall e . Wrapper source (F'T'I'TT'I (T'I'II u) t e)
 , forall e . Wrapper target (F'T'I'TT'I (T'I'II u) t e)
 , forall i . Wrapper source (Recursive (T'I'II u i `T'TT'I` t))
 , forall i . Wrapper target (Recursive (T'I'II u i `T'TT'I` t))
 , forall i ii . Wrapper source (T'II'I u i ii)
 , forall i ii . Wrapper target (T'II'I u i ii)
 , forall i ii . Wrapper source (T'I'II u i ii)
 , forall i ii . Wrapper target (T'I'II u i ii)
 , forall i ii . Wrapper source ((T'I'II u i `T'TT'I` t) ii)
 , forall i ii . Wrapper target ((T'I'II u i `T'TT'I` t) ii)
 ) => Mapping T'I'II T'I'II source target (F'T'I'TT'I (T'I'II u) t) (F'T'I'TT'I (T'I'II u) t) where
 mapping = rewrap `identity` \source -> rewrap `compose` rewrap `identity`
  ((rewrap `compose` rewrap) (wrapped (map @T'I'II @T'I'II @_ @_ @(T'II'I u (t _)) @(T'II'I u (t _)) source))
  `compose` map @T'I'II @T'I'II @source @target @(T'I'II u _ `T'TT'I` t) @(T'I'II u _ `T'TT'I` t)
   (wrapped (map @T'I'II @T'I'II @source @_ @(F'T'I'TT'I (T'I'II u) t) @(F'T'I'TT'I (T'I'II u) t) source))
  )

instance
 ( forall i . Covariant Semi Functor source target (T'II'I u i `T'TT'I` t)
 , forall i . Covariant Endo Semi Functor source (T'II'I u i `T'TT'I` t)
 , forall i . Covariant Endo Semi Functor source (T'I'II u (t i))
 , forall i . Covariant Semi Functor source target (T'I'II u (t i))
 , forall e . Wrapper source (F'T'I'TT'I (T'II'I u) t e)
 , forall e . Wrapper target (F'T'I'TT'I (T'II'I u) t e)
 , forall i . Wrapper source (Recursive (T'II'I u i `T'TT'I` t))
 , forall i . Wrapper target (Recursive (T'II'I u i `T'TT'I` t))
 , forall i ii . Wrapper source (T'II'I u i ii)
 , forall i ii . Wrapper target (T'II'I u i ii)
 , forall i ii . Wrapper source (T'I'II u i ii)
 , forall i ii . Wrapper target (T'I'II u i ii)
 , forall i ii . Wrapper source ((T'II'I u i `T'TT'I` t) ii)
 , forall i ii . Wrapper target ((T'II'I u i `T'TT'I` t) ii)
 ) => Mapping T'I'II T'I'II source target (F'T'I'TT'I (T'II'I u) t) (F'T'I'TT'I (T'II'I u) t) where
 mapping = rewrap `identity` \source -> rewrap `compose` rewrap `identity`
  ((rewrap `compose` rewrap) (wrapped (map @T'I'II @T'I'II @_ @_ @(T'I'II u (t _)) @(T'I'II u (t _)) source))
  `compose` map @T'I'II @T'I'II @source @target @(T'II'I u _ `T'TT'I` t) @(T'II'I u _ `T'TT'I` t)
   (wrapped (map @T'I'II @T'I'II @source @_ @(F'T'I'TT'I (T'II'I u) t) @(F'T'I'TT'I (T'II'I u) t) source))
  )

instance {-# OVERLAPPABLE #-} Mapping T'I'II T'I'II (AR) (AR) (T'I'II (AR) a) (T'I'II (AR) a) where
 mapping (T'I'II source) = T'I'II `identity` \(T'I'II between) -> T'I'II (\x -> source (between x))

instance Mapping T'II'I T'I'II (AR) (AR) (T'II'I (AR) o) (T'II'I (AR) o) where
 mapping (T'II'I source) = T'I'II `identity` \(T'II'I between) -> T'II'I (\x -> between (source x))

instance Category (AR) where
 identity = \x -> x

instance Mapping T'I'II T'I'II (AR) target t tt
 => Mapping U_1_I T'I'II (AR) target t tt where
  mapping (U_1_I f) = mapping (T'I'II (f `compose` terminal))

-- instance Mapping T'I'II T'I'II (AR) (AR) (U_1_I (AR) e) (U_1_I (AR) e) where
--  mapping = rewrap `identity` \source (U_1_I x) -> U_1_I `identity` source x

instance Mapping T'I'II T'I'II (AR) (AR) I (T'I'II (AR) e) where
 mapping = rewrap `identity` \source (Identity x) -> T'I'II `identity` \_ -> source x

instance Mapping T'I'II T'I'II (AR) (AR) I (T'I'I (P)) where
 mapping (T'I'II source) = T'I'II `identity` \(Identity x) -> T'I'I (These (source x) (source x))

-- TODO: redefine using limits
instance Mapping T'I'II T'I'II (AR) (AR) (T'I'I (P)) (T'I'I (P)) where
 mapping (T'I'II source) = T'I'II `identity` \(T'I'I (These x y)) -> T'I'I (These (source x) (source y))

instance Mapping T'I'II T'I'II (AR) (AR) (P'I'II e) I where
 mapping (T'I'II source) = T'I'II `identity` \(T'I'II (These _ x)) -> Identity (source x)

instance Mapping T'I'II T'I'II (AR) (AR) (T'II'I (P) e) I where
 mapping (T'I'II source) = T'I'II `identity` \(T'II'I (These x _)) -> Identity (source x)

instance Mapping T'I'II T'I'II (AR) (AR) (T'I'I (S)) I where
 mapping (T'I'II source) = T'I'II `identity` \case
  T'I'I (This x) -> Identity (source x)
  T'I'I (That x) -> Identity (source x)

instance Mapping T'I'II T'I'II (AR) (AR) I (S'I'II e) where
 mapping (T'I'II source) = T'I'II `identity` \(Identity x) -> T'I'II (That (source x))

instance Mapping T'I'II T'I'II (AR) (AR) I (T'II'I (S) e) where
 mapping (T'I'II source) = T'I'II `identity` \(Identity x) -> T'II'I (This (source x))

instance Mapping T'I'II T'I'II (AT) (AR) (T'I'II (AT) i) (T'I'II (AT) i) where
 mapping = rewrap `identity` \target -> rewrap `compose` rewrap `identity` \source x ->
  let These i i_origin = source x in
  let These ii ii_i = unwrap target i in
  These ii (i_origin `compose` ii_i)

instance Mapping T'II'I T'I'II (AT) (AR) (T'II'I (AT) i) (T'II'I (AT) i) where
 mapping = rewrap `identity` \source -> rewrap `compose` rewrap `identity` \target x ->
  let These i i_origin = unwrap source x in
  let These ii ii_i = target i in
  These ii (i_origin `compose` ii_i)

instance Category (AT) where
 identity = T'I'TT'II'T'II'I `identity` \x -> These x identity

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
   -- `identity` Identity (wrapped (left @T'I'II @(AR) identity) (source old))
   -- `identity` \(Identity new) -> T'I'II (These e ((wrapped (right @T'I'II @(AR) identity) (source old)) new))

-- instance Mapping T'I'II T'I'II (W_I_II_II (U_I_UU_III_T'II'I (AR) (P))) (AR) Identity (T'I'I (P)) where
 -- mapping = rewrap `identity` \(W_I_II_II (U_I_UU_III_T'II'I source)) (Identity old) -> T'I'I `identity` These
  -- (wrapped (left @T'I'II @(AR) identity) (source old))
  -- (wrapped (left @T'I'II @(AR) identity) (source old))

-- instance Mapping T'II'I T'I'II (W_I_II_II (U_I_UU_III_T'II'I (AR) (P))) (AR) (This (AR) e) (This (AR) e) where
 -- mapping = rewrap `identity` \(W_I_II_II (U_I_UU_III_T'II'I source)) ->
  -- map @T'II'I @T'I'II `identity` (\(These x _) -> x) `compose` source

instance Mapping T'I'II T'I'II (AR) (AR) (Day T'I'II (AR) (P) P I (I `L` I `T` Void) e ee) I where
 mapping = rewrap `identity` \source -> rewrap `identity` \case
  These (These (Identity e) (Label (Identity ee))) (T'I'II f) -> source (f (These e ee))

instance Mapping T'I'II T'I'II (AR) (AR) (T'I'II (AR) Unit) I where
 mapping = rewrap `identity` \source (T'I'II f) -> Identity (source (f Unit))

instance Mapping T'I'II T'I'II (AR) (AR)
 (Day T'I'II (AR) (P) P (T'II'I (S) e) (T'II'I (S) e `L` T'II'I (S) e `T` Void) ee eee) (T'II'I (S) e) where
 mapping = rewrap `identity` \source -> rewrap `identity` \case
  These (These (T'II'I (This ee)) (Label (T'II'I (This eee)))) (T'I'II f) -> This (source (f (These ee eee)))
  These (These (T'II'I (That e)) _) _ -> That e

instance Mapping T'I'II T'I'II (AR) (AR) (T'I'II (AR) Unit) (T'II'I (S) e) where
 mapping = rewrap `identity` \source (T'I'II f) -> T'II'I (This (source (f Unit)))

instance Mapping T'I'II T'I'II (AR) (AR)
 (Day T'I'II (AR) (P) P (S'I'II e) (S'I'II e `L` S'I'II e `T` Void) ee eee) (S'I'II e) where
 mapping = rewrap `identity` \source -> rewrap `identity` \case
  These (These (T'I'II (That ee)) (Label (T'I'II (That eee)))) (T'I'II f) -> That (source (f (These ee eee)))
  These (These (T'I'II (This e)) _) _ -> This e
  These (These _ (Label (T'I'II (This e)))) _ -> This e

instance Mapping T'I'II T'I'II (AR) (AR)
 (Day T'I'II (AR) (P) (R) (S'I'II e) (S'I'II e `L` S'I'II e `T` Void) ee eee) (S'I'II e) where
 mapping = rewrap `identity` \source -> rewrap `identity` \case
  These (These (T'I'II (That ee)) (Label (T'I'II (That eee)))) (T'I'II f) ->
   That `compose` source `compose` f `compose` U_T'I'II_UT'I'II `compose` That `identity` These ee eee
  These (These (T'I'II (That ee)) _) (T'I'II f) ->
   That `compose` source `compose` f `compose` U_T'I'II_UT'I'II `compose` This `identity` This ee
  These (These (T'I'II (This _)) (Label (T'I'II (That eee)))) (T'I'II f) ->
   That `compose` source `compose` f `compose` U_T'I'II_UT'I'II `compose` This `identity` That eee
  These (These (T'I'II (This e)) (Label (T'I'II (This _)))) (T'I'II _) ->
   This e

instance Mapping T'I'II T'I'II (AR) (AR) (T'I'II (AR) Unit) (S'I'II e) where
 mapping = rewrap `identity` \source (T'I'II f) -> T'I'II (That (source (f Unit)))

instance Mapping T'I'II T'I'II (AR) (AR) (Day T'I'II (AR) (P) (S) (S'I'II e) (S'I'II e `L` S'I'II e `T` Void) ee eee) (S'I'II e) where
 mapping = rewrap `identity` \source -> rewrap `identity` \case
  These (These (T'I'II (That ee)) _) (T'I'II f) -> That (source (f (This ee)))
  These (These _ (Label (T'I'II (That eee)))) (T'I'II f) -> That (source (f (That eee)))
  These (These _ (Label (T'I'II (This eee)))) (T'I'II _) -> This eee

instance Mapping T'I'II T'I'II (AR) (AR) (T'I'II (AR) Void) (T'II'I (S) Unit) where
 mapping = rewrap `identity` \_ _ -> T'II'I (That Unit)

-- instance Mapping T'I'II T'I'II (AR) (AR)
--   (Day T'I'II (AR) (P) (S) (T'II'I (S) e) (T'II'I (S) e) ee eee) (T'II'I (S) e) where
--  mapping = rewrap `identity` \source -> rewrap `identity` \case
--   These (These (T'II'I (This ee)) _) (T'I'II f) -> This (source (f (This ee)))
--   These (These _ (T'II'I (This eee))) (T'I'II f) -> This (source (f (That eee)))
--   These (These _ (T'II'I (That eee))) _ -> That eee

instance Mapping T'I'II T'I'II (AR) (AR) (T'I'II (AR) Void) (S'I'II Unit) where
 mapping = rewrap `identity` \_ _ -> T'I'II (This Unit)

instance Mapping T'I'II T'I'II (AR) (AR) (T'I'II (AR) (S Unit Unit)) (T'I'I (P)) where
 mapping = rewrap `identity` \source -> rewrap `identity` \f -> These
  (source `compose` f `identity` This Unit)
  (source `compose` f `identity` That Unit)

instance Mapping T'I'II T'I'II (AR) (AR) (T'I'I (P)) (T'I'II (AR) (S Unit Unit)) where
 mapping = rewrap `identity` \source -> rewrap `identity` \(These x y) -> \case
  This _ -> source x
  That _ -> source y

-- instance Mapping T'I'II T'I'II
 -- (W_I_II_II (U_I_UU_III_T'II'I (AR) (P)))
 -- (W_I_II_II (U_I_UU_III_T'II'I (AR) (P)))
 -- (T'I'I (P)) (T'I'II (AR) (S Unit Unit)) where
 -- mapping = rewrap `compose` rewrap `compose` rewrap `identity` \source (T'I'I (These x y)) -> These
  -- `identity` T'I'II (\case { This Unit -> this (source x); That Unit -> this (source y) })
  -- `identity` \(T'I'II f) -> T'I'I (These
   -- `identity` that (source x) (f (This Unit))
   -- `identity` that (source x) (f (That Unit))
   -- )

-- instance Mapping T'I'II T'I'II
 -- (W_I_II_II (U_I_UU_III_T'II'I (AR) (P)))
 -- (W_I_II_II (U_I_UU_III_T'II'I (AR) (P)))
 -- (T'I'II (AR) (S Unit Unit)) (T'I'I (P)) where
 -- mapping = rewrap `compose` rewrap `compose` rewrap `identity` \source (T'I'II f) -> These
  -- `identity` T'I'I (These `identity` this (source (f (This Unit))) `identity` this (source (f (That Unit))))
  -- `identity` \(T'I'I (These x y)) -> T'I'II `identity` \case
   -- This Unit -> that (source (f (This Unit))) x
   -- That Unit -> that (source (f (That Unit))) y

-- instance Mapping T'I'II T'I'II (AR) (AR)
  -- (Day T'I'II (AR) (P) (S) (T'I'I (P) `T'TT'I` t) (T'I'I (P) `T'TT'I` t) ee eee) (T'I'I (P) `T'TT'I` t)

-- instance Monoidal T'I'II Functor (AR) (P) (S) t
 -- => Mapping T'I'II T'I'II (AR) (AR) (T'I'II (AR) Void) (T'I'I (P) `T'TT'I` t) where
 -- mapping = rewrap `identity` \_ _ -> T'TT'I `compose` T'I'I `identity` These
  -- (map @T'I'II @T'I'II @(AR) @(AR) @t @t initial empty)
  -- (map @T'I'II @T'I'II @(AR) @(AR) @t @t initial empty)

instance Mapping T'I'II T'I'II (AR) (AR) (Day T'I'II (AR) (P) (P) t (t `L` t `T` Void) ee eee) t
 => Mapping T'I'II T'I'II (AR) (AR) (Day T'I'II (AR) (P) (P) (T'I'II (AR) e `T'TT'I` t) ((T'I'II (AR) e `T'TT'I` t) `L` (T'I'II (AR) e `T'TT'I` t) `T` Void) ee eee) (T'I'II (AR) e `T'TT'I` t) where
 mapping = rewrap `identity` \source -> rewrap `identity` \case
  These (These (T'TT'I x) (Label (T'TT'I xx))) (T'I'II f) -> (T'I'II (\e ->
   day @T'I'II @(AR) @Void @t @t @(P) @(P) identity (source `compose` f) `identity` These (unwrap x e) (wrap (unwrap xx e))))

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
   `compose` wrap @(AR) @(tt `T'TT'I` tt `L` tt `T` Void `T'I_` _)
   `compose` map  @T'I'II @T'I'II @(AR) @(AR) @(tt) @(tt) (wrap @(AR) @(tt `L` tt `T` Void `T'I` _))
   ) `compose` wrap @(AR) @(t `T'TT'I` t `L` t `T` Void `T'I_` _)
     `compose` map @T'I'II @T'I'II @(AR) @(AR) @t @t
   (wrap @(AR) @(t `L` t `T` Void `T'I` _)
   `compose` wrapped (map @T'I'II @T'I'II @(AR) @(AR) @(tt `T'TT'I` t `L` t `T` Void `L` tt `T` Void) @(tt `TT'T'I` t) identity)
   `compose` map @T'I'II @T'I'II @(AR) @(AR) @(tt) @(tt) (Label `compose` Label `compose` unwrap `compose` unwrap)
   ) `identity` unwrap x

instance Adjoint Functor (AR) (AR) (T'II'I (P) i) (T'I'II (AR) i)
instance Adjoint Functor (AR) (AR) (T'I'II (P) i) (T'I'II (AR) i)
