{-# OPTIONS_GHC -fno-warn-orphans #-}
{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE UndecidableInstances #-}
module Ya.Algebra.Instances where

import Ya.Algebra.Abstract
import Ya.Algebra.Definition

instance (Precategory into, forall e . Wrapper into (I e)) 
 => Mapping Straight Straight into into I I where
 mapping = rewrap rewrap

instance
 ( forall e . Wrapper into (I e)
 , forall e . Wrapper into (L l t e)
 , forall e . Wrapper into (I `TT'T'I` t `WR___` e)
 , forall e . Wrapper into (I `T'TT'I` L l t `WR___` e)
 , Covariant Endo Semi Functor into t
 ) => Mapping U_I_II U_I_II into into (I `T'TT'I` L l t) (I `TT'T'I` t) where
 mapping = rewrap / \from -> rewrap /
  map @U_I_II @U_I_II @into @into (wrap @into @(I _) `compose` from) `compose` unwrap @into @(L l t _) `compose` unwrap @into @(I _)

instance
 ( Covariant Semi Functor from into tt
 , Covariant Endo Semi Functor into t
 , forall e . Wrapper into (T'TT'I t tt e)
 ) => Mapping Straight Straight from into (T'TT'I t tt) (T'TT'I t tt) where
 mapping = rewrap / \from -> wrap @into `compose` (map @Straight @Straight @into @into `compose` map @Straight @Straight @from @into) from `compose` unwrap @into

instance
 ( Covariant Semi Functor from into t
 , Covariant Endo Semi Functor into tt
 , forall e . Wrapper into (TT'T'I t tt e)
 ) => Mapping Straight Straight from into (TT'T'I t tt) (TT'T'I t tt) where
 mapping = rewrap / \from -> wrap @into `compose` (map @Straight @Straight @into @into `compose` map @Straight @Straight @from @into) from `compose` unwrap @into

instance
 ( Covariant Semi Functor from into t
 , forall e . Wrapper into (T_'_I l t e)
 ) => Mapping Straight Straight from into (T_'_I l t) (T_'_I l t) where
 mapping = rewrap / \from -> wrap @into @(T_'_I _ t _)
   `compose` map @Straight @Straight @from @into @t from
   `compose` unwrap @into @(T_'_I _ t _)

instance
 ( Covariant Semi Functor from into t
 , forall ee . Covariant Endo Semi Functor into (Straight u ee)
 , forall ee . Wrapper into (Straight (U_I_T_II t u) e ee)
 , forall ee . Wrapper into (U_I_T_II t u e ee)
 , forall ee . Wrapper into (Straight u e (t ee))
 ) => Mapping Straight Straight from into (Straight (U_I_T_II t u) e) (Straight (U_I_T_II t u) e) where
 mapping = rewrap / \from ->
  wrap @into @(Straight _ _ _)
  `compose` wrap @into @(U_I_T_II _ _ _ _)
  `compose` unwrap @into @(Straight _ _ _)
  `compose` map @Straight @Straight @into @into (map @Straight @Straight @from @into from)
  `compose` wrap @into @(Straight _ _ _)
  `compose` unwrap @into @(U_I_T_II _ _ _ _)
  `compose` unwrap @into @(Straight _ _ _)

instance
 ( forall ee . Covariant Semi Functor from into (Opposite u ee)
 , forall ee . Wrapper into (Opposite (U_I_T_II t u) e ee)
 , forall ee . Wrapper into (U_I_T_II t u ee e)
 , forall ee . Wrapper into (Opposite u (t e) ee)
 ) => Mapping Straight Straight from into (Opposite (U_I_T_II t u) e) (Opposite (U_I_T_II t u) e) where
 mapping = rewrap / \from ->
  wrap @into @(Opposite _ _ _)
  `compose` wrap @into @(U_I_T_II _ _ _ _)
  `compose` unwrap @into @(Opposite _ _ _)
  `compose` map @Straight @Straight @from @into from
  `compose` wrap @into @(Opposite _ _ _)
  `compose` unwrap @into @(U_I_T_II _ _ _ _)
  `compose` unwrap @into @(Opposite _ _ _)

instance
 ( Covariant Semi Functor from into h
 , Covariant Endo Semi Functor into tt
 , Covariant Endo Semi Functor into t
 , forall e . Wrapper into (T'TTT'TT'I t h tt e)
 ) => Mapping Straight Straight from into (T'TTT'TT'I t h tt) (T'TTT'TT'I t h tt) where
 mapping = rewrap / \from -> wrap @into
  `compose` (map @Straight @Straight @into @into
   `compose` map @Straight @Straight @into @into
   `compose` map @Straight @Straight @from @into
   ) from
  `compose` unwrap @into

instance
 ( forall e . Covariant Endo Semi Functor into (Straight u (t e))
 , forall e . Covariant Endo Semi Functor into (Opposite u (tt e))
 , Covariant Semi Functor from into tt
 , Covariant Semi Functor from into t
 , forall e . Wrapper into (U_T_I_TT_I u t tt e)
 , forall e ee . Wrapper into (Straight u (t e) (tt ee))
 , forall e ee . Wrapper into (Opposite u (tt e) (t ee))
 ) => Mapping Straight Straight from into (U_T_I_TT_I u t tt) (U_T_I_TT_I u t tt) where
 mapping = rewrap / \from -> rewrap /
  i_ (map @Straight @Straight @into @into `compose` map @Straight @Straight @from @into @t @t / from) `compose`
  _i (map @Straight @Straight @into @into `compose` map @Straight @Straight @from @into @tt @tt / from)

instance
 ( forall e . Covariant Endo Semi Functor AR (Straight u e)
 , forall e . Covariant Endo Semi Functor AR (Opposite u e)
 , Covariant Monoidal Functor from u u ttt
 , Component Natural from AR (t `T'TT'I` ttt) (t `TT'T'I` ttt)
 , Component Natural from AR (tt `T'TT'I` ttt) (tt `TT'T'I` ttt)
 , forall e . Wrapper from (U_T_I_TT_I u t tt e)
 , forall e . Wrapper AR (TT'T'I (U_T_I_TT_I u t tt) ttt e)
 , forall e . Wrapper AR (T'TT'I (U_T_I_TT_I u t tt) ttt e)
 ) => Mapping Straight Straight from AR (U_T_I_TT_I u t tt `T'TT'I` ttt) (U_T_I_TT_I u t tt `TT'T'I` ttt) where
 mapping = rewrap / \from -> rewrap /
  day @Straight @from @ttt @u @u (wrap @_ @(U_T_I_TT_I u t tt _)) identity `compose`
   i_ (map @Straight @Straight @AR @AR
    (wrapped (map @Straight @Straight @from @AR @(t `T'TT'I` ttt) @(t `TT'T'I` ttt) from))) `compose`
   _i (map @Straight @Straight @AR @AR
    (wrapped (map @Straight @Straight @from @AR @(tt `T'TT'I` ttt) @(tt `TT'T'I` ttt) from))) `compose`
   unwrap @AR @(U_T_I_TT_I u t tt _)

-- TODO: here should be a generalized version of an instance above
-- instance
 -- ( forall e . Covariant Endo Semi Functor into (Straight (u :: * -> * -> *) (t e))
 -- , forall e . Wrapper into (U_T_I_TT_I u t tt e)
 -- , forall e . Wrapper into (TT'T'I (U_T_I_TT_I u t tt) ttt e)
 -- , forall e . Wrapper into (T'TT'I (U_T_I_TT_I u t tt) ttt e)
 -- ) => Mapping Straight Straight from into (U_T_I_TT_I u t tt `T'TT'I` ttt) (U_T_I_TT_I u t tt `TT'T'I` ttt where
 -- mapping = rewrap / \from -> rewrap /
  -- day_ @Straight @from @from @ttt @u @u (wrap @_ @(U_T_I_TT_I u t tt _)) identity `compose`
   -- wrapped (map @Straight @into @into @(Opposite u _)
    -- (wrapped (map @Straight @Straight @from @into @(t `T'TT'I` ttt) @(t `TT'T'I` ttt) from))) `compose`
   -- wrapped (map @Straight @into @into @(Straight u _)
    -- (wrapped (map @Straight @Straight @from @into @(tt `T'TT'I` ttt) @(tt `TT'T'I` ttt) from))) `compose`
   -- unwrap @into @(U_T_I_TT_I u t tt _)

instance Mapping Straight Straight AR AR (U_I_II LM e `T'TT'I` U_I_II AR e) I where
 mapping = rewrap / \from -> rewrap / \(Straight (These e (Straight f))) -> from (f e)

instance Mapping Straight Straight AR AR I (U_I_II AR e `T'TT'I` U_I_II LM e) where
 mapping = rewrap / \from -> rewrap / \x -> U_I_II / \e -> U_I_II (These e (from x))

instance Mapping Straight Straight AR AR I (U_I_II AR e `T'TT'I` U_II_I LM e) where
 mapping = rewrap / \from -> rewrap / \x -> U_I_II / \e -> U_II_I (These (from x) e)

instance Mapping Straight Straight AR AR (U_II_I LM e `T'TT'I` U_I_II AR e) I where
 mapping = rewrap / \from -> rewrap / \(U_II_I (These (U_I_II f) e)) -> from (f e)

instance Mapping Straight Straight AR AR (U_I_II LM e) (U_I_II LM e) where
 mapping = rewrap / \from -> rewrap / \case
  These e x -> These e (from x)

instance Mapping Straight Straight AR AR (U_II_I LM o) (U_II_I LM o) where
 mapping = rewrap / \from -> rewrap / \case
  These x e -> These (from x) e

instance Mapping Straight Straight AR AR (U_I_II ML o) (U_I_II ML o) where
 mapping = rewrap / \from -> rewrap / \case
  That x -> That (from x)
  This e -> This e

instance Mapping Straight Straight AR AR (U_II_I ML o) (U_II_I ML o) where
 mapping = rewrap / \from -> rewrap / \case
  This x -> This (from x)
  That e -> That e

instance
 ( Covariant Semi Functor from AR t
 , Covariant Functor from from (U_I_I u)
 , Covariant Monoidal Functor from u u t
 , forall e . Castable Opposite from (U_I_I u e)
 ) => Mapping Straight Straight from AR (U_I_I u `T'TT'I` t) (U_I_I u `TT'T'I` t) where
 mapping = rewrap / \from -> rewrap /
  day @Straight @from @t @u @u
   (map @Straight @Straight from `compose` wrap @from @(U_I_I _ _)) identity
  `compose` unwrap @AR @(U_I_I u _)

instance
 ( Covariant Semi Functor AR AR t
 , Covariant Functor AR AR (U_I_I u)
 , Covariant Monoidal Functor AR u u tt
 , Mapping Straight Straight AR AR (T'TT'I t tt) (TT'T'I t tt)
 ) => Mapping Straight Straight AR AR
  ((U_I_I u `T'TT'I` t) `T'TT'I` tt)
  ((U_I_I u `T'TT'I` t) `TT'T'I` tt) where
 mapping = rewrap / \from -> rewrap /
  map @Straight @Straight @AR @AR (wrap @_ @(T'TT'I (U_I_I u) t _)) `compose`
  wrapped (component @Straight @AR @AR @(T'TT'I (U_I_I u) tt) @(TT'T'I (U_I_I u) tt)) `compose`
  map @Straight @Straight @AR @AR @(U_I_I u)
   (wrapped / map @Straight @Straight @AR @AR @(T'TT'I t tt) @(TT'T'I t tt) from) `compose`
  unwrap @AR

-- instance Covariant Yoneda AR AR tt =>
--  Mapping Straight Straight AR AR (U_II_I LM e `T'TT'I` tt) (U_II_I LM e `TT'T'I` tt) where
--  mapping = rewrap / \from -> rewrap / \(U_II_I (These x e)) ->
--   yoneda @Straight x (U_II_I `compose` (\x_ -> These (from x_) e))

-- TODO: to fix
instance Mapping Straight Straight AR AR
 (U_I_II (U_I_UU_II_I AR LM) e)
 (U_I_II (U_I_UU_II_I AR LM) e) where
 mapping = rewrap / \from -> rewrap `compose` rewrap / \f x ->
  i_ (map @Straight @Straight from) (f x)

-- TODO: it doesn't work correctly?
instance Mapping Straight Straight
 (U_I_UU_II_I AR LM) AR
 (U_I_II (U_I_UU_II_I AR LM) e)
 (U_I_II (U_I_UU_II_I AR LM) e) where
 mapping = rewrap / \(U_I_UU_II_I from)
  -> rewrap `compose` rewrap / \trstn e ->
   let These old e' = trstn e in
   let These new _ = from old in
   These new e'

-- TODO: it doesn't work correctly?
instance Mapping Opposite Straight
 (U_I_UU_II_I AR LM) AR
 (U_II_I (U_I_UU_II_I AR LM) e)
 (U_II_I (U_I_UU_II_I AR LM) e) where
 mapping = rewrap / \(U_I_UU_II_I from)
  -> rewrap `compose` rewrap / \trstn new ->
   let These old new' = from new in
   let These e old' = trstn old in
   These e new'

instance Category (U_I_UU_II_I AR LM) where
 identity = U_I_UU_II_I (\e -> These e e)

instance Mapping Straight Straight AR AR
 (UU_V_U_I_II_T_II Straight AR AR t e)
 (UU_V_U_I_II_T_II Straight AR AR t e) where
 mapping = rewrap / \from -> rewrap (`compose` (rewrap (`compose` from)))

instance Mapping Opposite Straight AR AR
 (UU_V_U_I_II_T_II Opposite AR AR t e)
 (UU_V_U_I_II_T_II Opposite AR AR t e) where
 mapping = rewrap / \from -> rewrap (`compose` (rewrap (compose from)))

-- TODO: implement `mapping` method
-- instance Mapping Straight Straight (W_I_II_II (U_I_UU_III_U_II_I (->) LM)) (->)
--  (UU_V_U_I_II_T_II Straight (W_I_II_II (U_I_UU_III_U_II_I (->) LM)) (->) (Straight (W_I_II_II (U_I_UU_III_U_II_I (->) LM)) ee) e)
--  (UU_V_U_I_II_T_II Straight (W_I_II_II (U_I_UU_III_U_II_I (->) LM)) (->) (Straight (W_I_II_II (U_I_UU_III_U_II_I (->) LM)) ee) e)

-- TODO: implement `mapping` method
-- instance Mapping Opposite Straight (U_I_UU_II_I (->) LM)) (->)
--  (UU_V_U_I_II_T_II Opposite (W_I_II_II (U_I_UU_III_U_II_I (->) LM)) (->) (Opposite (U_I_UU_II_I (->) LM)) ee) e)
--  (UU_V_U_I_II_T_II Opposite (W_I_II_II (U_I_UU_III_U_II_I (->) LM)) (->) (Opposite (U_I_UU_II_I (->) LM)) ee) e)

instance
 ( forall e . Covariant Semi Functor from into (Straight (U_I_T_II t u) e)
 , forall e . Covariant Semi Functor from into (Opposite (U_I_T_II t u) e)
 , forall e . Covariant Endo Semi Functor from (Straight (U_I_T_II t u) e)
 , forall e . Covariant Endo Semi Functor from (Opposite (U_I_T_II t u) e)
 , forall e . Wrapper from (R_U_I_T_I u t e)
 , forall e . Wrapper into (R_U_I_T_I u t e)
 , forall e . Wrapper from (Recursive (U_I_T_II t u e))
 , forall e . Wrapper into (Recursive (U_I_T_II t u e))
 , forall e ee . Wrapper from (Opposite (U_I_T_II t u) e ee)
 , forall e ee . Wrapper into (Opposite (U_I_T_II t u) e ee)
 , forall e ee . Wrapper from (Straight (U_I_T_II t u) e ee)
 , forall e ee . Wrapper into (Straight (U_I_T_II t u) e ee)
 ) => Mapping Straight Straight from into (R_U_I_T_I u t) (R_U_I_T_I u t) where
 mapping = rewrap / \from ->
  wrap @into @(R_U_I_T_I u t _)
  `compose` wrap @into @(Recursive _)
  `compose` unwrap @into @(Opposite _ _ _)
  `compose` map @Straight @Straight @_ @_ from
  `compose` wrap @into @(Opposite _ _ _)
  `compose` unwrap @into @(Straight _ _ _)
  `compose` map @Straight @Straight @from @into @(U_I_II (U_I_T_II t u) _) @(U_I_II (U_I_T_II t u) _)
   (unwrap @from
   `compose` map @Straight @Straight @from @_ @(R_U_I_T_I u t) @(R_U_I_T_I u t) from
   `compose` wrap @from @(R_U_I_T_I u t _))
  `compose` wrap @into @(Straight _ _ _)
  `compose` unwrap @into @(Recursive _)
  `compose` unwrap @into @(R_U_I_T_I u t _)

instance {-# OVERLAPPABLE #-} Mapping Straight Straight AR AR (U_I_II AR a) (U_I_II AR a) where
 mapping (Straight from) = Straight / \(Straight between) -> Straight (\x -> from (between x))

instance Mapping Opposite Straight AR AR (U_II_I AR o) (U_II_I AR o) where
 mapping (U_II_I from) = Straight / \(U_II_I between) -> U_II_I (\x -> between (from x))

instance Category AR where
 identity = \x -> x

instance Mapping U_I_II Straight AR into t tt
 => Mapping U_1_I Straight AR into t tt where
  mapping (U_1_I f) = mapping (Straight (f `compose` terminal))

-- instance Mapping Straight Straight AR AR (U_1_I (->) e) (U_1_I (->) e) where
--  mapping = rewrap / \from (U_1_I x) -> U_1_I / from x

instance Mapping Straight Straight AR AR I (U_I_II AR e) where
 mapping = rewrap / \from (Identity x) -> U_I_II / \_ -> from x

instance Mapping Straight Straight AR AR I (U_I_I LM) where
 mapping (Straight from) = Straight / \(Identity x) -> U_I_I (These (from x) (from x))

-- TODO: redefine using limits
instance Mapping Straight Straight AR AR (U_I_I LM) (U_I_I LM) where
 mapping (Straight from) = Straight / \(U_I_I (These x y)) -> U_I_I (These (from x) (from y))

instance Mapping Straight Straight AR AR (U_I_II LM e) I where
 mapping (Straight from) = Straight / \(Straight (These _ x)) -> Identity (from x)

instance Mapping Straight Straight AR AR (Opposite LM e) I where
 mapping (Straight from) = Straight / \(U_II_I (These x _)) -> Identity (from x)

instance Mapping Straight Straight AR AR (U_I_I ML) I where
 mapping (Straight from) = Straight / \case
  U_I_I (This x) -> Identity (from x)
  U_I_I (That x) -> Identity (from x)

instance Mapping Straight Straight AR AR I (Straight ML e) where
 mapping (Straight from) = Straight / \(Identity x) -> Straight (That (from x))

instance Mapping Straight Straight AR AR I (Opposite ML e) where
 mapping (Straight from) = Straight / \(Identity x) -> U_II_I (This (from x))

instance Mapping Straight Straight (U_I_UU_II_U_II_I AR LM) AR
 (Straight (U_I_UU_II_U_II_I AR LM) origin)
 (Straight (U_I_UU_II_U_II_I AR LM) origin) where
 mapping = rewrap / \into -> rewrap `compose` rewrap / \from origin ->
  let These source source_origin = from origin in
  let These target target_source = (unwrap `compose` unwrap) into source in
  These target (source_origin `compose` target_source)

instance Mapping Opposite Straight (U_I_UU_II_U_II_I AR LM) AR
 (Opposite (U_I_UU_II_U_II_I AR LM) origin)
 (Opposite (U_I_UU_II_U_II_I AR LM) origin) where
 mapping = rewrap / \from -> rewrap `compose` rewrap `compose` rewrap / \into origin ->
  let These source source_origin = (unwrap `compose` unwrap) from origin in
  let These target target_source = into source in
  These target (source_origin `compose` target_source)

instance Category (U_I_UU_II_U_II_I AR LM) where
 identity = U_I_UU_II_U_II_I / \x -> These x identity

-- instance Mapping Straight Straight
 -- (W_I_II_II (U_I_UU_III_U_II_I (->) LM))
 -- (W_I_II_II (U_I_UU_III_U_II_I (->) LM))
 -- (This LM e) Identity where
 -- mapping = rewrap `compose` rewrap `compose` rewrap /
  -- \from (U_II_I (These old e)) -> These 
   -- (Identity (wrapped (left @Straight @(->) identity) (from old)))
   -- (\(Identity new) -> U_II_I (These ((wrapped (right @Straight @(->) identity) (from old)) new) e))

-- instance Mapping Straight Straight
 -- (W_I_II_II (U_I_UU_III_U_II_I (->) LM))
 -- (W_I_II_II (U_I_UU_III_U_II_I (->) LM))
 -- (That LM e) Identity where
 -- mapping = rewrap `compose` rewrap `compose` rewrap /
  -- -- \from (Straight (These e old)) -> These 
   -- / Identity (wrapped (left @Straight @(->) identity) (from old))
   -- / \(Identity new) -> Straight (These e ((wrapped (right @Straight @(->) identity) (from old)) new))

-- instance Mapping Straight Straight (W_I_II_II (U_I_UU_III_U_II_I (->) LM)) (->) Identity (U_I_I LM) where
 -- mapping = rewrap / \(W_I_II_II (U_I_UU_III_U_II_I from)) (Identity old) -> U_I_I / These
  -- (wrapped (left @Straight @(->) identity) (from old))
  -- (wrapped (left @Straight @(->) identity) (from old))

-- instance Mapping Opposite Straight (W_I_II_II (U_I_UU_III_U_II_I (->) LM)) (->) (This (->) e) (This (->) e) where
 -- mapping = rewrap / \(W_I_II_II (U_I_UU_III_U_II_I from)) ->
  -- map @Opposite @Straight / (\(These x _) -> x) `compose` from

instance Mapping Straight Straight AR AR (Day Straight AR LM LM I I e ee) I where
 mapping = rewrap / \from -> rewrap / \case
  These (These (Identity e) (Identity ee)) (Straight f) -> from (f (These e ee))

instance Mapping Straight Straight AR AR (U_I_II AR Unit) I where
 mapping = rewrap / \from (Straight f) -> Identity (from (f Unit))

instance Mapping Straight Straight AR AR (Day Straight AR LM LM (U_II_I ML e) (U_II_I ML e) ee eee) (U_II_I ML e) where
 mapping = rewrap / \from -> rewrap / \case
  These (These (U_II_I (This ee)) (U_II_I (This eee))) (Straight f) -> This (from (f (These ee eee)))
  These (These (U_II_I (That e)) _) _ -> That e

instance Mapping Straight Straight AR AR (U_I_II AR Unit) (U_II_I ML e) where
 mapping = rewrap / \from (Straight f) -> U_II_I (This (from (f Unit)))

instance Mapping Straight Straight AR AR (Day Straight AR LM LM (U_I_II ML e) (U_I_II ML e) ee eee) (U_I_II ML e) where
 mapping = rewrap / \from -> rewrap / \case
  These (These (U_I_II (That ee)) (U_I_II (That eee))) (U_I_II f) -> That (from (f (These ee eee)))
  These (These (U_I_II (This e)) _) (U_I_II _) -> This e
  These (These _ (U_I_II (This e))) (U_I_II _) -> This e

instance Mapping Straight Straight AR AR
  (Day Straight AR LM MLM (U_I_II ML e) (U_I_II ML e) ee eee) (U_I_II ML e) where
 mapping = rewrap / \from -> rewrap / \case
  These (These (U_I_II (That ee)) (U_I_II (That eee))) (U_I_II f) ->
   That `compose` from `compose` f `compose` U_U_I_II_UU_I_II `compose` That / These ee eee
  These (These (U_I_II (That ee)) _) (U_I_II f) ->
   That `compose` from `compose` f `compose` U_U_I_II_UU_I_II `compose` This / This ee
  These (These (U_I_II (This _)) (U_I_II (That eee))) (U_I_II f) ->
   That `compose` from `compose` f `compose` U_U_I_II_UU_I_II `compose` This / That eee
  These (These (U_I_II (This e)) (U_I_II (This _))) (U_I_II _) ->
   This e

instance Mapping Straight Straight AR AR (U_I_II AR Unit) (U_I_II ML e) where
 mapping = rewrap / \from (Straight f) -> Straight (That (from (f Unit)))

instance Mapping Straight Straight AR AR
  (Day Straight AR LM ML (U_I_II ML e) (U_I_II ML e) ee eee) (U_I_II ML e) where
 mapping = rewrap / \from -> rewrap / \case
  These (These (U_I_II (That ee)) _) (U_I_II f) -> That (from (f (This ee)))
  These (These _ (U_I_II (That eee))) (U_I_II f) -> That (from (f (That eee)))
  These (These _ (U_I_II (This eee))) (U_I_II _) -> This eee

instance Mapping Straight Straight AR AR (U_I_II AR Void) (U_II_I ML Unit) where
 mapping = rewrap / \_ _ -> U_II_I (That Unit)

instance Mapping Straight Straight AR AR
  (Day Straight AR LM ML (U_II_I ML e) (U_II_I ML e) ee eee) (U_II_I ML e) where
 mapping = rewrap / \from -> rewrap / \case
  These (These (U_II_I (This ee)) _) (U_I_II f) -> This (from (f (This ee)))
  These (These _ (U_II_I (This eee))) (U_I_II f) -> This (from (f (That eee)))
  These (These _ (U_II_I (That eee))) _ -> That eee

instance Mapping Straight Straight AR AR (U_I_II AR Void) (U_I_II ML Unit) where
 mapping = rewrap / \_ _ -> U_I_II (This Unit)

instance Mapping Straight Straight AR AR (U_I_II AR (ML Unit Unit)) (U_I_I LM) where
 mapping = rewrap / \from -> rewrap / \f -> These
  (from `compose` f / This Unit)
  (from `compose` f / That Unit)

instance Mapping Straight Straight AR AR (U_I_I LM) (U_I_II AR (ML Unit Unit)) where
 mapping = rewrap / \from -> rewrap / \(These x y) -> \case
  This _ -> from x
  That _ -> from y

-- instance Mapping Straight Straight
 -- (W_I_II_II (U_I_UU_III_U_II_I (->) LM))
 -- (W_I_II_II (U_I_UU_III_U_II_I (->) LM))
 -- (U_I_I LM) (U_I_II (->) (ML Unit Unit)) where
 -- mapping = rewrap `compose` rewrap `compose` rewrap / \from (U_I_I (These x y)) -> These
  -- / U_I_II (\case { This Unit -> this (from x); That Unit -> this (from y) })
  -- / \(U_I_II f) -> U_I_I (These
   -- / that (from x) (f (This Unit))
   -- / that (from x) (f (That Unit))
   -- )

-- instance Mapping Straight Straight
 -- (W_I_II_II (U_I_UU_III_U_II_I (->) LM))
 -- (W_I_II_II (U_I_UU_III_U_II_I (->) LM))
 -- (U_I_II (->) (ML Unit Unit)) (U_I_I LM) where
 -- mapping = rewrap `compose` rewrap `compose` rewrap / \from (U_I_II f) -> These
  -- / U_I_I (These / this (from (f (This Unit))) / this (from (f (That Unit))))
  -- / \(U_I_I (These x y)) -> U_I_II / \case
   -- This Unit -> that (from (f (This Unit))) x
   -- That Unit -> that (from (f (That Unit))) y

-- instance Mapping Straight Straight AR AR
  -- (Day U_I_II AR LM ML (U_I_I LM `T'TT'I` t) (U_I_I LM `T'TT'I` t) ee eee) (U_I_I LM `T'TT'I` t)

-- instance Monoidal Straight Functor AR LM ML t
 -- => Mapping Straight Straight AR AR (U_I_II AR Void) (U_I_I LM `T'TT'I` t) where
 -- mapping = rewrap / \_ _ -> T'TT'I `compose` U_I_I / These
  -- (map @Straight @Straight @AR @AR @t @t initial empty)
  -- (map @Straight @Straight @AR @AR @t @t initial empty)

-- instance Mapping Straight Straight (->) (->)
--  (W_III_I_II (U_I_UU_II_III (->) LM) e ee)
--  (W_III_I_II (U_I_UU_II_III (->) LM) e ee) where
--  mapping = rewrap / \from -> rewrap `compose` rewrap / \f x -> i_ (map @Straight @Straight from) (f x)
