{-# OPTIONS_GHC -fno-warn-orphans #-}
{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE UndecidableInstances #-}
module Ya.Algebra.Instances where

import Ya.Algebra.Abstract
import Ya.Algebra.Definition

instance (Precategory into, forall e . Wrapper into (I e)) 
 => Mapping T'I'II T'I'II into into I I where
 mapping = rewrap rewrap

instance
 ( forall e . Wrapper into (I e)
 , forall e . Wrapper into (l `L` ll `L` t `T'I` e)
 , forall e . Wrapper into (ll `L` t `T'I` e)
 , forall e . Wrapper into (I `TT'T'I` t `T'I_` e)
 , forall e . Wrapper into (I `T'TT'I` l `L` ll `L` t `T'I_` e)
 , Covariant Endo Semi Functor into t
 ) => Mapping T'I'II T'I'II into into (I `T'TT'I` l `L` ll `L` t) (I `TT'T'I` t) where
 mapping = rewrap / \from -> rewrap /
  map @T'I'II @T'I'II @into @into (wrap @into @(I _) `compose` from) `compose` unwrap @into @(L ll t _) `compose` unwrap @into @(L l _ _) `compose` unwrap @into @(I _)

instance
 ( Covariant Semi Functor from into tt
 , Covariant Endo Semi Functor into t
 , forall e . Wrapper into (t `T'TT'I` tt `T'I_` e)
 ) => Mapping T'I'II T'I'II from into (t `T'TT'I` tt) (t `T'TT'I` tt) where
 mapping = rewrap / \from -> wrap @into `compose` (map @T'I'II @T'I'II @into @into `compose` map @T'I'II @T'I'II @from @into) from `compose` unwrap @into

instance
 ( Covariant Semi Functor from into t
 , Covariant Endo Semi Functor into tt
 , forall e . Wrapper into (t `TT'T'I` tt `T'I_` e)
 ) => Mapping T'I'II T'I'II from into (t `TT'T'I` tt) (t `TT'T'I` tt) where
 mapping = rewrap / \from -> wrap @into `compose` (map @T'I'II @T'I'II @into @into `compose` map @T'I'II @T'I'II @from @into) from `compose` unwrap @into

instance
 ( Covariant Semi Functor from into t
 , forall e . Wrapper into (l `L` t `T'I` e)
 ) => Mapping T'I'II T'I'II from into (l `L` t) (l `L` t) where
 mapping = rewrap / \from -> rewrap (map @T'I'II @T'I'II @from @into @t from)

instance
 ( Covariant Semi Functor from into t
 , forall ee . Covariant Endo Semi Functor into (T'I'II u ee)
 , forall ee . Wrapper into (T'I'II (U_I_T_II t u) e ee)
 , forall ee . Wrapper into (U_I_T_II t u e ee)
 , forall ee . Wrapper into (T'I'II u e (t ee))
 ) => Mapping T'I'II T'I'II from into (T'I'II (U_I_T_II t u) e) (T'I'II (U_I_T_II t u) e) where
 mapping = rewrap / \from ->
  wrap @into @(T'I'II _ _ _)
  `compose` wrap @into @(U_I_T_II _ _ _ _)
  `compose` unwrap @into @(T'I'II _ _ _)
  `compose` map @T'I'II @T'I'II @into @into (map @T'I'II @T'I'II @from @into from)
  `compose` wrap @into @(T'I'II _ _ _)
  `compose` unwrap @into @(U_I_T_II _ _ _ _)
  `compose` unwrap @into @(T'I'II _ _ _)

instance
 ( forall ee . Covariant Semi Functor from into (U_II_I u ee)
 , forall ee . Wrapper into (U_II_I (U_I_T_II t u) e ee)
 , forall ee . Wrapper into (U_I_T_II t u ee e)
 , forall ee . Wrapper into (U_II_I u (t e) ee)
 ) => Mapping T'I'II T'I'II from into (U_II_I (U_I_T_II t u) e) (U_II_I (U_I_T_II t u) e) where
 mapping = rewrap / \from ->
  wrap @into @(U_II_I _ _ _)
  `compose` wrap @into @(U_I_T_II _ _ _ _)
  `compose` unwrap @into @(U_II_I _ _ _)
  `compose` map @T'I'II @T'I'II @from @into from
  `compose` wrap @into @(U_II_I _ _ _)
  `compose` unwrap @into @(U_I_T_II _ _ _ _)
  `compose` unwrap @into @(U_II_I _ _ _)

instance
 ( Covariant Semi Functor from into h
 , Covariant Endo Semi Functor into tt
 , Covariant Endo Semi Functor into t
 , forall e . Wrapper into (T'TTT'TT'I t h tt e)
 ) => Mapping T'I'II T'I'II from into (T'TTT'TT'I t h tt) (T'TTT'TT'I t h tt) where
 mapping = rewrap / \from -> wrap @into
  `compose` (map @T'I'II @T'I'II @into @into
   `compose` map @T'I'II @T'I'II @into @into
   `compose` map @T'I'II @T'I'II @from @into
   ) from
  `compose` unwrap @into

instance
 ( forall e . Covariant Endo Semi Functor into (T'I'II u (t e))
 , forall e . Covariant Endo Semi Functor into (U_II_I u (tt e))
 , Covariant Semi Functor from into tt
 , Covariant Semi Functor from into t
 , forall e . Wrapper into (U_T_I_TT_I u t tt e)
 , forall e ee . Wrapper into (T'I'II u (t e) (tt ee))
 , forall e ee . Wrapper into (U_II_I u (tt e) (t ee))
 ) => Mapping T'I'II T'I'II from into (U_T_I_TT_I u t tt) (U_T_I_TT_I u t tt) where
 mapping = rewrap / \from -> rewrap /
  i_ (map @T'I'II @T'I'II @into @into `compose` map @T'I'II @T'I'II @from @into @t @t / from) `compose`
  _i (map @T'I'II @T'I'II @into @into `compose` map @T'I'II @T'I'II @from @into @tt @tt / from)

-- instance
 -- ( forall e . Covariant Endo Semi Functor AR (T'I'II u e)
 -- , forall e . Covariant Endo Semi Functor AR (U_II_I u e)
 -- , Covariant Monoidal Functor from AR u u Unit ttt
 -- , Covariant Transformation Functor from AR (t `T'TT'I` ttt) (t `TT'T'I` ttt)
 -- , Covariant Transformation Functor from AR (tt `T'TT'I` ttt) (tt `TT'T'I` ttt)
 -- , forall e . Wrapper from (U_T_I_TT_I u t tt e)
 -- , forall e . Wrapper AR (TT'T'I (U_T_I_TT_I u t tt) ttt e)
 -- , forall e . Wrapper AR (T'TT'I (U_T_I_TT_I u t tt) ttt e)
 -- ) => Mapping T'I'II T'I'II from AR (U_T_I_TT_I u t tt `T'TT'I` ttt) (U_T_I_TT_I u t tt `TT'T'I` ttt) where
 -- mapping = rewrap / \from -> rewrap /
  -- day @T'I'II @from @Unit @ttt @u @u (wrap @_ @(U_T_I_TT_I u t tt _)) identity
   -- `compose` i_ (map @T'I'II @T'I'II @AR @AR (wrapped (map @T'I'II @T'I'II @from @AR @(t `T'TT'I` ttt) @(t `TT'T'I` ttt) from)))
   -- `compose` _i (map @T'I'II @T'I'II @AR @AR (wrapped (map @T'I'II @T'I'II @from @AR @(tt `T'TT'I` ttt) @(tt `TT'T'I` ttt) from)))
   -- `compose` unwrap @AR @(U_T_I_TT_I u t tt _)

-- TODO: here should be a generalized version of an instance above
-- instance
 -- ( forall e . Covariant Endo Semi Functor into (T'I'II (u :: * -> * -> *) (t e))
 -- , forall e . Wrapper into (U_T_I_TT_I u t tt e)
 -- , forall e . Wrapper into (TT'T'I (U_T_I_TT_I u t tt) ttt e)
 -- , forall e . Wrapper into (T'TT'I (U_T_I_TT_I u t tt) ttt e)
 -- ) => Mapping T'I'II T'I'II from into (U_T_I_TT_I u t tt `T'TT'I` ttt) (U_T_I_TT_I u t tt `TT'T'I` ttt where
 -- mapping = rewrap / \from -> rewrap /
  -- day_ @T'I'II @from @from @ttt @u @u (wrap @_ @(U_T_I_TT_I u t tt _)) identity `compose`
   -- wrapped (map @T'I'II @into @into @(U_II_I u _)
    -- (wrapped (map @T'I'II @T'I'II @from @into @(t `T'TT'I` ttt) @(t `TT'T'I` ttt) from))) `compose`
   -- wrapped (map @T'I'II @into @into @(T'I'II u _)
    -- (wrapped (map @T'I'II @T'I'II @from @into @(tt `T'TT'I` ttt) @(tt `TT'T'I` ttt) from))) `compose`
   -- unwrap @into @(U_T_I_TT_I u t tt _)

instance Mapping T'I'II T'I'II AR AR (T'I'II P e `T'TT'I` T'I'II AR e) I where
 mapping = rewrap / \from -> rewrap / \(T'I'II (These e (T'I'II f))) -> from (f e)

instance Mapping T'I'II T'I'II AR AR I (T'I'II AR e `T'TT'I` T'I'II P e) where
 mapping = rewrap / \from -> rewrap / \x -> T'I'II / \e -> T'I'II (These e (from x))

instance Mapping T'I'II T'I'II AR AR I (T'I'II AR e `T'TT'I` U_II_I P e) where
 mapping = rewrap / \from -> rewrap / \x -> T'I'II / \e -> U_II_I (These (from x) e)

instance Mapping T'I'II T'I'II AR AR (U_II_I P e `T'TT'I` T'I'II AR e) I where
 mapping = rewrap / \from -> rewrap / \(U_II_I (These (T'I'II f) e)) -> from (f e)

instance Mapping T'I'II T'I'II AR AR (T'I'II P e) (T'I'II P e) where
 mapping = rewrap / \from -> rewrap / \case
  These e x -> These e (from x)

instance Mapping T'I'II T'I'II AR AR (U_II_I P o) (U_II_I P o) where
 mapping = rewrap / \from -> rewrap / \case
  These x e -> These (from x) e

instance Mapping T'I'II T'I'II AR AR (T'I'II S o) (T'I'II S o) where
 mapping = rewrap / \from -> rewrap / \case
  That x -> That (from x)
  This e -> This e

instance Mapping T'I'II T'I'II AR AR (U_II_I S o) (U_II_I S o) where
 mapping = rewrap / \from -> rewrap / \case
  This x -> This (from x)
  That e -> That e

-- instance
 -- ( Covariant Semi Functor from AR t
 -- , Covariant Functor from from (U_I_I u)
 -- , Covariant Monoidal Functor from AR u u t
 -- , forall e . Elicitable U_II_I from (U_I_I u e)
 -- ) => Mapping T'I'II T'I'II from AR (U_I_I u `T'TT'I` t) (U_I_I u `TT'T'I` t) where
 -- mapping = rewrap / \from -> rewrap /
  -- day @T'I'II @from @t @u @u
   -- (map @T'I'II @T'I'II from `compose` wrap @from @(U_I_I _ _)) identity
  -- `compose` unwrap @AR @(U_I_I u _)

-- instance
 -- ( Covariant Semi Functor AR AR t
 -- , Covariant Functor AR AR (U_I_I u)
 -- , Covariant Endo Monoidal Functor AR u u tt
 -- , Mapping T'I'II T'I'II AR AR (t `T'TT'I` tt) (t `TT'T'I` tt)
 -- ) => Mapping T'I'II T'I'II AR AR
  -- ((U_I_I u `T'TT'I` t) `T'TT'I` tt)
  -- ((U_I_I u `T'TT'I` t) `TT'T'I` tt) where
 -- mapping = rewrap / \from -> rewrap /
  -- map @T'I'II @T'I'II @AR @AR (wrap @_ @(U_I_I u `T'TT'I` t `T'I` _)) `compose`
  -- wrapped (component @AR @(U_I_I u `T'TT'I` tt) @(U_I_I u `TT'T'I` tt)) `compose`
  -- map @T'I'II @T'I'II @AR @AR @(U_I_I u)
   -- (wrapped / map @T'I'II @T'I'II @AR @AR @(t `T'TT'I` tt) @(t `TT'T'I` tt) from) `compose`
  -- unwrap @AR

-- instance Covariant Yoneda AR AR tt =>
--  Mapping T'I'II T'I'II AR AR (U_II_I P e `T'TT'I` tt) (U_II_I P e `TT'T'I` tt) where
--  mapping = rewrap / \from -> rewrap / \(U_II_I (These x e)) ->
--   yoneda @T'I'II x (U_II_I `compose` (\x_ -> These (from x_) e))

-- TODO: to fix
instance Mapping T'I'II T'I'II AR AR
 (T'I'II (U_I_UU_II_I AR P) e)
 (T'I'II (U_I_UU_II_I AR P) e) where
 mapping = rewrap / \from -> rewrap `compose` rewrap / \f x ->
  i_ (map @T'I'II @T'I'II from) (f x)

-- TODO: it doesn't work correctly?
instance Mapping T'I'II T'I'II
 (U_I_UU_II_I AR P) AR
 (T'I'II (U_I_UU_II_I AR P) e)
 (T'I'II (U_I_UU_II_I AR P) e) where
 mapping = rewrap / \(U_I_UU_II_I from)
  -> rewrap `compose` rewrap / \trstn e ->
   let These old e' = trstn e in
   let These new _ = from old in
   These new e'

-- TODO: it doesn't work correctly?
instance Mapping U_II_I T'I'II
 (U_I_UU_II_I AR P) AR
 (U_II_I (U_I_UU_II_I AR P) e)
 (U_II_I (U_I_UU_II_I AR P) e) where
 mapping = rewrap / \(U_I_UU_II_I from)
  -> rewrap `compose` rewrap / \trstn new ->
   let These old new' = from new in
   let These e old' = trstn old in
   These e new'

instance Category (U_I_UU_II_I AR P) where
 identity = U_I_UU_II_I (\e -> These e e)

instance Mapping T'I'II T'I'II AR AR
 (UU_V_T'I'II_T_II T'I'II AR AR t e)
 (UU_V_T'I'II_T_II T'I'II AR AR t e) where
 mapping = rewrap / \from -> rewrap (`compose` (rewrap (`compose` from)))

instance Mapping U_II_I T'I'II AR AR
 (UU_V_T'I'II_T_II U_II_I AR AR t e)
 (UU_V_T'I'II_T_II U_II_I AR AR t e) where
 mapping = rewrap / \from -> rewrap (`compose` (rewrap (compose from)))

-- TODO: implement `mapping` method
-- instance Mapping T'I'II T'I'II (W_I_II_II (U_I_UU_III_U_II_I (->) P)) (->)
--  (UU_V_T'I'II_T_II T'I'II (W_I_II_II (U_I_UU_III_U_II_I (->) P)) (->) (T'I'II (W_I_II_II (U_I_UU_III_U_II_I (->) P)) ee) e)
--  (UU_V_T'I'II_T_II T'I'II (W_I_II_II (U_I_UU_III_U_II_I (->) P)) (->) (T'I'II (W_I_II_II (U_I_UU_III_U_II_I (->) P)) ee) e)

-- TODO: implement `mapping` method
-- instance Mapping U_II_I T'I'II (U_I_UU_II_I (->) P)) (->)
--  (UU_V_T'I'II_T_II U_II_I (W_I_II_II (U_I_UU_III_U_II_I (->) P)) (->) (U_II_I (U_I_UU_II_I (->) P)) ee) e)
--  (UU_V_T'I'II_T_II U_II_I (W_I_II_II (U_I_UU_III_U_II_I (->) P)) (->) (U_II_I (U_I_UU_II_I (->) P)) ee) e)

instance
 ( forall e . Covariant Semi Functor from into (T'I'II (U_I_T_II t u) e)
 , forall e . Covariant Semi Functor from into (U_II_I (U_I_T_II t u) e)
 , forall e . Covariant Endo Semi Functor from (T'I'II (U_I_T_II t u) e)
 , forall e . Covariant Endo Semi Functor from (U_II_I (U_I_T_II t u) e)
 , forall e . Wrapper from (R_U_I_T_I u t e)
 , forall e . Wrapper into (R_U_I_T_I u t e)
 , forall e . Wrapper from (Recursive (U_I_T_II t u e))
 , forall e . Wrapper into (Recursive (U_I_T_II t u e))
 , forall e ee . Wrapper from (U_II_I (U_I_T_II t u) e ee)
 , forall e ee . Wrapper into (U_II_I (U_I_T_II t u) e ee)
 , forall e ee . Wrapper from (T'I'II (U_I_T_II t u) e ee)
 , forall e ee . Wrapper into (T'I'II (U_I_T_II t u) e ee)
 ) => Mapping T'I'II T'I'II from into (R_U_I_T_I u t) (R_U_I_T_I u t) where
 mapping = rewrap / \from ->
  wrap @into @(R_U_I_T_I u t _)
  `compose` wrap @into @(Recursive _)
  `compose` unwrap @into @(U_II_I _ _ _)
  `compose` map @T'I'II @T'I'II @_ @_ from
  `compose` wrap @into @(U_II_I _ _ _)
  `compose` unwrap @into @(T'I'II _ _ _)
  `compose` map @T'I'II @T'I'II @from @into @(T'I'II (U_I_T_II t u) _) @(T'I'II (U_I_T_II t u) _)
   (unwrap @from
   `compose` map @T'I'II @T'I'II @from @_ @(R_U_I_T_I u t) @(R_U_I_T_I u t) from
   `compose` wrap @from @(R_U_I_T_I u t _))
  `compose` wrap @into @(T'I'II _ _ _)
  `compose` unwrap @into @(Recursive _)
  `compose` unwrap @into @(R_U_I_T_I u t _)

instance {-# OVERLAPPABLE #-} Mapping T'I'II T'I'II AR AR (T'I'II AR a) (T'I'II AR a) where
 mapping (T'I'II from) = T'I'II / \(T'I'II between) -> T'I'II (\x -> from (between x))

instance Mapping U_II_I T'I'II AR AR (U_II_I AR o) (U_II_I AR o) where
 mapping (U_II_I from) = T'I'II / \(U_II_I between) -> U_II_I (\x -> between (from x))

instance Category AR where
 identity = \x -> x

instance Mapping T'I'II T'I'II AR into t tt
 => Mapping U_1_I T'I'II AR into t tt where
  mapping (U_1_I f) = mapping (T'I'II (f `compose` terminal))

-- instance Mapping T'I'II T'I'II AR AR (U_1_I (->) e) (U_1_I (->) e) where
--  mapping = rewrap / \from (U_1_I x) -> U_1_I / from x

instance Mapping T'I'II T'I'II AR AR I (T'I'II AR e) where
 mapping = rewrap / \from (Identity x) -> T'I'II / \_ -> from x

instance Mapping T'I'II T'I'II AR AR I (U_I_I P) where
 mapping (T'I'II from) = T'I'II / \(Identity x) -> U_I_I (These (from x) (from x))

-- TODO: redefine using limits
instance Mapping T'I'II T'I'II AR AR (U_I_I P) (U_I_I P) where
 mapping (T'I'II from) = T'I'II / \(U_I_I (These x y)) -> U_I_I (These (from x) (from y))

instance Mapping T'I'II T'I'II AR AR (T'I'II P e) I where
 mapping (T'I'II from) = T'I'II / \(T'I'II (These _ x)) -> Identity (from x)

instance Mapping T'I'II T'I'II AR AR (U_II_I P e) I where
 mapping (T'I'II from) = T'I'II / \(U_II_I (These x _)) -> Identity (from x)

instance Mapping T'I'II T'I'II AR AR (U_I_I S) I where
 mapping (T'I'II from) = T'I'II / \case
  U_I_I (This x) -> Identity (from x)
  U_I_I (That x) -> Identity (from x)

instance Mapping T'I'II T'I'II AR AR I (T'I'II S e) where
 mapping (T'I'II from) = T'I'II / \(Identity x) -> T'I'II (That (from x))

instance Mapping T'I'II T'I'II AR AR I (U_II_I S e) where
 mapping (T'I'II from) = T'I'II / \(Identity x) -> U_II_I (This (from x))

instance Mapping T'I'II T'I'II AT AR (T'I'II AT origin) (T'I'II AT origin) where
 mapping = rewrap / \into -> rewrap `compose` rewrap / \from origin ->
  let These source source_origin = from origin in
  let These target target_source = unwrap into source in
  These target (source_origin `compose` target_source)

instance Mapping U_II_I T'I'II AT AR (U_II_I AT origin) (U_II_I AT origin) where
 mapping = rewrap / \from -> rewrap `compose` rewrap / \into origin ->
  let These source source_origin = unwrap from origin in
  let These target target_source = into source in
  These target (source_origin `compose` target_source)

instance Category AT where
 identity = U_I_UU_II_U_II_I / \x -> These x identity

-- instance Mapping T'I'II T'I'II
 -- (W_I_II_II (U_I_UU_III_U_II_I (->) P))
 -- (W_I_II_II (U_I_UU_III_U_II_I (->) P))
 -- (This P e) Identity where
 -- mapping = rewrap `compose` rewrap `compose` rewrap /
  -- \from (U_II_I (These old e)) -> These 
   -- (Identity (wrapped (left @T'I'II @(->) identity) (from old)))
   -- (\(Identity new) -> U_II_I (These ((wrapped (right @T'I'II @(->) identity) (from old)) new) e))

-- instance Mapping T'I'II T'I'II
 -- (W_I_II_II (U_I_UU_III_U_II_I (->) P))
 -- (W_I_II_II (U_I_UU_III_U_II_I (->) P))
 -- (That P e) Identity where
 -- mapping = rewrap `compose` rewrap `compose` rewrap /
  -- -- \from (T'I'II (These e old)) -> These 
   -- / Identity (wrapped (left @T'I'II @(->) identity) (from old))
   -- / \(Identity new) -> T'I'II (These e ((wrapped (right @T'I'II @(->) identity) (from old)) new))

-- instance Mapping T'I'II T'I'II (W_I_II_II (U_I_UU_III_U_II_I (->) P)) (->) Identity (U_I_I P) where
 -- mapping = rewrap / \(W_I_II_II (U_I_UU_III_U_II_I from)) (Identity old) -> U_I_I / These
  -- (wrapped (left @T'I'II @(->) identity) (from old))
  -- (wrapped (left @T'I'II @(->) identity) (from old))

-- instance Mapping U_II_I T'I'II (W_I_II_II (U_I_UU_III_U_II_I (->) P)) (->) (This (->) e) (This (->) e) where
 -- mapping = rewrap / \(W_I_II_II (U_I_UU_III_U_II_I from)) ->
  -- map @U_II_I @T'I'II / (\(These x _) -> x) `compose` from

instance Mapping T'I'II T'I'II AR AR (Day T'I'II AR P P I (Void `L` I) e ee) I where
 mapping = rewrap / \from -> rewrap / \case
  These (These (Identity e) (Labeled (Identity ee))) (T'I'II f) -> from (f (These e ee))

instance Mapping T'I'II T'I'II AR AR (T'I'II AR Unit) I where
 mapping = rewrap / \from (T'I'II f) -> Identity (from (f Unit))

instance Mapping T'I'II T'I'II AR AR (Day T'I'II AR P P (U_II_I S e) (Void `L` U_II_I S e) ee eee) (U_II_I S e) where
 mapping = rewrap / \from -> rewrap / \case
  These (These (U_II_I (This ee)) (Labeled (U_II_I (This eee)))) (T'I'II f) -> This (from (f (These ee eee)))
  These (These (U_II_I (That e)) _) _ -> That e

instance Mapping T'I'II T'I'II AR AR (T'I'II AR Unit) (U_II_I S e) where
 mapping = rewrap / \from (T'I'II f) -> U_II_I (This (from (f Unit)))

instance Mapping T'I'II T'I'II AR AR (Day T'I'II AR P P (T'I'II S e) (Void `L` T'I'II S e) ee eee) (T'I'II S e) where
 mapping = rewrap / \from -> rewrap / \case
  These (These (T'I'II (That ee)) (Labeled (T'I'II (That eee)))) (T'I'II f) -> That (from (f (These ee eee)))
  These (These (T'I'II (This e)) _) _ -> This e
  These (These _ (Labeled (T'I'II (This e)))) _ -> This e

instance Mapping T'I'II T'I'II AR AR (Day T'I'II AR P SP (T'I'II S e) (Void `L` T'I'II S e) ee eee) (T'I'II S e) where
 mapping = rewrap / \from -> rewrap / \case
  These (These (T'I'II (That ee)) (Labeled (T'I'II (That eee)))) (T'I'II f) ->
   That `compose` from `compose` f `compose` U_T'I'II_UT'I'II `compose` That / These ee eee
  These (These (T'I'II (That ee)) _) (T'I'II f) ->
   That `compose` from `compose` f `compose` U_T'I'II_UT'I'II `compose` This / This ee
  These (These (T'I'II (This _)) (Labeled (T'I'II (That eee)))) (T'I'II f) ->
   That `compose` from `compose` f `compose` U_T'I'II_UT'I'II `compose` This / That eee
  These (These (T'I'II (This e)) (Labeled (T'I'II (This _)))) (T'I'II _) ->
   This e

instance Mapping T'I'II T'I'II AR AR (T'I'II AR Unit) (T'I'II S e) where
 mapping = rewrap / \from (T'I'II f) -> T'I'II (That (from (f Unit)))

instance Mapping T'I'II T'I'II AR AR (Day T'I'II AR P S (T'I'II S e) (Void `L` T'I'II S e) ee eee) (T'I'II S e) where
 mapping = rewrap / \from -> rewrap / \case
  These (These (T'I'II (That ee)) _) (T'I'II f) -> That (from (f (This ee)))
  These (These _ (Labeled (T'I'II (That eee)))) (T'I'II f) -> That (from (f (That eee)))
  These (These _ (Labeled (T'I'II (This eee)))) (T'I'II _) -> This eee

instance Mapping T'I'II T'I'II AR AR (T'I'II AR Void) (U_II_I S Unit) where
 mapping = rewrap / \_ _ -> U_II_I (That Unit)

-- instance Mapping T'I'II T'I'II AR AR
--   (Day T'I'II AR P S (U_II_I S e) (U_II_I S e) ee eee) (U_II_I S e) where
--  mapping = rewrap / \from -> rewrap / \case
--   These (These (U_II_I (This ee)) _) (T'I'II f) -> This (from (f (This ee)))
--   These (These _ (U_II_I (This eee))) (T'I'II f) -> This (from (f (That eee)))
--   These (These _ (U_II_I (That eee))) _ -> That eee

instance Mapping T'I'II T'I'II AR AR (T'I'II AR Void) (T'I'II S Unit) where
 mapping = rewrap / \_ _ -> T'I'II (This Unit)

instance Mapping T'I'II T'I'II AR AR (T'I'II AR (S Unit Unit)) (U_I_I P) where
 mapping = rewrap / \from -> rewrap / \f -> These
  (from `compose` f / This Unit)
  (from `compose` f / That Unit)

instance Mapping T'I'II T'I'II AR AR (U_I_I P) (T'I'II AR (S Unit Unit)) where
 mapping = rewrap / \from -> rewrap / \(These x y) -> \case
  This _ -> from x
  That _ -> from y

-- instance Mapping T'I'II T'I'II
 -- (W_I_II_II (U_I_UU_III_U_II_I (->) P))
 -- (W_I_II_II (U_I_UU_III_U_II_I (->) P))
 -- (U_I_I P) (T'I'II (->) (S Unit Unit)) where
 -- mapping = rewrap `compose` rewrap `compose` rewrap / \from (U_I_I (These x y)) -> These
  -- / T'I'II (\case { This Unit -> this (from x); That Unit -> this (from y) })
  -- / \(T'I'II f) -> U_I_I (These
   -- / that (from x) (f (This Unit))
   -- / that (from x) (f (That Unit))
   -- )

-- instance Mapping T'I'II T'I'II
 -- (W_I_II_II (U_I_UU_III_U_II_I (->) P))
 -- (W_I_II_II (U_I_UU_III_U_II_I (->) P))
 -- (T'I'II (->) (S Unit Unit)) (U_I_I P) where
 -- mapping = rewrap `compose` rewrap `compose` rewrap / \from (T'I'II f) -> These
  -- / U_I_I (These / this (from (f (This Unit))) / this (from (f (That Unit))))
  -- / \(U_I_I (These x y)) -> T'I'II / \case
   -- This Unit -> that (from (f (This Unit))) x
   -- That Unit -> that (from (f (That Unit))) y

-- instance Mapping T'I'II T'I'II AR AR
  -- (Day T'I'II AR P S (U_I_I P `T'TT'I` t) (U_I_I P `T'TT'I` t) ee eee) (U_I_I P `T'TT'I` t)

-- instance Monoidal T'I'II Functor AR P S t
 -- => Mapping T'I'II T'I'II AR AR (T'I'II AR Void) (U_I_I P `T'TT'I` t) where
 -- mapping = rewrap / \_ _ -> T'TT'I `compose` U_I_I / These
  -- (map @T'I'II @T'I'II @AR @AR @t @t initial empty)
  -- (map @T'I'II @T'I'II @AR @AR @t @t initial empty)

-- instance Mapping T'I'II T'I'II (->) (->)
--  (W_III_I_II (U_I_UU_II_III (->) P) e ee)
--  (W_III_I_II (U_I_UU_II_III (->) P) e ee) where
--  mapping = rewrap / \from -> rewrap `compose` rewrap / \f x -> i_ (map @T'I'II @T'I'II from) (f x)
