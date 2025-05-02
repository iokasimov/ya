{-# OPTIONS_GHC -fno-warn-orphans #-}
{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE UndecidableInstances #-}
module Ya.Algebra.Instances where

import Ya.Algebra.Abstract
import Ya.Algebra.Definition

instance (Precategory into, forall e . Wrapper into (I e)) 
 => Mapping U_I_II U_I_II into into I I where
 mapping = rewrap rewrap

instance
 ( forall e . Wrapper into (I e)
 , forall e . Wrapper into (l `L` ll `L` t `T'I` e)
 , forall e . Wrapper into (ll `L` t `T'I` e)
 , forall e . Wrapper into (I `TT'T'I` t `T'I_` e)
 , forall e . Wrapper into (I `T'TT'I` l `L` ll `L` t `T'I_` e)
 , Covariant Endo Semi Functor into t
 ) => Mapping U_I_II U_I_II into into (I `T'TT'I` l `L` ll `L` t) (I `TT'T'I` t) where
 mapping = rewrap / \from -> rewrap /
  map @U_I_II @U_I_II @into @into (wrap @into @(I _) `compose` from) `compose` unwrap @into @(L ll t _) `compose` unwrap @into @(L l _ _) `compose` unwrap @into @(I _)

instance
 ( Covariant Semi Functor from into tt
 , Covariant Endo Semi Functor into t
 , forall e . Wrapper into (t `T'TT'I` tt `T'I_` e)
 ) => Mapping U_I_II U_I_II from into (t `T'TT'I` tt) (t `T'TT'I` tt) where
 mapping = rewrap / \from -> wrap @into `compose` (map @U_I_II @U_I_II @into @into `compose` map @U_I_II @U_I_II @from @into) from `compose` unwrap @into

instance
 ( Covariant Semi Functor from into t
 , Covariant Endo Semi Functor into tt
 , forall e . Wrapper into (t `TT'T'I` tt `T'I_` e)
 ) => Mapping U_I_II U_I_II from into (t `TT'T'I` tt) (t `TT'T'I` tt) where
 mapping = rewrap / \from -> wrap @into `compose` (map @U_I_II @U_I_II @into @into `compose` map @U_I_II @U_I_II @from @into) from `compose` unwrap @into

instance
 ( Covariant Semi Functor from into t
 , forall e . Wrapper into (l `L` t `T'I` e)
 ) => Mapping U_I_II U_I_II from into (l `L` t) (l `L` t) where
 mapping = rewrap / \from -> rewrap (map @U_I_II @U_I_II @from @into @t from)

instance
 ( Covariant Semi Functor from into t
 , forall ee . Covariant Endo Semi Functor into (U_I_II u ee)
 , forall ee . Wrapper into (U_I_II (U_I_T_II t u) e ee)
 , forall ee . Wrapper into (U_I_T_II t u e ee)
 , forall ee . Wrapper into (U_I_II u e (t ee))
 ) => Mapping U_I_II U_I_II from into (U_I_II (U_I_T_II t u) e) (U_I_II (U_I_T_II t u) e) where
 mapping = rewrap / \from ->
  wrap @into @(U_I_II _ _ _)
  `compose` wrap @into @(U_I_T_II _ _ _ _)
  `compose` unwrap @into @(U_I_II _ _ _)
  `compose` map @U_I_II @U_I_II @into @into (map @U_I_II @U_I_II @from @into from)
  `compose` wrap @into @(U_I_II _ _ _)
  `compose` unwrap @into @(U_I_T_II _ _ _ _)
  `compose` unwrap @into @(U_I_II _ _ _)

instance
 ( forall ee . Covariant Semi Functor from into (U_II_I u ee)
 , forall ee . Wrapper into (U_II_I (U_I_T_II t u) e ee)
 , forall ee . Wrapper into (U_I_T_II t u ee e)
 , forall ee . Wrapper into (U_II_I u (t e) ee)
 ) => Mapping U_I_II U_I_II from into (U_II_I (U_I_T_II t u) e) (U_II_I (U_I_T_II t u) e) where
 mapping = rewrap / \from ->
  wrap @into @(U_II_I _ _ _)
  `compose` wrap @into @(U_I_T_II _ _ _ _)
  `compose` unwrap @into @(U_II_I _ _ _)
  `compose` map @U_I_II @U_I_II @from @into from
  `compose` wrap @into @(U_II_I _ _ _)
  `compose` unwrap @into @(U_I_T_II _ _ _ _)
  `compose` unwrap @into @(U_II_I _ _ _)

instance
 ( Covariant Semi Functor from into h
 , Covariant Endo Semi Functor into tt
 , Covariant Endo Semi Functor into t
 , forall e . Wrapper into (T'TTT'TT'I t h tt e)
 ) => Mapping U_I_II U_I_II from into (T'TTT'TT'I t h tt) (T'TTT'TT'I t h tt) where
 mapping = rewrap / \from -> wrap @into
  `compose` (map @U_I_II @U_I_II @into @into
   `compose` map @U_I_II @U_I_II @into @into
   `compose` map @U_I_II @U_I_II @from @into
   ) from
  `compose` unwrap @into

instance
 ( forall e . Covariant Endo Semi Functor into (U_I_II u (t e))
 , forall e . Covariant Endo Semi Functor into (U_II_I u (tt e))
 , Covariant Semi Functor from into tt
 , Covariant Semi Functor from into t
 , forall e . Wrapper into (U_T_I_TT_I u t tt e)
 , forall e ee . Wrapper into (U_I_II u (t e) (tt ee))
 , forall e ee . Wrapper into (U_II_I u (tt e) (t ee))
 ) => Mapping U_I_II U_I_II from into (U_T_I_TT_I u t tt) (U_T_I_TT_I u t tt) where
 mapping = rewrap / \from -> rewrap /
  i_ (map @U_I_II @U_I_II @into @into `compose` map @U_I_II @U_I_II @from @into @t @t / from) `compose`
  _i (map @U_I_II @U_I_II @into @into `compose` map @U_I_II @U_I_II @from @into @tt @tt / from)

-- instance
 -- ( forall e . Covariant Endo Semi Functor AR (U_I_II u e)
 -- , forall e . Covariant Endo Semi Functor AR (U_II_I u e)
 -- , Covariant Monoidal Functor from AR u u Unit ttt
 -- , Covariant Transformation Functor from AR (t `T'TT'I` ttt) (t `TT'T'I` ttt)
 -- , Covariant Transformation Functor from AR (tt `T'TT'I` ttt) (tt `TT'T'I` ttt)
 -- , forall e . Wrapper from (U_T_I_TT_I u t tt e)
 -- , forall e . Wrapper AR (TT'T'I (U_T_I_TT_I u t tt) ttt e)
 -- , forall e . Wrapper AR (T'TT'I (U_T_I_TT_I u t tt) ttt e)
 -- ) => Mapping U_I_II U_I_II from AR (U_T_I_TT_I u t tt `T'TT'I` ttt) (U_T_I_TT_I u t tt `TT'T'I` ttt) where
 -- mapping = rewrap / \from -> rewrap /
  -- day @U_I_II @from @Unit @ttt @u @u (wrap @_ @(U_T_I_TT_I u t tt _)) identity
   -- `compose` i_ (map @U_I_II @U_I_II @AR @AR (wrapped (map @U_I_II @U_I_II @from @AR @(t `T'TT'I` ttt) @(t `TT'T'I` ttt) from)))
   -- `compose` _i (map @U_I_II @U_I_II @AR @AR (wrapped (map @U_I_II @U_I_II @from @AR @(tt `T'TT'I` ttt) @(tt `TT'T'I` ttt) from)))
   -- `compose` unwrap @AR @(U_T_I_TT_I u t tt _)

-- TODO: here should be a generalized version of an instance above
-- instance
 -- ( forall e . Covariant Endo Semi Functor into (U_I_II (u :: * -> * -> *) (t e))
 -- , forall e . Wrapper into (U_T_I_TT_I u t tt e)
 -- , forall e . Wrapper into (TT'T'I (U_T_I_TT_I u t tt) ttt e)
 -- , forall e . Wrapper into (T'TT'I (U_T_I_TT_I u t tt) ttt e)
 -- ) => Mapping U_I_II U_I_II from into (U_T_I_TT_I u t tt `T'TT'I` ttt) (U_T_I_TT_I u t tt `TT'T'I` ttt where
 -- mapping = rewrap / \from -> rewrap /
  -- day_ @U_I_II @from @from @ttt @u @u (wrap @_ @(U_T_I_TT_I u t tt _)) identity `compose`
   -- wrapped (map @U_I_II @into @into @(U_II_I u _)
    -- (wrapped (map @U_I_II @U_I_II @from @into @(t `T'TT'I` ttt) @(t `TT'T'I` ttt) from))) `compose`
   -- wrapped (map @U_I_II @into @into @(U_I_II u _)
    -- (wrapped (map @U_I_II @U_I_II @from @into @(tt `T'TT'I` ttt) @(tt `TT'T'I` ttt) from))) `compose`
   -- unwrap @into @(U_T_I_TT_I u t tt _)

instance Mapping U_I_II U_I_II AR AR (U_I_II P e `T'TT'I` U_I_II AR e) I where
 mapping = rewrap / \from -> rewrap / \(U_I_II (These e (U_I_II f))) -> from (f e)

instance Mapping U_I_II U_I_II AR AR I (U_I_II AR e `T'TT'I` U_I_II P e) where
 mapping = rewrap / \from -> rewrap / \x -> U_I_II / \e -> U_I_II (These e (from x))

instance Mapping U_I_II U_I_II AR AR I (U_I_II AR e `T'TT'I` U_II_I P e) where
 mapping = rewrap / \from -> rewrap / \x -> U_I_II / \e -> U_II_I (These (from x) e)

instance Mapping U_I_II U_I_II AR AR (U_II_I P e `T'TT'I` U_I_II AR e) I where
 mapping = rewrap / \from -> rewrap / \(U_II_I (These (U_I_II f) e)) -> from (f e)

instance Mapping U_I_II U_I_II AR AR (U_I_II P e) (U_I_II P e) where
 mapping = rewrap / \from -> rewrap / \case
  These e x -> These e (from x)

instance Mapping U_I_II U_I_II AR AR (U_II_I P o) (U_II_I P o) where
 mapping = rewrap / \from -> rewrap / \case
  These x e -> These (from x) e

instance Mapping U_I_II U_I_II AR AR (U_I_II S o) (U_I_II S o) where
 mapping = rewrap / \from -> rewrap / \case
  That x -> That (from x)
  This e -> This e

instance Mapping U_I_II U_I_II AR AR (U_II_I S o) (U_II_I S o) where
 mapping = rewrap / \from -> rewrap / \case
  This x -> This (from x)
  That e -> That e

-- instance
 -- ( Covariant Semi Functor from AR t
 -- , Covariant Functor from from (U_I_I u)
 -- , Covariant Monoidal Functor from AR u u t
 -- , forall e . Elicitable U_II_I from (U_I_I u e)
 -- ) => Mapping U_I_II U_I_II from AR (U_I_I u `T'TT'I` t) (U_I_I u `TT'T'I` t) where
 -- mapping = rewrap / \from -> rewrap /
  -- day @U_I_II @from @t @u @u
   -- (map @U_I_II @U_I_II from `compose` wrap @from @(U_I_I _ _)) identity
  -- `compose` unwrap @AR @(U_I_I u _)

-- instance
 -- ( Covariant Semi Functor AR AR t
 -- , Covariant Functor AR AR (U_I_I u)
 -- , Covariant Endo Monoidal Functor AR u u tt
 -- , Mapping U_I_II U_I_II AR AR (t `T'TT'I` tt) (t `TT'T'I` tt)
 -- ) => Mapping U_I_II U_I_II AR AR
  -- ((U_I_I u `T'TT'I` t) `T'TT'I` tt)
  -- ((U_I_I u `T'TT'I` t) `TT'T'I` tt) where
 -- mapping = rewrap / \from -> rewrap /
  -- map @U_I_II @U_I_II @AR @AR (wrap @_ @(U_I_I u `T'TT'I` t `T'I` _)) `compose`
  -- wrapped (component @AR @(U_I_I u `T'TT'I` tt) @(U_I_I u `TT'T'I` tt)) `compose`
  -- map @U_I_II @U_I_II @AR @AR @(U_I_I u)
   -- (wrapped / map @U_I_II @U_I_II @AR @AR @(t `T'TT'I` tt) @(t `TT'T'I` tt) from) `compose`
  -- unwrap @AR

-- instance Covariant Yoneda AR AR tt =>
--  Mapping U_I_II U_I_II AR AR (U_II_I P e `T'TT'I` tt) (U_II_I P e `TT'T'I` tt) where
--  mapping = rewrap / \from -> rewrap / \(U_II_I (These x e)) ->
--   yoneda @U_I_II x (U_II_I `compose` (\x_ -> These (from x_) e))

-- TODO: to fix
instance Mapping U_I_II U_I_II AR AR
 (U_I_II (U_I_UU_II_I AR P) e)
 (U_I_II (U_I_UU_II_I AR P) e) where
 mapping = rewrap / \from -> rewrap `compose` rewrap / \f x ->
  i_ (map @U_I_II @U_I_II from) (f x)

-- TODO: it doesn't work correctly?
instance Mapping U_I_II U_I_II
 (U_I_UU_II_I AR P) AR
 (U_I_II (U_I_UU_II_I AR P) e)
 (U_I_II (U_I_UU_II_I AR P) e) where
 mapping = rewrap / \(U_I_UU_II_I from)
  -> rewrap `compose` rewrap / \trstn e ->
   let These old e' = trstn e in
   let These new _ = from old in
   These new e'

-- TODO: it doesn't work correctly?
instance Mapping U_II_I U_I_II
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

instance Mapping U_I_II U_I_II AR AR
 (UU_V_U_I_II_T_II U_I_II AR AR t e)
 (UU_V_U_I_II_T_II U_I_II AR AR t e) where
 mapping = rewrap / \from -> rewrap (`compose` (rewrap (`compose` from)))

instance Mapping U_II_I U_I_II AR AR
 (UU_V_U_I_II_T_II U_II_I AR AR t e)
 (UU_V_U_I_II_T_II U_II_I AR AR t e) where
 mapping = rewrap / \from -> rewrap (`compose` (rewrap (compose from)))

-- TODO: implement `mapping` method
-- instance Mapping U_I_II U_I_II (W_I_II_II (U_I_UU_III_U_II_I (->) P)) (->)
--  (UU_V_U_I_II_T_II U_I_II (W_I_II_II (U_I_UU_III_U_II_I (->) P)) (->) (U_I_II (W_I_II_II (U_I_UU_III_U_II_I (->) P)) ee) e)
--  (UU_V_U_I_II_T_II U_I_II (W_I_II_II (U_I_UU_III_U_II_I (->) P)) (->) (U_I_II (W_I_II_II (U_I_UU_III_U_II_I (->) P)) ee) e)

-- TODO: implement `mapping` method
-- instance Mapping U_II_I U_I_II (U_I_UU_II_I (->) P)) (->)
--  (UU_V_U_I_II_T_II U_II_I (W_I_II_II (U_I_UU_III_U_II_I (->) P)) (->) (U_II_I (U_I_UU_II_I (->) P)) ee) e)
--  (UU_V_U_I_II_T_II U_II_I (W_I_II_II (U_I_UU_III_U_II_I (->) P)) (->) (U_II_I (U_I_UU_II_I (->) P)) ee) e)

instance
 ( forall e . Covariant Semi Functor from into (U_I_II (U_I_T_II t u) e)
 , forall e . Covariant Semi Functor from into (U_II_I (U_I_T_II t u) e)
 , forall e . Covariant Endo Semi Functor from (U_I_II (U_I_T_II t u) e)
 , forall e . Covariant Endo Semi Functor from (U_II_I (U_I_T_II t u) e)
 , forall e . Wrapper from (R_U_I_T_I u t e)
 , forall e . Wrapper into (R_U_I_T_I u t e)
 , forall e . Wrapper from (Recursive (U_I_T_II t u e))
 , forall e . Wrapper into (Recursive (U_I_T_II t u e))
 , forall e ee . Wrapper from (U_II_I (U_I_T_II t u) e ee)
 , forall e ee . Wrapper into (U_II_I (U_I_T_II t u) e ee)
 , forall e ee . Wrapper from (U_I_II (U_I_T_II t u) e ee)
 , forall e ee . Wrapper into (U_I_II (U_I_T_II t u) e ee)
 ) => Mapping U_I_II U_I_II from into (R_U_I_T_I u t) (R_U_I_T_I u t) where
 mapping = rewrap / \from ->
  wrap @into @(R_U_I_T_I u t _)
  `compose` wrap @into @(Recursive _)
  `compose` unwrap @into @(U_II_I _ _ _)
  `compose` map @U_I_II @U_I_II @_ @_ from
  `compose` wrap @into @(U_II_I _ _ _)
  `compose` unwrap @into @(U_I_II _ _ _)
  `compose` map @U_I_II @U_I_II @from @into @(U_I_II (U_I_T_II t u) _) @(U_I_II (U_I_T_II t u) _)
   (unwrap @from
   `compose` map @U_I_II @U_I_II @from @_ @(R_U_I_T_I u t) @(R_U_I_T_I u t) from
   `compose` wrap @from @(R_U_I_T_I u t _))
  `compose` wrap @into @(U_I_II _ _ _)
  `compose` unwrap @into @(Recursive _)
  `compose` unwrap @into @(R_U_I_T_I u t _)

instance {-# OVERLAPPABLE #-} Mapping U_I_II U_I_II AR AR (U_I_II AR a) (U_I_II AR a) where
 mapping (U_I_II from) = U_I_II / \(U_I_II between) -> U_I_II (\x -> from (between x))

instance Mapping U_II_I U_I_II AR AR (U_II_I AR o) (U_II_I AR o) where
 mapping (U_II_I from) = U_I_II / \(U_II_I between) -> U_II_I (\x -> between (from x))

instance Category AR where
 identity = \x -> x

instance Mapping U_I_II U_I_II AR into t tt
 => Mapping U_1_I U_I_II AR into t tt where
  mapping (U_1_I f) = mapping (U_I_II (f `compose` terminal))

-- instance Mapping U_I_II U_I_II AR AR (U_1_I (->) e) (U_1_I (->) e) where
--  mapping = rewrap / \from (U_1_I x) -> U_1_I / from x

instance Mapping U_I_II U_I_II AR AR I (U_I_II AR e) where
 mapping = rewrap / \from (Identity x) -> U_I_II / \_ -> from x

instance Mapping U_I_II U_I_II AR AR I (U_I_I P) where
 mapping (U_I_II from) = U_I_II / \(Identity x) -> U_I_I (These (from x) (from x))

-- TODO: redefine using limits
instance Mapping U_I_II U_I_II AR AR (U_I_I P) (U_I_I P) where
 mapping (U_I_II from) = U_I_II / \(U_I_I (These x y)) -> U_I_I (These (from x) (from y))

instance Mapping U_I_II U_I_II AR AR (U_I_II P e) I where
 mapping (U_I_II from) = U_I_II / \(U_I_II (These _ x)) -> Identity (from x)

instance Mapping U_I_II U_I_II AR AR (U_II_I P e) I where
 mapping (U_I_II from) = U_I_II / \(U_II_I (These x _)) -> Identity (from x)

instance Mapping U_I_II U_I_II AR AR (U_I_I S) I where
 mapping (U_I_II from) = U_I_II / \case
  U_I_I (This x) -> Identity (from x)
  U_I_I (That x) -> Identity (from x)

instance Mapping U_I_II U_I_II AR AR I (U_I_II S e) where
 mapping (U_I_II from) = U_I_II / \(Identity x) -> U_I_II (That (from x))

instance Mapping U_I_II U_I_II AR AR I (U_II_I S e) where
 mapping (U_I_II from) = U_I_II / \(Identity x) -> U_II_I (This (from x))

instance Mapping U_I_II U_I_II AT AR (U_I_II AT origin) (U_I_II AT origin) where
 mapping = rewrap / \into -> rewrap `compose` rewrap / \from origin ->
  let These source source_origin = from origin in
  let These target target_source = unwrap into source in
  These target (source_origin `compose` target_source)

instance Mapping U_II_I U_I_II AT AR (U_II_I AT origin) (U_II_I AT origin) where
 mapping = rewrap / \from -> rewrap `compose` rewrap / \into origin ->
  let These source source_origin = unwrap from origin in
  let These target target_source = into source in
  These target (source_origin `compose` target_source)

instance Category AT where
 identity = U_I_UU_II_U_II_I / \x -> These x identity

-- instance Mapping U_I_II U_I_II
 -- (W_I_II_II (U_I_UU_III_U_II_I (->) P))
 -- (W_I_II_II (U_I_UU_III_U_II_I (->) P))
 -- (This P e) Identity where
 -- mapping = rewrap `compose` rewrap `compose` rewrap /
  -- \from (U_II_I (These old e)) -> These 
   -- (Identity (wrapped (left @U_I_II @(->) identity) (from old)))
   -- (\(Identity new) -> U_II_I (These ((wrapped (right @U_I_II @(->) identity) (from old)) new) e))

-- instance Mapping U_I_II U_I_II
 -- (W_I_II_II (U_I_UU_III_U_II_I (->) P))
 -- (W_I_II_II (U_I_UU_III_U_II_I (->) P))
 -- (That P e) Identity where
 -- mapping = rewrap `compose` rewrap `compose` rewrap /
  -- -- \from (U_I_II (These e old)) -> These 
   -- / Identity (wrapped (left @U_I_II @(->) identity) (from old))
   -- / \(Identity new) -> U_I_II (These e ((wrapped (right @U_I_II @(->) identity) (from old)) new))

-- instance Mapping U_I_II U_I_II (W_I_II_II (U_I_UU_III_U_II_I (->) P)) (->) Identity (U_I_I P) where
 -- mapping = rewrap / \(W_I_II_II (U_I_UU_III_U_II_I from)) (Identity old) -> U_I_I / These
  -- (wrapped (left @U_I_II @(->) identity) (from old))
  -- (wrapped (left @U_I_II @(->) identity) (from old))

-- instance Mapping U_II_I U_I_II (W_I_II_II (U_I_UU_III_U_II_I (->) P)) (->) (This (->) e) (This (->) e) where
 -- mapping = rewrap / \(W_I_II_II (U_I_UU_III_U_II_I from)) ->
  -- map @U_II_I @U_I_II / (\(These x _) -> x) `compose` from

instance Mapping U_I_II U_I_II AR AR (Day U_I_II AR P P I (Unit `L` I) e ee) I where
 mapping = rewrap / \from -> rewrap / \case
  These (These (Identity e) (Labeled (Identity ee))) (U_I_II f) -> from (f (These e ee))

instance Mapping U_I_II U_I_II AR AR (U_I_II AR Unit) I where
 mapping = rewrap / \from (U_I_II f) -> Identity (from (f Unit))

instance Mapping U_I_II U_I_II AR AR (Day U_I_II AR P P (U_II_I S e) (Unit `L` U_II_I S e) ee eee) (U_II_I S e) where
 mapping = rewrap / \from -> rewrap / \case
  These (These (U_II_I (This ee)) (Labeled (U_II_I (This eee)))) (U_I_II f) -> This (from (f (These ee eee)))
  These (These (U_II_I (That e)) _) _ -> That e

instance Mapping U_I_II U_I_II AR AR (U_I_II AR Unit) (U_II_I S e) where
 mapping = rewrap / \from (U_I_II f) -> U_II_I (This (from (f Unit)))

instance Mapping U_I_II U_I_II AR AR (Day U_I_II AR P P (U_I_II S e) (Unit `L` U_I_II S e) ee eee) (U_I_II S e) where
 mapping = rewrap / \from -> rewrap / \case
  These (These (U_I_II (That ee)) (Labeled (U_I_II (That eee)))) (U_I_II f) -> That (from (f (These ee eee)))
  These (These (U_I_II (This e)) _) _ -> This e
  These (These _ (Labeled (U_I_II (This e)))) _ -> This e

instance Mapping U_I_II U_I_II AR AR (Day U_I_II AR P SP (U_I_II S e) (Unit `L` U_I_II S e) ee eee) (U_I_II S e) where
 mapping = rewrap / \from -> rewrap / \case
  These (These (U_I_II (That ee)) (Labeled (U_I_II (That eee)))) (U_I_II f) ->
   That `compose` from `compose` f `compose` U_U_I_II_UU_I_II `compose` That / These ee eee
  These (These (U_I_II (That ee)) _) (U_I_II f) ->
   That `compose` from `compose` f `compose` U_U_I_II_UU_I_II `compose` This / This ee
  These (These (U_I_II (This _)) (Labeled (U_I_II (That eee)))) (U_I_II f) ->
   That `compose` from `compose` f `compose` U_U_I_II_UU_I_II `compose` This / That eee
  These (These (U_I_II (This e)) (Labeled (U_I_II (This _)))) (U_I_II _) ->
   This e

instance Mapping U_I_II U_I_II AR AR (U_I_II AR Unit) (U_I_II S e) where
 mapping = rewrap / \from (U_I_II f) -> U_I_II (That (from (f Unit)))

instance Mapping U_I_II U_I_II AR AR (Day U_I_II AR P S (U_I_II S e) (Unit `L` U_I_II S e) ee eee) (U_I_II S e) where
 mapping = rewrap / \from -> rewrap / \case
  These (These (U_I_II (That ee)) _) (U_I_II f) -> That (from (f (This ee)))
  These (These _ (Labeled (U_I_II (That eee)))) (U_I_II f) -> That (from (f (That eee)))
  These (These _ (Labeled (U_I_II (This eee)))) (U_I_II _) -> This eee

instance Mapping U_I_II U_I_II AR AR (U_I_II AR Void) (U_II_I S Unit) where
 mapping = rewrap / \_ _ -> U_II_I (That Unit)

-- instance Mapping U_I_II U_I_II AR AR
--   (Day U_I_II AR P S (U_II_I S e) (U_II_I S e) ee eee) (U_II_I S e) where
--  mapping = rewrap / \from -> rewrap / \case
--   These (These (U_II_I (This ee)) _) (U_I_II f) -> This (from (f (This ee)))
--   These (These _ (U_II_I (This eee))) (U_I_II f) -> This (from (f (That eee)))
--   These (These _ (U_II_I (That eee))) _ -> That eee

instance Mapping U_I_II U_I_II AR AR (U_I_II AR Void) (U_I_II S Unit) where
 mapping = rewrap / \_ _ -> U_I_II (This Unit)

instance Mapping U_I_II U_I_II AR AR (U_I_II AR (S Unit Unit)) (U_I_I P) where
 mapping = rewrap / \from -> rewrap / \f -> These
  (from `compose` f / This Unit)
  (from `compose` f / That Unit)

instance Mapping U_I_II U_I_II AR AR (U_I_I P) (U_I_II AR (S Unit Unit)) where
 mapping = rewrap / \from -> rewrap / \(These x y) -> \case
  This _ -> from x
  That _ -> from y

-- instance Mapping U_I_II U_I_II
 -- (W_I_II_II (U_I_UU_III_U_II_I (->) P))
 -- (W_I_II_II (U_I_UU_III_U_II_I (->) P))
 -- (U_I_I P) (U_I_II (->) (S Unit Unit)) where
 -- mapping = rewrap `compose` rewrap `compose` rewrap / \from (U_I_I (These x y)) -> These
  -- / U_I_II (\case { This Unit -> this (from x); That Unit -> this (from y) })
  -- / \(U_I_II f) -> U_I_I (These
   -- / that (from x) (f (This Unit))
   -- / that (from x) (f (That Unit))
   -- )

-- instance Mapping U_I_II U_I_II
 -- (W_I_II_II (U_I_UU_III_U_II_I (->) P))
 -- (W_I_II_II (U_I_UU_III_U_II_I (->) P))
 -- (U_I_II (->) (S Unit Unit)) (U_I_I P) where
 -- mapping = rewrap `compose` rewrap `compose` rewrap / \from (U_I_II f) -> These
  -- / U_I_I (These / this (from (f (This Unit))) / this (from (f (That Unit))))
  -- / \(U_I_I (These x y)) -> U_I_II / \case
   -- This Unit -> that (from (f (This Unit))) x
   -- That Unit -> that (from (f (That Unit))) y

-- instance Mapping U_I_II U_I_II AR AR
  -- (Day U_I_II AR P S (U_I_I P `T'TT'I` t) (U_I_I P `T'TT'I` t) ee eee) (U_I_I P `T'TT'I` t)

-- instance Monoidal U_I_II Functor AR P S t
 -- => Mapping U_I_II U_I_II AR AR (U_I_II AR Void) (U_I_I P `T'TT'I` t) where
 -- mapping = rewrap / \_ _ -> T'TT'I `compose` U_I_I / These
  -- (map @U_I_II @U_I_II @AR @AR @t @t initial empty)
  -- (map @U_I_II @U_I_II @AR @AR @t @t initial empty)

-- instance Mapping U_I_II U_I_II (->) (->)
--  (W_III_I_II (U_I_UU_II_III (->) P) e ee)
--  (W_III_I_II (U_I_UU_II_III (->) P) e ee) where
--  mapping = rewrap / \from -> rewrap `compose` rewrap / \f x -> i_ (map @U_I_II @U_I_II from) (f x)
