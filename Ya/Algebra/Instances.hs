{-# OPTIONS_GHC -fno-warn-orphans #-}
{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE UndecidableInstances #-}
module Ya.Algebra.Instances where

import Ya.Algebra.Abstract
import Ya.Algebra.Definition

instance Mapping T'I'II T'I'II AR into t tt
 => Mapping T''II T'I'II AR into t tt where
  mapping = rewrap `identity` (map @T'I'II @T'I'II @AR @into `compose` constant)

instance
 ( Covariant Semi Functor from into t
 , forall e . Wrapper into (t `L` tt `T` l `T` e)
 ) => Mapping T'I'II T'I'II from into (t `L` tt `T` l) (t `L` tt `T` l) where
 mapping = rewrap `identity` (rewrap `compose` map @T'I'II @T'I'II @from @into @t @t)

instance (Precategory into, forall e . Wrapper into (I e))
 => Mapping T'I'II T'I'II into into I I where
 mapping = rewrap rewrap

instance (Precategory into, forall i ii . Wrapper into (T'I' i ii))
 => Mapping T'I'II T'I'II into (AR) (T'I' i) (T'I' i) where
 mapping = rewrap `identity` \_ (T'I' x) -> (T'I' x)

instance
 ( Precategory into
 , forall i ii . Wrapper into (T'I' i ii)
 , Covariant Lax Monoidal Functor (AR) (AR) (P) P Void t
 ) => Mapping T'I'II T'I'II into (AR) (T'I' i `T'TT'I` t `L` t `T` l `L` T'I' i `T` ll) (T'I' i `TT'T'I` t) where
 mapping = rewrap `identity` \_ -> rewrap `identity` \(T'I' x) -> intro (T'I' x)

instance
 ( forall e . Wrapper into (I e)
 , forall e . Wrapper into (t `L` t `T` l `L` I `T` ll `T` e)
 , forall e . Wrapper into (t `L` t `T` l `T` e)
 , forall e . Wrapper into (I `TT'T'I` t `T'I_` e)
 , forall e . Wrapper into (I `T'TT'I` t `L` t `T` l `L` I `T` ll `T'I_` e)
 , Covariant Endo Semi Functor into t
 ) => Mapping T'I'II T'I'II into into (I `T'TT'I` t `L` t `T` l `L` I `T` ll) (I `TT'T'I` t) where
 mapping = rewrap `identity` \from -> rewrap (
  map @T'I'II @T'I'II @into @into (wrap @into @(I _) `compose` from)
   `compose` unwrap @into @(t `L` t `T` l `T` _)
   `compose` unwrap @into @(t `L` t `T` l `L` I `T` ll `T` _)
   `compose` unwrap @into @(I _))

instance
 ( Covariant Semi Functor from into tt
 , Covariant Endo Semi Functor into t
 , forall e . Wrapper into (t `T'TT'I` tt `T'I_` e)
 ) => Mapping T'I'II T'I'II from into (t `T'TT'I` tt) (t `T'TT'I` tt) where
 mapping = rewrap `identity` \from -> wrap @into `compose` (map @T'I'II @T'I'II @into @into `compose` map @T'I'II @T'I'II @from @into) from `compose` unwrap @into

instance
 ( Covariant Semi Functor from into t
 , Covariant Endo Semi Functor into tt
 , forall e . Wrapper into (t `TT'T'I` tt `T'I_` e)
 ) => Mapping T'I'II T'I'II from into (t `TT'T'I` tt) (t `TT'T'I` tt) where
 mapping = rewrap `identity` \from -> wrap @into `compose` (map @T'I'II @T'I'II @into @into `compose` map @T'I'II @T'I'II @from @into) from `compose` unwrap @into

instance
 ( Covariant Semi Functor from into t
 , forall ee . Covariant Endo Semi Functor into (T'I'II u ee)
 , forall ee . Wrapper into (T'I'II (T'I'TT'II u t) e ee)
 , forall ee . Wrapper into (T'I'TT'II u t e ee)
 , forall ee . Wrapper into (T'I'II u e (t ee))
 ) => Mapping T'I'II T'I'II from into (T'I'II (T'I'TT'II u t) e) (T'I'II (T'I'TT'II u t) e) where
 mapping = rewrap `identity` \from ->
  wrap @into @(T'I'II _ _ _)
  `compose` wrap @into @(T'I'TT'II _ _ _ _)
  `compose` unwrap @into @(T'I'II _ _ _)
  `compose` map @T'I'II @T'I'II @into @into (map @T'I'II @T'I'II @from @into from)
  `compose` wrap @into @(T'I'II _ _ _)
  `compose` unwrap @into @(T'I'TT'II _ _ _ _)
  `compose` unwrap @into @(T'I'II _ _ _)

instance
 ( forall ee . Covariant Semi Functor from into (T'II'I u ee)
 , forall ee . Wrapper into (T'II'I (T'I'TT'II u t) e ee)
 , forall ee . Wrapper into (T'I'TT'II u t ee e)
 , forall ee . Wrapper into (T'II'I u (t e) ee)
 ) => Mapping T'I'II T'I'II from into (T'II'I (T'I'TT'II u t) e) (T'II'I (T'I'TT'II u t) e) where
 mapping = rewrap `identity` \from ->
  wrap @into @(T'II'I _ _ _)
  `compose` wrap @into @(T'I'TT'II _ _ _ _)
  `compose` unwrap @into @(T'II'I _ _ _)
  `compose` map @T'I'II @T'I'II @from @into from
  `compose` wrap @into @(T'II'I _ _ _)
  `compose` unwrap @into @(T'I'TT'II _ _ _ _)
  `compose` unwrap @into @(T'II'I _ _ _)

instance
 ( Covariant Semi Functor from into h
 , Covariant Endo Semi Functor into tt
 , Covariant Endo Semi Functor into t
 , forall e . Wrapper into (T'TTT'TT'I t h tt e)
 ) => Mapping T'I'II T'I'II from into (T'TTT'TT'I t h tt) (T'TTT'TT'I t h tt) where
 mapping = rewrap `identity` \from -> wrap @into
  `compose` (map @T'I'II @T'I'II @into @into
   `compose` map @T'I'II @T'I'II @into @into
   `compose` map @T'I'II @T'I'II @from @into
   ) from
  `compose` unwrap @into

instance
 ( forall e . Covariant Endo Semi Functor into (T'I'II u (t e))
 , forall e . Covariant Endo Semi Functor into (T'II'I u (tt e))
 , Covariant Semi Functor from into tt
 , Covariant Semi Functor from into t
 , forall e . Wrapper into (T'TT'I'TTT'I u t tt e)
 , forall e ee . Wrapper into (T'I'II u (t e) (tt ee))
 , forall e ee . Wrapper into (T'II'I u (tt e) (t ee))
 ) => Mapping T'I'II T'I'II from into (T'TT'I'TTT'I u t tt) (T'TT'I'TTT'I u t tt) where
 mapping = rewrap `identity` \from -> rewrap (
  i_ (map @T'I'II @T'I'II @into @into `compose` map @T'I'II @T'I'II @from @into @t @t `identity` from) `compose`
  _i (map @T'I'II @T'I'II @into @into `compose` map @T'I'II @T'I'II @from @into @tt @tt `identity` from))

-- instance
 -- ( forall e . Covariant Endo Semi Functor (AR) (T'I'II u e)
 -- , forall e . Covariant Endo Semi Functor (AR) (T'II'I u e)
 -- , Covariant Monoidal Functor from (AR) u u Unit ttt
 -- , Covariant Transformation Functor from (AR) (t `T'TT'I` ttt) (t `TT'T'I` ttt)
 -- , Covariant Transformation Functor from (AR) (tt `T'TT'I` ttt) (tt `TT'T'I` ttt)
 -- , forall e . Wrapper from (T'TT'I'TTT'I u t tt e)
 -- , forall e . Wrapper (AR) (TT'T'I (T'TT'I'TTT'I u t tt) ttt e)
 -- , forall e . Wrapper (AR) (T'TT'I (T'TT'I'TTT'I u t tt) ttt e)
 -- ) => Mapping T'I'II T'I'II from (AR) (T'TT'I'TTT'I u t tt `T'TT'I` ttt) (T'TT'I'TTT'I u t tt `TT'T'I` ttt) where
 -- mapping = rewrap `identity` \from -> rewrap `identity`
  -- day @T'I'II @from @Unit @ttt @u @u (wrap @_ @(T'TT'I'TTT'I u t tt _)) identity
   -- `compose` i_ (map @T'I'II @T'I'II @(AR) @(AR) (wrapped (map @T'I'II @T'I'II @from @(AR) @(t `T'TT'I` ttt) @(t `TT'T'I` ttt) from)))
   -- `compose` _i (map @T'I'II @T'I'II @(AR) @(AR) (wrapped (map @T'I'II @T'I'II @from @(AR) @(tt `T'TT'I` ttt) @(tt `TT'T'I` ttt) from)))
   -- `compose` unwrap @(AR) @(T'TT'I'TTT'I u t tt _)

-- TODO: here should be a generalized version of an instance above
-- instance
 -- ( forall e . Covariant Endo Semi Functor into (T'I'II (u :: * -> * -> *) (t e))
 -- , forall e . Wrapper into (T'TT'I'TTT'I u t tt e)
 -- , forall e . Wrapper into (TT'T'I (T'TT'I'TTT'I u t tt) ttt e)
 -- , forall e . Wrapper into (T'TT'I (T'TT'I'TTT'I u t tt) ttt e)
 -- ) => Mapping T'I'II T'I'II from into (T'TT'I'TTT'I u t tt `T'TT'I` ttt) (T'TT'I'TTT'I u t tt `TT'T'I` ttt where
 -- mapping = rewrap `identity` \from -> rewrap `identity`
  -- day_ @T'I'II @from @from @ttt @u @u (wrap @_ @(T'TT'I'TTT'I u t tt _)) identity `compose`
   -- wrapped (map @T'I'II @into @into @(T'II'I u _)
    -- (wrapped (map @T'I'II @T'I'II @from @into @(t `T'TT'I` ttt) @(t `TT'T'I` ttt) from))) `compose`
   -- wrapped (map @T'I'II @into @into @(T'I'II u _)
    -- (wrapped (map @T'I'II @T'I'II @from @into @(tt `T'TT'I` ttt) @(tt `TT'T'I` ttt) from))) `compose`
   -- unwrap @into @(T'TT'I'TTT'I u t tt _)

instance Mapping T'I'II T'I'II (AR) (AR) (P'I'II e `T'TT'I` T'I'II (AR) e) I where
 mapping = rewrap `identity` \from -> rewrap `identity` \(T'I'II (These e (T'I'II f))) -> from (f e)

instance Mapping T'I'II T'I'II (AR) (AR) I (T'I'II (AR) e `T'TT'I` P'I'II e) where
 mapping = rewrap `identity` \from -> rewrap `identity` \x -> T'I'II `identity` \e -> T'I'II (These e (from x))

instance Mapping T'I'II T'I'II (AR) (AR) I (T'I'II (AR) e `T'TT'I` T'II'I (P) e) where
 mapping = rewrap `identity` \from -> rewrap `identity` \x -> T'I'II `identity` \e -> T'II'I (These (from x) e)

instance Mapping T'I'II T'I'II (AR) (AR) (T'II'I (P) e `T'TT'I` T'I'II (AR) e) I where
 mapping = rewrap `identity` \from -> rewrap `identity` \(T'II'I (These (T'I'II f) e)) -> from (f e)

instance Mapping T'I'II T'I'II (AR) (AR) (P'I'II e) (P'I'II e) where
 mapping = rewrap `identity` \from -> rewrap `identity` \case
  These e x -> These e (from x)

instance Mapping T'I'II T'I'II (AR) (AR) (T'II'I (P) o) (T'II'I (P) o) where
 mapping = rewrap `identity` \from -> rewrap `identity` \case
  These x e -> These (from x) e

instance Mapping T'I'II T'I'II (AR) (AR) (S'I'II o) (S'I'II o) where
 mapping = rewrap `identity` \from -> rewrap `identity` \case
  That x -> That (from x)
  This e -> This e

instance Mapping T'I'II T'I'II (AR) (AR) (T'II'I (S) o) (T'II'I (S) o) where
 mapping = rewrap `identity` \from -> rewrap `identity` \case
  This x -> This (from x)
  That e -> That e

instance
 ( Covariant Endo Semi Functor (AR) tt
 , Covariant Endo Semi Functor (AR) (T'I'I t)
 , forall i . Covariant Endo Semi Functor (AR) (T'I'II t i)
 , forall i . Covariant Endo Semi Functor (AR) (T'II'I t i)
 , Covariant Lax Monoidal Functor (AR) (AR) t t l tt
 , forall i . Wrapper (AR) (T'I'I t i)
 ) => Mapping T'I'II T'I'II (AR) (AR) (T'I'I t `T'TT'I` tt `L` tt `T` l `L` T'I'I t `T` Void) (T'I'I t `TT'T'I` tt) where
 mapping = rewrap `identity` \from -> rewrap `identity`
  (day @T'I'II @(AR) @l @tt @tt @t @t identity
   (map @T'I'II @T'I'II from `compose` wrap @(AR) @(T'I'I t _))
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
 -- mapping = rewrap `identity` \from -> rewrap `identity`
  -- map @T'I'II @T'I'II @(AR) @(AR) (wrap @_ @(T'I'I u `T'TT'I` t `T'I` _)) `compose`
  -- wrapped (component @(AR) @(T'I'I u `T'TT'I` tt) @(T'I'I u `TT'T'I` tt)) `compose`
  -- map @T'I'II @T'I'II @(AR) @(AR) @(T'I'I u)
   -- (wrapped `identity` map @T'I'II @T'I'II @(AR) @(AR) @(t `T'TT'I` tt) @(t `TT'T'I` tt) from) `compose`
  -- unwrap @(AR)

-- instance Covariant Yoneda (AR) (AR) tt =>
--  Mapping T'I'II T'I'II (AR) (AR) (T'II'I (P) e `T'TT'I` tt) (T'II'I (P) e `TT'T'I` tt) where
--  mapping = rewrap `identity` \from -> rewrap `identity` \(T'II'I (These x e)) ->
--   yoneda @T'I'II x (T'II'I `compose` (\x_ -> These (from x_) e))

-- TODO: to fix
instance Mapping T'I'II T'I'II (AR) (AR)
 (T'I'II (T'I'TT'II'I (AR) (P)) e)
 (T'I'II (T'I'TT'II'I (AR) (P)) e) where
 mapping = rewrap `identity` \from -> rewrap `compose` rewrap `identity` \f x ->
  i_ (map @T'I'II @T'I'II from) (f x)

-- TODO: it doesn't work correctly?
instance Mapping T'I'II T'I'II
 (T'I'TT'II'I (AR) (P)) (AR)
 (T'I'II (T'I'TT'II'I (AR) (P)) e)
 (T'I'II (T'I'TT'II'I (AR) (P)) e) where
 mapping = rewrap `identity` \(T'I'TT'II'I from)
  -> rewrap `compose` rewrap `identity` \trstn e ->
   let These old e' = trstn e in
   let These new _ = from old in
   These new e'

-- TODO: it doesn't work correctly?
instance Mapping T'II'I T'I'II
 (T'I'TT'II'I (AR) (P)) (AR)
 (T'II'I (T'I'TT'II'I (AR) (P)) e)
 (T'II'I (T'I'TT'II'I (AR) (P)) e) where
 mapping = rewrap `identity` \(T'I'TT'II'I from)
  -> rewrap `compose` rewrap `identity` \trstn new ->
   let These old new' = from new in
   let These e old' = trstn old in
   These e new'

instance Category (T'I'TT'II'I (AR) (P)) where
 identity = T'I'TT'II'I (\e -> These e e)

instance Mapping T'I'II T'I'II (AR) (AR)
 (Covariant Embedding (AR) (AR) t e)
 (Covariant Embedding (AR) (AR) t e) where
 mapping = rewrap `identity` \from ->
  rewrap (`compose` (rewrap (`compose` from)))

instance Mapping T'II'I T'I'II (AR) (AR)
 (Contravariant Embedding (AR) (AR) t e)
 (Contravariant Embedding (AR) (AR) t e) where
 mapping = rewrap `identity` \from ->
  rewrap (`compose` (rewrap (from `compose`)))

instance
 ( Covariant Semi Functor from (AR) t
 , forall e . Covariant Semi Functor into (AR) (T'I'II from e)
 ) => Mapping T'I'II T'I'II from (AR) t (Covariant Embedding into (AR) t r) where
 mapping = rewrap `identity` \from x ->
  Embedding `identity` \e -> map @T'I'II @T'I'II @from
   (wrapped (map @T'I'II @T'I'II @into @(AR) @(T'I'II from _) @(T'I'II from _) (unwrap e)) from) x

instance
 ( Covariant Endo Semi Functor (AR) t
 , forall e . Covariant Endo Semi Functor (AR) (T'I'II (AR) e)
 ) => Mapping U_1_I T'I'II (AR) (AR) t (Embedding U_1_I (AR) (AR) t r) where
 mapping = rewrap `identity` \_ x ->
  Embedding (\(U_1_I e) -> map @T'I'II @T'I'II (\_ -> e Unit) x)

instance
 ( Contravariant Semi Functor from (AR) t
 , forall e . Contravariant Semi Functor into (AR) (T'II'I from e)
 ) => Mapping T'II'I T'I'II from (AR) t (Contravariant Embedding into (AR) t r) where
 mapping = rewrap `identity` \from x ->
  Embedding `identity` \e -> map @T'II'I @T'I'II @from
   (wrapped (map @T'II'I @T'I'II @into @(AR) @(T'II'I from _) @(T'II'I from _) (unwrap e)) from) x


-- TODO: implement `mapping` method
-- instance Mapping T'I'II T'I'II (W_I_II_II (U_I_UU_III_T'II'I (AR) (P))) (AR)
--  (UU_V_T'I'II_T_II T'I'II (W_I_II_II (U_I_UU_III_T'II'I (AR) (P))) (AR) (T'I'II (W_I_II_II (U_I_UU_III_T'II'I (AR) (P))) ee) e)
--  (UU_V_T'I'II_T_II T'I'II (W_I_II_II (U_I_UU_III_T'II'I (AR) (P))) (AR) (T'I'II (W_I_II_II (U_I_UU_III_T'II'I (AR) (P))) ee) e)

-- TODO: implement `mapping` method
-- instance Mapping T'II'I T'I'II (T'I'TT'II'I (AR) (P))) (AR)
--  (UU_V_T'I'II_T_II T'II'I (W_I_II_II (U_I_UU_III_T'II'I (AR) (P))) (AR) (T'II'I (T'I'TT'II'I (AR) (P))) ee) e)
--  (UU_V_T'I'II_T_II T'II'I (W_I_II_II (U_I_UU_III_T'II'I (AR) (P))) (AR) (T'II'I (T'I'TT'II'I (AR) (P))) ee) e)

instance
 ( forall i . Covariant Semi Functor from into (T'I'II u i `T'TT'I` t)
 , forall i . Covariant Endo Semi Functor from (T'I'II u i `T'TT'I` t)
 , forall i . Covariant Endo Semi Functor from (T'II'I u (t i))
 , forall i . Covariant Semi Functor from into (T'II'I u (t i))
 , forall e . Wrapper from (R_U_I_T_I (T'I'II u) t e)
 , forall e . Wrapper into (R_U_I_T_I (T'I'II u) t e)
 , forall i . Wrapper from (Recursive (T'I'II u i `T'TT'I` t))
 , forall i . Wrapper into (Recursive (T'I'II u i `T'TT'I` t))
 , forall i ii . Wrapper from (T'II'I u (t i) ii)
 , forall i ii . Wrapper into (T'II'I u (t i) ii)
 , forall i ii . Wrapper from (T'I'II u i ii)
 , forall i ii . Wrapper into (T'I'II u i ii)
 , forall i ii . Wrapper from ((T'I'II u i `T'TT'I` t) ii)
 , forall i ii . Wrapper into ((T'I'II u i `T'TT'I` t) ii)
 ) => Mapping T'I'II T'I'II from into (R_U_I_T_I (T'I'II u) t) (R_U_I_T_I (T'I'II u) t) where
 mapping = rewrap `identity` \from -> rewrap `compose` rewrap `identity`
  ((rewrap `compose` rewrap) (wrapped (map @T'I'II @T'I'II @_ @_ @(T'II'I u (t _)) @(T'II'I u (t _)) from))
  `compose` map @T'I'II @T'I'II @from @into @(T'I'II u _ `T'TT'I` t) @(T'I'II u _ `T'TT'I` t)
   (wrapped (map @T'I'II @T'I'II @from @_ @(R_U_I_T_I (T'I'II u) t) @(R_U_I_T_I (T'I'II u) t) from))
  )

instance {-# OVERLAPPABLE #-} Mapping T'I'II T'I'II (AR) (AR) (T'I'II (AR) a) (T'I'II (AR) a) where
 mapping (T'I'II from) = T'I'II `identity` \(T'I'II between) -> T'I'II (\x -> from (between x))

instance Mapping T'II'I T'I'II (AR) (AR) (T'II'I (AR) o) (T'II'I (AR) o) where
 mapping (T'II'I from) = T'I'II `identity` \(T'II'I between) -> T'II'I (\x -> between (from x))

instance Category (AR) where
 identity = \x -> x

instance Mapping T'I'II T'I'II (AR) into t tt
 => Mapping U_1_I T'I'II (AR) into t tt where
  mapping (U_1_I f) = mapping (T'I'II (f `compose` terminal))

-- instance Mapping T'I'II T'I'II (AR) (AR) (U_1_I (AR) e) (U_1_I (AR) e) where
--  mapping = rewrap `identity` \from (U_1_I x) -> U_1_I `identity` from x

instance Mapping T'I'II T'I'II (AR) (AR) I (T'I'II (AR) e) where
 mapping = rewrap `identity` \from (Identity x) -> T'I'II `identity` \_ -> from x

instance Mapping T'I'II T'I'II (AR) (AR) I (T'I'I (P)) where
 mapping (T'I'II from) = T'I'II `identity` \(Identity x) -> T'I'I (These (from x) (from x))

-- TODO: redefine using limits
instance Mapping T'I'II T'I'II (AR) (AR) (T'I'I (P)) (T'I'I (P)) where
 mapping (T'I'II from) = T'I'II `identity` \(T'I'I (These x y)) -> T'I'I (These (from x) (from y))

instance Mapping T'I'II T'I'II (AR) (AR) (P'I'II e) I where
 mapping (T'I'II from) = T'I'II `identity` \(T'I'II (These _ x)) -> Identity (from x)

instance Mapping T'I'II T'I'II (AR) (AR) (T'II'I (P) e) I where
 mapping (T'I'II from) = T'I'II `identity` \(T'II'I (These x _)) -> Identity (from x)

instance Mapping T'I'II T'I'II (AR) (AR) (T'I'I (S)) I where
 mapping (T'I'II from) = T'I'II `identity` \case
  T'I'I (This x) -> Identity (from x)
  T'I'I (That x) -> Identity (from x)

instance Mapping T'I'II T'I'II (AR) (AR) I (S'I'II e) where
 mapping (T'I'II from) = T'I'II `identity` \(Identity x) -> T'I'II (That (from x))

instance Mapping T'I'II T'I'II (AR) (AR) I (T'II'I (S) e) where
 mapping (T'I'II from) = T'I'II `identity` \(Identity x) -> T'II'I (This (from x))

instance Mapping T'I'II T'I'II (AT) (AR) (T'I'II (AT) i) (T'I'II (AT) i) where
 mapping = rewrap `identity` \into -> rewrap `compose` rewrap `identity` \from x ->
  let These source source_origin = from x in
  let These target target_source = unwrap into source in
  These target (source_origin `compose` target_source)

instance Mapping T'II'I T'I'II (AT) (AR) (T'II'I (AT) i) (T'II'I (AT) i) where
 mapping = rewrap `identity` \from -> rewrap `compose` rewrap `identity` \into x ->
  let These source source_origin = unwrap from x in
  let These target target_source = into source in
  These target (source_origin `compose` target_source)

instance Category (AT) where
 identity = T'I'TT'II'T'II'I `identity` \x -> These x identity

instance Mapping T'I'II T'I'II AP (AR) (T'I'II AP i) (T'I'II AP i) where
 mapping = rewrap `identity` \from -> rewrap `compose` rewrap `identity` \into i -> case into i of
  This _ -> This Unit
  That a -> case unwrap from a of
   This _ -> This Unit
   That o -> That o

instance Mapping T'II'I T'I'II AP (AR) (T'II'I AP i) (T'II'I AP i) where
 mapping = rewrap `identity` \from -> rewrap `compose` rewrap `identity` \into i -> case unwrap from i of
  This _ -> This Unit
  That a -> case into a of
   This _ -> This Unit
   That o -> That o

instance Category (AP) where
 identity = T'II'TT'I'III `identity` \x -> That x

-- instance Mapping T'I'II T'I'II
 -- (W_I_II_II (U_I_UU_III_T'II'I (AR) (P)))
 -- (W_I_II_II (U_I_UU_III_T'II'I (AR) (P)))
 -- (This (P) e) Identity where
 -- mapping = rewrap `compose` rewrap `compose` rewrap `identity`
  -- \from (T'II'I (These old e)) -> These 
   -- (Identity (wrapped (left @T'I'II @(AR) identity) (from old)))
   -- (\(Identity new) -> T'II'I (These ((wrapped (right @T'I'II @(AR) identity) (from old)) new) e))

-- instance Mapping T'I'II T'I'II
 -- (W_I_II_II (U_I_UU_III_T'II'I (AR) (P)))
 -- (W_I_II_II (U_I_UU_III_T'II'I (AR) (P)))
 -- (That (P) e) Identity where
 -- mapping = rewrap `compose` rewrap `compose` rewrap `identity`
  -- -- \from (T'I'II (These e old)) -> These 
   -- `identity` Identity (wrapped (left @T'I'II @(AR) identity) (from old))
   -- `identity` \(Identity new) -> T'I'II (These e ((wrapped (right @T'I'II @(AR) identity) (from old)) new))

-- instance Mapping T'I'II T'I'II (W_I_II_II (U_I_UU_III_T'II'I (AR) (P))) (AR) Identity (T'I'I (P)) where
 -- mapping = rewrap `identity` \(W_I_II_II (U_I_UU_III_T'II'I from)) (Identity old) -> T'I'I `identity` These
  -- (wrapped (left @T'I'II @(AR) identity) (from old))
  -- (wrapped (left @T'I'II @(AR) identity) (from old))

-- instance Mapping T'II'I T'I'II (W_I_II_II (U_I_UU_III_T'II'I (AR) (P))) (AR) (This (AR) e) (This (AR) e) where
 -- mapping = rewrap `identity` \(W_I_II_II (U_I_UU_III_T'II'I from)) ->
  -- map @T'II'I @T'I'II `identity` (\(These x _) -> x) `compose` from

instance Mapping T'I'II T'I'II (AR) (AR) (Day T'I'II (AR) (P) P I (I `L` I `T` Void) e ee) I where
 mapping = rewrap `identity` \from -> rewrap `identity` \case
  These (These (Identity e) (Label (Identity ee))) (T'I'II f) -> from (f (These e ee))

instance Mapping T'I'II T'I'II (AR) (AR) (T'I'II (AR) Unit) I where
 mapping = rewrap `identity` \from (T'I'II f) -> Identity (from (f Unit))

instance Mapping T'I'II T'I'II (AR) (AR)
 (Day T'I'II (AR) (P) P (T'II'I (S) e) (T'II'I (S) e `L` T'II'I (S) e `T` Void) ee eee) (T'II'I (S) e) where
 mapping = rewrap `identity` \from -> rewrap `identity` \case
  These (These (T'II'I (This ee)) (Label (T'II'I (This eee)))) (T'I'II f) -> This (from (f (These ee eee)))
  These (These (T'II'I (That e)) _) _ -> That e

instance Mapping T'I'II T'I'II (AR) (AR) (T'I'II (AR) Unit) (T'II'I (S) e) where
 mapping = rewrap `identity` \from (T'I'II f) -> T'II'I (This (from (f Unit)))

instance Mapping T'I'II T'I'II (AR) (AR)
 (Day T'I'II (AR) (P) P (S'I'II e) (S'I'II e `L` S'I'II e `T` Void) ee eee) (S'I'II e) where
 mapping = rewrap `identity` \from -> rewrap `identity` \case
  These (These (T'I'II (That ee)) (Label (T'I'II (That eee)))) (T'I'II f) -> That (from (f (These ee eee)))
  These (These (T'I'II (This e)) _) _ -> This e
  These (These _ (Label (T'I'II (This e)))) _ -> This e

instance Mapping T'I'II T'I'II (AR) (AR)
 (Day T'I'II (AR) (P) (R) (S'I'II e) (S'I'II e `L` S'I'II e `T` Void) ee eee) (S'I'II e) where
 mapping = rewrap `identity` \from -> rewrap `identity` \case
  These (These (T'I'II (That ee)) (Label (T'I'II (That eee)))) (T'I'II f) ->
   That `compose` from `compose` f `compose` U_T'I'II_UT'I'II `compose` That `identity` These ee eee
  These (These (T'I'II (That ee)) _) (T'I'II f) ->
   That `compose` from `compose` f `compose` U_T'I'II_UT'I'II `compose` This `identity` This ee
  These (These (T'I'II (This _)) (Label (T'I'II (That eee)))) (T'I'II f) ->
   That `compose` from `compose` f `compose` U_T'I'II_UT'I'II `compose` This `identity` That eee
  These (These (T'I'II (This e)) (Label (T'I'II (This _)))) (T'I'II _) ->
   This e

instance Mapping T'I'II T'I'II (AR) (AR) (T'I'II (AR) Unit) (S'I'II e) where
 mapping = rewrap `identity` \from (T'I'II f) -> T'I'II (That (from (f Unit)))

instance Mapping T'I'II T'I'II (AR) (AR) (Day T'I'II (AR) (P) (S) (S'I'II e) (S'I'II e `L` S'I'II e `T` Void) ee eee) (S'I'II e) where
 mapping = rewrap `identity` \from -> rewrap `identity` \case
  These (These (T'I'II (That ee)) _) (T'I'II f) -> That (from (f (This ee)))
  These (These _ (Label (T'I'II (That eee)))) (T'I'II f) -> That (from (f (That eee)))
  These (These _ (Label (T'I'II (This eee)))) (T'I'II _) -> This eee

instance Mapping T'I'II T'I'II (AR) (AR) (T'I'II (AR) Void) (T'II'I (S) Unit) where
 mapping = rewrap `identity` \_ _ -> T'II'I (That Unit)

-- instance Mapping T'I'II T'I'II (AR) (AR)
--   (Day T'I'II (AR) (P) (S) (T'II'I (S) e) (T'II'I (S) e) ee eee) (T'II'I (S) e) where
--  mapping = rewrap `identity` \from -> rewrap `identity` \case
--   These (These (T'II'I (This ee)) _) (T'I'II f) -> This (from (f (This ee)))
--   These (These _ (T'II'I (This eee))) (T'I'II f) -> This (from (f (That eee)))
--   These (These _ (T'II'I (That eee))) _ -> That eee

instance Mapping T'I'II T'I'II (AR) (AR) (T'I'II (AR) Void) (S'I'II Unit) where
 mapping = rewrap `identity` \_ _ -> T'I'II (This Unit)

instance Mapping T'I'II T'I'II (AR) (AR) (T'I'II (AR) (S Unit Unit)) (T'I'I (P)) where
 mapping = rewrap `identity` \from -> rewrap `identity` \f -> These
  (from `compose` f `identity` This Unit)
  (from `compose` f `identity` That Unit)

instance Mapping T'I'II T'I'II (AR) (AR) (T'I'I (P)) (T'I'II (AR) (S Unit Unit)) where
 mapping = rewrap `identity` \from -> rewrap `identity` \(These x y) -> \case
  This _ -> from x
  That _ -> from y

-- instance Mapping T'I'II T'I'II
 -- (W_I_II_II (U_I_UU_III_T'II'I (AR) (P)))
 -- (W_I_II_II (U_I_UU_III_T'II'I (AR) (P)))
 -- (T'I'I (P)) (T'I'II (AR) (S Unit Unit)) where
 -- mapping = rewrap `compose` rewrap `compose` rewrap `identity` \from (T'I'I (These x y)) -> These
  -- `identity` T'I'II (\case { This Unit -> this (from x); That Unit -> this (from y) })
  -- `identity` \(T'I'II f) -> T'I'I (These
   -- `identity` that (from x) (f (This Unit))
   -- `identity` that (from x) (f (That Unit))
   -- )

-- instance Mapping T'I'II T'I'II
 -- (W_I_II_II (U_I_UU_III_T'II'I (AR) (P)))
 -- (W_I_II_II (U_I_UU_III_T'II'I (AR) (P)))
 -- (T'I'II (AR) (S Unit Unit)) (T'I'I (P)) where
 -- mapping = rewrap `compose` rewrap `compose` rewrap `identity` \from (T'I'II f) -> These
  -- `identity` T'I'I (These `identity` this (from (f (This Unit))) `identity` this (from (f (That Unit))))
  -- `identity` \(T'I'I (These x y)) -> T'I'II `identity` \case
   -- This Unit -> that (from (f (This Unit))) x
   -- That Unit -> that (from (f (That Unit))) y

-- instance Mapping T'I'II T'I'II (AR) (AR)
  -- (Day T'I'II (AR) (P) (S) (T'I'I (P) `T'TT'I` t) (T'I'I (P) `T'TT'I` t) ee eee) (T'I'I (P) `T'TT'I` t)

-- instance Monoidal T'I'II Functor (AR) (P) (S) t
 -- => Mapping T'I'II T'I'II (AR) (AR) (T'I'II (AR) Void) (T'I'I (P) `T'TT'I` t) where
 -- mapping = rewrap `identity` \_ _ -> T'TT'I `compose` T'I'I `identity` These
  -- (map @T'I'II @T'I'II @(AR) @(AR) @t @t initial empty)
  -- (map @T'I'II @T'I'II @(AR) @(AR) @t @t initial empty)

instance Mapping T'I'II T'I'II (AR) (AR) (Day T'I'II (AR) (P) (P) t (t `L` t `T` Void) ee eee) t
 => Mapping T'I'II T'I'II (AR) (AR) (Day T'I'II (AR) (P) (P) (T'I'II (AR) e `T'TT'I` t) ((T'I'II (AR) e `T'TT'I` t) `L` (T'I'II (AR) e `T'TT'I` t) `T` Void) ee eee) (T'I'II (AR) e `T'TT'I` t) where
 mapping = rewrap `identity` \from -> rewrap `identity` \case
  These (These (T'TT'I x) (Label (T'TT'I xx))) (T'I'II f) -> (T'I'II (\e ->
   day @T'I'II @(AR) @Void @t @t @(P) @(P) identity (from `compose` f) `identity` These (unwrap x e) (wrap (unwrap xx e))))

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
 mapping = rewrap `identity` \from -> rewrap `identity` \x ->
  map @T'I'II @T'I'II @(AR) @(AR) @(t `T'TT'I` t `L` t `T` Void) @t
   (map @T'I'II @T'I'II @(AR) @(AR) @(tt `T'TT'I` tt `L` tt `T` Void) @(tt) from
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