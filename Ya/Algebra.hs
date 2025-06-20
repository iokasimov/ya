{-# OPTIONS_GHC -fno-warn-orphans #-}
{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE UndecidableInstances #-}
module Ya.Algebra (module Exports) where

import Ya.Algebra.Abstract as Exports
import Ya.Algebra.Definition as Exports
import Ya.Algebra.Effectful as Exports
import Ya.Algebra.Instances as Exports ()

import Ya.Operators

instance
 ( Covariant Lax Monoidal Functor (AR) (AR) (P) P Void (T'I'II (S) Unit)
 ) => Mapping T'I'II T'I'II (AR) (AR)
 (Day T'I'II (AR) (P) (S) (R_U_I_T_I (P) (T'I'II (S) Unit)) (Void `L` R_U_I_T_I (P) (T'I'II (S) Unit)) i ii)
 (R_U_I_T_I (P) (T'I'II (S) Unit)) where
 mapping = rewrap `identity` \from -> rewrap `identity` \(These (These i ii) (T'I'II f)) ->
   let These x xs = he'he'he i in
   let These _ ys = he'he'he'he ii in
   Recursive `compose` TT'I'T'II `identity` These
    (from `compose` f `identity` This x)
    (day @T'I'II @(AR) @Void @(T'I'II (S) Unit) @(T'I'II (S) Unit) @(P) @P identity
     (unwrap `compose` day @T'I'II @(AR) @Void @(R_U_I_T_I (P) _) @(R_U_I_T_I (P) _) @(P) @(S) identity (from `compose` f)
      `compose` fio (wrap `compose` R_U_I_T_I) `compose` foi R_U_I_T_I)
     `identity` These xs (wrap ys))

instance
 ( Covariant Lax Monoidal Functor (AR) (AR) (P) P Void (T'I'II (S) Unit)
 -- , Covariant Endo Monoidal Functor (AR) (P) (S) Void (R_U_I_T_I (P) (T'I'II (S) Unit))
 ) => Mapping T'I'II T'I'II (AR) (AR) (Day T'I'II (AR) (P) (S)
  (T'I'II (S) Unit `T'TT'I` R_U_I_T_I (P) (T'I'II (S) Unit))
  (Void `L` (T'I'II (S) Unit `T'TT'I` R_U_I_T_I (P) (T'I'II (S) Unit)))
 i ii)
 (T'I'II (S) Unit `T'TT'I` R_U_I_T_I (P) (T'I'II (S) Unit)) where
 mapping = rewrap `identity` \from -> rewrap `identity` \(These (These i (Labeled ii)) (T'I'II f)) ->
  (day @T'I'II @(AR) @Void @(T'I'II (S) Unit) @(T'I'II (S) Unit) @(P) @P identity
     (day @T'I'II @(AR) @Void @(R_U_I_T_I (P) _) @(R_U_I_T_I (P) _) @(P) @(S) identity (from `compose` f)
  `compose` fio @(AR) wrap)
     `li_` unwrap i `lu` wrap (unwrap ii))

-- 1. t (R_U_I_T_I (P) t (L l (L ll tt _)))
-- 2. t (tt (R_U_I_T_I (P) t _))
-- 3. t (L l (L ll tt (R_U_I_T_I (P) t _)))
-- 4. tt (t (R_U_I_T_I (P) t _))
instance
 ( Covariant Endo Semi Functor (AR) t
 , Covariant Lax Monoidal Functor (AR) (AR) (P) P Void tt
 , Covariant Transformation Functor (AR) (AR) (t `T'TT'I` l `L` ll `L` tt) (t `TT'T'I` tt)
 , Covariant Transformation Functor (AR) (AR) (R_U_I_T_I (P) t `T'TT'I` l `L` ll `L` tt) (R_U_I_T_I (P) t `TT'T'I` tt)
 ) => Mapping T'I'II T'I'II (AR) (AR)
  ((t `T'TT'I` R_U_I_T_I (P) t) `T'TT'I` l `L` ll `L` tt)
  ((t `T'TT'I` R_U_I_T_I (P) t) `TT'T'I` tt) where
 mapping = rewrap `identity` \from -> rewrap `identity` \x -> unwrap x
  `yo` wrapped (map @T'I'II @T'I'II @(AR) @(AR)
   @(R_U_I_T_I (P) t `T'TT'I` l `L` ll `L` tt)
   @(R_U_I_T_I (P) t `TT'T'I` tt) from)
  `ho` wrap @(AR) @(L ll tt (R_U_I_T_I (P) t _))
  `ho` wrap @(AR) @((l `L` ll `L` tt) (R_U_I_T_I (P) t _))
  `yi` wrapped (map @T'I'II @T'I'II @(AR) @(AR) @(t `T'TT'I` l `L` ll `L` tt) @(t `TT'T'I` tt) identity)
  `yo` wrap @(AR) @(T'TT'I t (R_U_I_T_I (P) t) _)

-- TODO: reduce a number of transformations here
-- 1. (R_U_I_T_I (P) t (L l tt _))
-- 2. tt  _ `P` t (Recursive (TT'I'T'II t (P) (L l tt _)))
-- 3. tt _ `P` t (R_U_I_T_I (P) t (L l tt _))
-- 4. tt _ `P` t (tt (R_U_I_T_I (P) t _))
-- 5. tt _ `P` t (L l tt (R_U_I_T_I (P) t _))
-- 6. tt _ `P` tt (t (R_U_I_T_I (P) t _))
-- 7. tt (R_U_I_T_I (P) t _)

instance
 ( Covariant Endo Semi Functor (AR) t
 , Covariant Endo Semi Functor (AR) tt
 , Covariant Lax Monoidal Functor (AR) (AR) (P) P Void tt
 , Covariant Transformation Functor (AR) (AR) (t `T'TT'I` Void `L` ll `L` tt) (t `TT'T'I` tt)
 ) => Mapping T'I'II T'I'II (AR) (AR) (R_U_I_T_I (P) t `T'TT'I` Void `L` ll `L` tt) (R_U_I_T_I (P) t `TT'T'I` tt) where
 mapping = rewrap `identity` \from -> rewrap `identity` \(R_U_I_T_I (Recursive (TT'I'T'II (These x xs)))) ->
    unwrap (unwrap x) `yo` from
     `lu_`xs
      `yo` wrap @(AR) @(R_U_I_T_I _ _ _)
      `ho` wrapped (map @T'I'II @T'I'II @(AR) @(AR) @(R_U_I_T_I (P) t `T'TT'I` Void `L` ll `L` tt) @(R_U_I_T_I (P) t `TT'T'I` tt) from)
      `ho` wrap @(AR) @((ll `L` tt) _)
      `ho` wrap @(AR) @((Void `L` ll `L` tt) _)
      `yi` wrapped (map @T'I'II @T'I'II @(AR) @(AR) @(t `T'TT'I` Void `L` ll `L` tt) @(t `TT'T'I` tt) (unwrap @(AR) @(R_U_I_T_I _ _ _)))
      `ho` wrap @(AR) @((Void `L` _) _)
     `yp_'yo` wrap @(AR) @(R_U_I_T_I _ _ _) `ha` wrap @(AR) @(Recursive _) `ha` wrap @(AR) @(TT'I'T'II _ _ _ _)

instance
 ( Covariant Endo Semi Functor (AR) t
 , Covariant Endo Semi Functor (AR) tt
 , Covariant Lax Monoidal Functor (AR) (AR) (P) P Void tt
 , Transformation T'I'II Functor (AR) (AR) (t `T'TT'I` L (Void `P` Void) (L ll tt)) (t `TT'T'I` tt)
 ) => Mapping T'I'II T'I'II (AR) (AR)
  (R_U_I_T_I (P) t `T'TT'I` L (Void `P` Void) (L ll tt))
  (R_U_I_T_I (P) t `TT'T'I` tt) where
 mapping = rewrap `identity` \from -> rewrap
  `identity` \(R_U_I_T_I (Recursive (TT'I'T'II (These x xs)))) ->
   (These
    `ho_'ho` wrap @(AR) @(TT'I'T'II _ _ _ _)
    `ho` wrap @(AR) @(Recursive _)
    `ho` wrap @(AR) @(R_U_I_T_I _ _ _))
   `fo` (unwrap (unwrap x) `yo` from)
   `fc` (xs
      `yo` wrap @(AR) @(R_U_I_T_I _ _ _)
      `ho` wrapped (map @T'I'II @T'I'II @(AR) @(AR)
       @(R_U_I_T_I (P) t `T'TT'I` L (Void `P` Void) (L ll tt))
       @(R_U_I_T_I (P) t `TT'T'I` tt) from)
      `ho` wrap @(AR) @(L ll tt _)
      `ho` wrap @(AR) @(L (Void `P` Void) (L ll tt) _)
      `yi` wrapped (map @T'I'II @T'I'II @(AR) @(AR) @(t `T'TT'I` L (Void `P` Void) (L ll tt)) @(t `TT'T'I` tt) (unwrap @(AR) @(R_U_I_T_I _ _ _)))
    )

-- TODO: try to simplify
instance
 ( Covariant Lax Monoidal Functor (AR) (AR) (P) P Void t
 , Covariant Lax Monoidal Functor (AR) (AR) (P) P Void (R_U_I_T_I (P) t)
 ) => Mapping T'I'II T'I'II (AR) (AR) (Day T'I'II (AR) (P) P (R_U_I_T_I (P) t) (Void `L` R_U_I_T_I (P) t) e ee) (R_U_I_T_I (P) t) where
 mapping = rewrap `identity` \from -> rewrap `identity` \case
  These (These e ee) (T'I'II f) ->
   let These e_ e__ = he'he'he e in
   let These ee_ ee__ = he'he'he'he ee in
   Recursive `compose` TT'I'T'II `identity` These
    (from `compose` f `identity` These e_ ee_)
    (day @T'I'II @(AR) @Void @t @t @(P) @P identity
     (unwrap
      `compose` day @T'I'II @(AR) @Void @(R_U_I_T_I (P) t) @(R_U_I_T_I (P) t) @(P) @P identity (from `compose` f)
      `compose` fio (wrap `compose` R_U_I_T_I)
      `compose` foi R_U_I_T_I)
     `identity` These e__ (wrap ee__))

instance (Initial (AR), Covariant Lax Monoidal Functor (AR) (AR) (P) (S) Void t) =>
 Mapping T'I'II T'I'II (AR) (AR) (T'I'II (AR) Unit) (R_U_I_T_I (P) t) where
 mapping = rewrap `identity` \from (T'I'II f) ->
  R_U_I_T_I `compose` Recursive `compose` TT'I'T'II
   `identity` These (from `identity` f Unit) (empty @t `yo` initial' @(AR))

instance
 ( Covariant Lax Monoidal Functor (AR) (AR) (P) P Void t
 , Covariant Lax Monoidal Functor (AR) (AR) (P) P Void (R_U_I_T_I (P) t)
 ) => Mapping T'I'II T'I'II (AR) (AR) (Day T'I'II (AR) (P) P (t `T'TT'I` R_U_I_T_I (P) t) (Void `L` (t `T'TT'I` R_U_I_T_I (P) t)) e ee) (t `T'TT'I` R_U_I_T_I (P) t) where
 mapping = rewrap `identity` \from -> rewrap `identity` \case
  These (These (T'TT'I e) (Labeled (T'TT'I ee))) (T'I'II f) ->
    day @T'I'II @(AR) @Void @t @t @(P) @P identity
     (day @T'I'II @(AR) @Void @(R_U_I_T_I (P) t) @(R_U_I_T_I (P) t) @(P) @P identity (from `compose` f) `compose` fio @(AR) wrap)
      (These e (wrap ee))

instance
 ( Covariant Lax Monoidal Functor (AR) (AR) (P) P Void t
 , Covariant Lax Monoidal Functor (AR) (AR) (P) P Void (R_U_I_T_I (P) tt)
 ) => Mapping T'I'II T'I'II (AR) (AR) (T'I'II (AR) Unit) (t `T'TT'I` R_U_I_T_I (P) tt) where
 mapping = rewrap `identity` \from (T'I'II f) -> T'TT'I `li`
  intro @t @(AR) `compose` intro @(R_U_I_T_I (P) tt) @(AR) `compose` from `compose` f `identity` Unit

-- TODO: try to avoid mapping a datastructure twice here
instance
 ( Covariant Endo Semi Functor (AR) t
 , Covariant Lax Monoidal Functor (AR) (AR) (P) (SP) Void t
 ) => Mapping T'I'II T'I'II (AR) (AR) (Day T'I'II (AR) (P) (SP) (t `T'TT'I` R_U_I_T_I (P) t) (Void `L` (t `T'TT'I` R_U_I_T_I (P) t)) e ee) (t `T'TT'I` R_U_I_T_I (P) t) where
 mapping = rewrap `identity` \from -> rewrap `identity` \case
  These (These (T'TT'I e) (Labeled (T'TT'I ee))) (T'I'II f) ->
    (day @T'I'II @(AR) @Void @t @t @(P) @(SP) identity
     (\case
      U_T'I'II_UT'I'II (This (This x)) -> x `yo` from `compose` f `compose` U_T'I'II_UT'I'II `compose` This `compose` This
      U_T'I'II_UT'I'II (This (That x)) -> x `yo` from `compose` f `compose` U_T'I'II_UT'I'II `compose` This `compose` That
      U_T'I'II_UT'I'II (That x) -> day @T'I'II @(AR) @Void @(R_U_I_T_I (P) t) @(R_U_I_T_I (P) t) @(P) @(SP) identity (from `compose` f) (fio @(AR) wrap x)
     )
      (These e (wrap @(AR) ee))
    )

-- TODO: try to avoid mapping twice datastructure here
instance
 ( Covariant Endo Semi Functor (AR) t
 , Covariant Lax Monoidal Functor (AR) (AR) (P) (SP) Void t
  -- TODO: I hope it doesn't produce cycles
 -- , Covariant Monoidal Functor (AR) (AR) (P) (SP) Void (R_U_I_T_I (P) t)
 ) => Mapping T'I'II T'I'II (AR) (AR) (Day T'I'II (AR) (P) (SP) (R_U_I_T_I (P) t) (Void `L` R_U_I_T_I (P) t) e ee) (R_U_I_T_I (P) t) where
 mapping = rewrap `identity` \from -> rewrap `identity` \case
  These (These e ee) (T'I'II f) ->
   let These e_ e__ = he'he'he e in
   let These ee_ ee__ = he'he'he'he ee in
   Recursive `compose` TT'I'T'II `identity` These
    (from `compose` f `compose` U_T'I'II_UT'I'II `compose` That `identity` These e_ ee_)
    (day @T'I'II @(AR) @Void @t @t @(P) @(SP) identity
     (unwrap @(AR) `compose` \case
      U_T'I'II_UT'I'II (This (This x)) -> R_U_I_T_I x `yo` from `compose` f `compose` U_T'I'II_UT'I'II `compose` This `compose` This
      U_T'I'II_UT'I'II (This (That x)) -> R_U_I_T_I x `yo` from `compose` f `compose` U_T'I'II_UT'I'II `compose` This `compose` That
      U_T'I'II_UT'I'II (That (These x xx)) -> day @T'I'II @(AR) @Void @(R_U_I_T_I (P) t) @(R_U_I_T_I (P) t) @(P) @(SP) identity (from `compose` f) (R_U_I_T_I x `lu` wrap (R_U_I_T_I xx))
     )
     `identity` These e__ (wrap ee__))

instance (Initial (AR), Covariant Lax Monoidal Functor (AR) (AR) (P) (S) Void t) =>
 Mapping T'I'II T'I'II (AR) (AR) (T'I'II (AR) Void) (t `T'TT'I` R_U_I_T_I (P) tt) where
 mapping = rewrap `identity` \_ _ -> T'TT'I (empty @t `yo` initial' @(AR))

instance Mapping T'I'II T'I'II (AT) (AT) (T'I'II (P) e) (T'I'II (P) e) where
 mapping = rewrap `compose` rewrap `identity` \from (T'I'II (These e x)) ->
   let s = from x in T'I'II (These e (this s)) `lu` fo (that s)

instance Mapping T'I'II T'I'II (AT) (AT) (T'II'I (P) e) (T'II'I (P) e) where
 mapping = rewrap `compose` rewrap `identity` \from (T'II'I (These x e)) ->
   let s = from x in T'II'I (These (this s) e) `lu` fo (that s)

-- TODO: I'm not really sure about this instance... it could easily lead to an error!
instance Mapping T'I'II T'I'II (AT) (AT) I (T'I'I (P)) where
 mapping = rewrap `compose` rewrap `identity` \from (Identity x) ->
   let s = from x in T'I'I (this s `lu`this s) `lu` (\(T'I'I (These _ _)) -> Identity (that s (this s)))

instance Mapping T'I'II T'I'II (AT) (AT) (T'I'II (P) e) I where
 mapping = rewrap `compose` rewrap `identity` \from (T'I'II (These e x)) ->
   let s = from x in Identity (this s) `lu` (T'I'II `compose` (e `lu`) `compose` that s `compose` unwrap)

instance Mapping T'I'II T'I'II (AT) (AT) (T'II'I (P) e) I where
 mapping = rewrap `compose` rewrap `identity` \from (T'II'I (These x e)) ->
   let s = from x in Identity (this s) `lu` (T'II'I `compose` (`lu` e) `compose` that s `compose` unwrap)

-- TODO: I should alse test how attributes behave on sums

-- This instance for normal state propagation. How unnormal should look like?
instance (e ~ ee) =>
 Mapping T'I'II T'I'II (AR) (AR)
 (T'I'II (U_I_UT'II'I (AR) (P)) e `T'TT'I` Void `L` T'I'II (U_I_UT'II'I (AR) (P)) ee)
 (T'I'II (U_I_UT'II'I (AR) (P)) e) where
 mapping = rewrap `identity` \from -> rewrap `compose` rewrap `identity` \(U_I_UT'II'I state) old ->
    let These trn btw = state old in
    let These res new = unwrap (unwrap (unwrap trn)) btw in
        These (from res) new

instance (e ~ ee) => Mapping T'I'II T'I'II (AR) (AR)
 (T'I'II (U_I_UT'II'I (AR) (P)) e `T'TT'I` L (Void `P` Void) `T'I` T'I'II (U_I_UT'II'I (AR) (P)) ee)
 (T'I'II (U_I_UT'II'I (AR) (P)) e) where
 mapping = rewrap `identity` \from -> rewrap `compose` rewrap `identity` \(U_I_UT'II'I state) old ->
    let These trn btw = state old in
    let These res _ = unwrap (unwrap (unwrap trn)) btw in
        These (from res) old

instance (Covariant Lax Monoidal Functor (AR) (AR) (P) (P) Void t, e ~ ee)
 => Mapping T'I'II T'I'II (AR) (AR)
  (T'I'II (U_I_UT'II'I (AR) (P)) ee)
  (T'TTT'TT'I (T'I'II (AR) e) (T'II'I (P) e) t) where
 mapping = rewrap `identity` \from (T'I'II (U_I_UT'II'I x)) ->
  wrap @_ @(T'TTT'TT'I _ _ _ _) `compose` wrap @_ @(T'I'II _ _ _)
  `identity` (intro `compose` map @T'I'II @T'I'II from `compose` wrap @_ @(T'II'I _ _ _) `compose` x)

instance {-# OVERLAPPABLE #-} Covariant Transformation Functor (AR) (AR) (t `T'TT'I` ll `L` tt) t => Mapping T'I'II T'I'II (AR) (AR)
 (T'I'II (AR) e `T'TT'I` t `T'TT'I_` ll `L` tt) (T'I'II (AR) e `T'TT'I` t) where
 mapping = rewrap `identity` \from -> rewrap `compose` rewrap `identity`
  \(T'I'II f) e -> map @T'I'II @T'I'II @(AR) @(AR) @(t `T'TT'I` ll `L` tt) @t from (T'TT'I (f e))

instance {-# OVERLAPS #-}
 Covariant Endo Semi Functor (AR) t
 => Mapping T'I'II T'I'II (AR) (AR) (T'I'II (AR) e `T'TT'I` t `T'TT'I_` T'I'II (AR) e) (T'I'II (AR) e `T'TT'I` t) where
 mapping = rewrap `identity` \from -> rewrap `compose` rewrap `identity`
  \(T'I'II f) e -> f e `yo` unwrap @(AR) `ho` (`li` e) `ho` from

instance {-# OVERLAPPABLE #-}
 Covariant Transformation Functor (AR) (AR) (t `T'TT'I` Void `L` t) t
 => Mapping T'I'II T'I'II (AR) (AR) (T'I'II (AR) e `T'TT'I` t `T'TT'I_` Void `L` (T'I'II (AR) e `T'TT'I` t)) (T'I'II (AR) e `T'TT'I` t) where
 mapping = rewrap `identity` \from -> rewrap `compose` rewrap `identity`
  \(T'I'II f) e ->
   map @T'I'II @T'I'II @AR @AR @(t `T'TT'I` Void `L` t) @t from `compose` wrap
   `compose` map @T'I'II @T'I'II @AR @AR @t @t (wrap @AR @(Void `L` t `T'I` _) `compose` yi e `compose` unwrap `compose` unwrap `compose` unwrap)
   `identity` f e

-- f e: t (Void `L` (T'I'II AR e `T'TT'I` t) `T'I` a)


-- NOTE: this version allow different type of states, but it requires providing types to make it compile
-- 1. T'I'II (AR) old (t (T'II'I (P) btw))

instance
 ( Covariant Endo Semi Functor (AR) t
 , Covariant Transformation Functor (AR) (AR) (t `T'TT'I` Void `L` t) t
 ) => Mapping T'I'II T'I'II (AR) (AR)
 (
  ((T'I'II (AR) old `T'TTT'TT'I` T'II'I (P) btw) t) `T'TT'I`
  Void `L` (T'I'II (AR) btw `T'TTT'TT'I` T'II'I (P) new) t
 )
 (T'TTT'TT'I (T'I'II (AR) old) (T'II'I (P) new) t) where
 mapping = rewrap `identity` \from -> rewrap `compose` rewrap `identity`
  \(T'I'II x) -> component @(AR) @(t `T'TT'I` L Void t) @t
  `compose` wrap @(AR) @(T'TT'I t (L Void t) _)
  `compose` map @T'I'II @T'I'II @(AR) @(AR) @t @t
   (wrap @(AR) @(L Void t _) `compose` fd @(AR) @(AR) (unwrap @(AR) @(T'TTT'TT'I (T'I'II (AR) btw) (T'II'I (P) new) t _) `compose` fo from `compose` unwrap @(AR) @(L Void _ _)))
  `compose` x

-- TODO: try to use adjunctions here
instance
 ( Covariant Lax Monoidal Functor (AR) (AR) (P) P Void tt
 , Covariant Transformation Functor (AR) (AR) (tt `T'TT'I` Void `L` tt) tt
 , e ~ ee
 ) => Mapping T'I'II T'I'II (AR) (AR)
 (T'TTT'TT'I (T'I'II (AR) e) (T'II'I (P) e) tt `T'TT'I` Void `L` T'I'II (U_I_UT'II'I (AR) (P)) ee)
 (T'TTT'TT'I (T'I'II (AR) e) (T'II'I (P) e) tt) where
  mapping = rewrap `identity` \from -> rewrap `compose` rewrap `identity` \(T'I'II x) ->
    \old -> x old `yok` \(T'II'I (These (Labeled (T'I'II (U_I_UT'II'I f))) btw))
      -> (Labeled @Void `compose` intro @tt) `identity` (T'II'I (f btw) `yo` from)

instance
 ( Covariant Lax Monoidal Functor (AR) (AR) (P) P Void tt
 , Covariant Transformation Functor (AR) (AR) (tt `T'TT'I` Void `L` tt) tt
 , e ~ ee
 ) => Mapping T'I'II T'I'II (AR) (AR)
 (T'TT'I
  (T'TTT'TT'I (T'I'II (AR) e) (T'II'I (P) e) tt)
  ((Void `P` Void) `L` (T'I'II (U_I_UT'II'I (AR) (P)) ee))
 )
 (T'TTT'TT'I (T'I'II (AR) e) (T'II'I (P) e) tt) where
  mapping = rewrap `identity` \from -> rewrap `compose` rewrap `identity` \(T'I'II x) ->
    \old -> x old `yok` \(T'II'I (These (Labeled (T'I'II (U_I_UT'II'I f))) btw))
      -> (Labeled @Void `compose` intro @tt @(AR) ) `identity` (T'II'I (f btw `yiu` old) `yo` from)

-- TODO: introduce a label
instance
 ( Covariant Functor into into t
 , Covariant Endo Semi Functor into ttt
 , Mapping T'I'II T'I'II into into (t `T'TT'I` L l t) t
 , Mapping T'I'II T'I'II into into (tt `T'TT'I` L l t) (tt `TT'T'I` t)
 , forall ee . Wrapper into ((tt `T'TT'I` L l t) ee)
 , forall ee . Wrapper into (L l t ee)
 , forall ee . Wrapper into (L l t (tt ee))
 , forall ee . Wrapper into (T'TTT'TT'I ttt (tt) t ee)
 , forall ee . Wrapper into ((tt `T'TT'I` t) ee)
 , forall ee . Wrapper into ((tt `TT'T'I` t) ee)
 , forall ee . Wrapper into ((t `T'TT'I` L l t) ee)
 , forall ee . Wrapper into (T'TT'I (T'TTT'TT'I ttt tt t) (L l t) ee)
 ) => Mapping T'I'II T'I'II into into
  (T'TTT'TT'I ttt tt t `T'TT'I` L l t)
  (T'TTT'TT'I ttt tt t) where
 mapping = rewrap `identity` \from -> rewrap `identity`
  map @T'I'II @T'I'II @into @into @ttt
   (component @into @(t `T'TT'I` L l t) @t `compose` wrap @into
    `compose` map @T'I'II @T'I'II @into @into @t
     (wrap @into @(L l t _) `compose` wrapped (map @T'I'II @T'I'II @into @into @(tt `T'TT'I` L l t) @(tt `TT'T'I` t) from))
    )
  `compose` unwrap @into

-- TODO: rename type variables
-- 1. t (tt't (tt'tt (ttt (L l tt't _))))
-- 2. t (tt't (tt'tt (tt't (ttt _))))
-- 3. t (tt't (tt't (tt'tt (ttt _))))
-- 4. t (tt't (tt'tt (ttt _)))
instance
 ( Covariant Functor into into tt'tt
 , Covariant Endo Semi Functor into t
 , Covariant Endo Semi Functor into tt't
 , Component into (tt't `T'TT'I` L l tt't) tt't
 , Covariant Transformation Functor into into (ttt `T'TT'I` L l tt't) (ttt `TT'T'I` tt't)
 , Component into (tt'tt `T'TT'I` L l tt't) (tt'tt `TT'T'I` tt't)
 , forall ee . Wrapper into (L l tt't ee)
 , forall ee . Wrapper into (T'TT'I ttt (L l tt't) ee)
 , forall ee . Wrapper into (TT'T'I ttt tt't ee)
 , forall ee . Wrapper into (T'TT'I tt'tt (L l tt't) ee)
 , forall ee . Wrapper into (TT'T'I tt'tt tt't ee)
 , forall ee . Wrapper into (T'TT'I tt't (L l tt't) ee)
 , forall ee . Wrapper into (T'TT'I (T'TTT'TT'I t ttt (TT'T'I tt'tt tt't)) (L l tt't) ee)
 , forall ee . Wrapper into (T'TTT'TT'I t ttt (TT'T'I tt'tt tt't) ee)
 ) => Mapping T'I'II T'I'II into into
  (T'TTT'TT'I t ttt (TT'T'I tt'tt tt't) `T'TT'I` L l tt't)
  (T'TTT'TT'I t ttt (TT'T'I tt'tt tt't)) where
 mapping = rewrap `identity` \from -> rewrap `identity`
  map @T'I'II @T'I'II @into @into @t @t
   (wrap @into @(TT'T'I _ _ _)
    `compose` component @into @(tt't `T'TT'I` L l tt't) @tt't
    `compose` wrap @into @(T'TT'I tt't (L l tt't) _)
    `compose` map @T'I'II @T'I'II @into @into @tt't @tt't (wrap @into @(L l tt't _))
    `compose` map @T'I'II @T'I'II @into @into @tt't
     (wrapped (component @into @(tt'tt `T'TT'I` L l tt't) @(tt'tt `TT'T'I` tt't))
     `compose` map @T'I'II @T'I'II @into @into @(tt'tt) @(tt'tt) (wrap @into @(L l tt't _)))
    `compose` unwrap @into @(TT'T'I tt'tt tt't _)
    `compose` map @T'I'II @T'I'II @into @into @(TT'T'I tt'tt tt't) @(TT'T'I tt'tt tt't)
     (wrapped (map @T'I'II @T'I'II @into @into @(ttt `T'TT'I` L l tt't) @(ttt `TT'T'I` tt't) from))
   )
  `compose` unwrap @into

-- TODO: introduce a label
-- 1. t (ttt'tt (ttt't (tt (ttt't _))))
-- 2. t (ttt'tt (ttt't (ttt't (tt _))))
-- 4. t (ttt'tt (ttt't (tt _)))
instance
 ( Covariant Functor into into ttt't
 , Covariant Endo Semi Functor into t
 , Covariant Endo Semi Functor into ttt'tt
 , Component into (ttt't `T'TT'I` L l ttt't) ttt't
 , Covariant Transformation Functor into into (tt `T'TT'I` L l ttt't) (tt `TT'T'I` ttt't)
 , forall ee . Wrapper into ((ttt't `T'TT'I` L l ttt't) ee)
 , forall ee . Wrapper into ((tt `T'TT'I` L l ttt't) ee)
 , forall ee . Wrapper into (L l ttt't ee)
 , forall ee . Wrapper into (T'TT'I ttt't ttt't ee)
 , forall ee . Wrapper into (T'TT'I ttt't ttt'tt ee)
 , forall ee . Wrapper into (T'TT'I (T'TTT'TT'I t tt (TT'T'I ttt't ttt'tt)) (L l ttt't) ee)
 , forall ee . Wrapper into (TT'T'I tt ttt't ee)
 , forall ee . Wrapper into (TT'T'I ttt't ttt'tt ee)
 , forall ee . Wrapper into (T'TTT'TT'I t tt (TT'T'I ttt't ttt'tt) ee)
 ) => Mapping T'I'II T'I'II into into
  (T'TTT'TT'I t tt (TT'T'I ttt't ttt'tt) `T'TT'I` L l ttt't)
  (T'TTT'TT'I t tt (TT'T'I ttt't ttt'tt)) where
 mapping = rewrap `identity` \from -> rewrap `identity`
  map @T'I'II @T'I'II @into @into @t @t
   (wrap @into @(TT'T'I _ _ _)
    `compose` map @T'I'II @T'I'II @into @into @ttt'tt
     (component @into @(ttt't `T'TT'I` L l ttt't) @ttt't
     `compose` wrap @into @(T'TT'I _ _ _)
     `compose` map @T'I'II @T'I'II @into @into @ttt't (wrap @into @(L l ttt't _))
     )
    `compose` unwrap @into @(TT'T'I ttt't ttt'tt _)
    `compose` map @T'I'II @T'I'II @into @into @(ttt't `TT'T'I` ttt'tt) @(ttt't `TT'T'I` ttt'tt)
     (wrapped (map @T'I'II @T'I'II @into @into @(tt `T'TT'I` L l ttt't) @(tt `TT'T'I` ttt't) from))
   )
  `compose` unwrap @into

instance
 ( Covariant Lax Monoidal Functor (AR) (AR) (P) P Void t
 , Covariant Endo Semi Functor (AR) tt
 ) => Mapping T'I'II T'I'II (AR) (AR) tt (tt `TT'T'I` t) where
 mapping = rewrap `identity` \from -> wrap @(AR) @((tt `TT'T'I` t) _)
  `compose` component @(AR) @(T'I'II (AR) Unit) @t
  `compose` component @(AR) @I @(T'I'II (AR) Unit)
  `compose` wrap @(AR)
  `compose` map @T'I'II @T'I'II @(AR) @(AR) @tt @tt from

-- instance Mapping T'I'II T'I'II (AR) (AR) (T'II'I (P) e `T'TT'I` L (T'I'II (S) () ()) tt) (T'II'I (P) e `TT'T'I` tt) =>
 -- Mapping T'I'II T'I'II (AR) (AR)
  -- (T'I'II (U_I_UT'II'I (AR) (P)) e `T'TT'I` tt)
  -- (T'TTT'TT'I (T'I'II (AR) e) (T'II'I (P) e) tt) where
 -- mapping = rewrap `identity` \from (T'TT'I (T'I'II (U_I_UT'II'I x))) ->
  -- T'TTT'TT'I `compose` T'I'II `identity` \old -> wrapped @(AR)
   -- `li` map @T'I'II @T'I'II @(AR) @(AR) @(T'II'I (P) e `T'TT'I` L (T'I'II (S) () ()) tt) @(T'II'I (P) e `TT'T'I` tt) from
   -- `li` T'II'I (x old)

instance Covariant Lax Monoidal Functor (AR) (AR) (P) P Void t =>
 Mapping T'I'II T'I'II (AR) (AR) (T'I'II (AR) Unit) (T'I'II (AR) e `T'TT'I` t) where
 mapping = rewrap `identity` \from -> rewrap `identity` \f -> T'I'II `identity` \_ -> intro `compose` from `li` f Unit

instance
 ( Covariant Yoneda Functor into into I
 , Covariant Endo Semi Functor into (T'I'II into i)
 , Adjoint Functor into into (T'II'I t i) (T'I'II tt i)
 , forall e . Wrapper into (T'II'I t i e)
 , forall e . Wrapper into (T'I'II into Unit e)
 , forall e . Wrapper into (T'I'II tt i e)
 , forall e . Wrapper into (U_I_UT'II'I tt t i e)
 , forall e . Wrapper into (T'I'II (U_I_UT'II'I tt t) i e)
 , forall e . Wrapper into (T'TT'I (T'I'II tt i) (T'II'I t i) e)
 , forall e . Wrapper into (T'TT'I (T'II'I t i) (T'I'II tt i) e)
 , forall e . Wrapper into (I e)
 ) => Mapping T'I'II T'I'II into into (T'I'II into Unit) (T'I'II (U_I_UT'II'I tt t) i) where
 mapping = rewrap `identity` \from -> rewrap
  `li` wrap @into @(U_I_UT'II'I _ _ _ _)
   `compose` fij @into @into identity
   `compose` from
   `compose` yi Unit

instance
 ( Covariant Yoneda Functor into into I
 -- , Covariant Endo Monoidal Functor into tt tt t
 , Covariant Endo Semi Functor into t
 , Adjoint Functor into into (T'II'I tt e) (T'I'II ttt e)
 , Component into I (T'I'II into Unit)
 , Component into (T'I'II into Unit) t
 , forall ee . Wrapper into (I ee)
 , forall ee . Wrapper into (T'I'II into Unit ee)
 , forall ee . Wrapper into (T'TT'I (T'I'II ttt e) (T'II'I tt e) ee)
 , forall ee . Wrapper into (T'TTT'TT'I (T'I'II ttt e) (T'II'I tt e) t ee)
 ) => Mapping T'I'II T'I'II into into (T'I'II into Unit) (T'TTT'TT'I (T'I'II ttt e) (T'II'I tt e) t) where
 mapping = rewrap `identity` \from -> rewrap
  `li` fj @into @into
   (component @into @(T'I'II into Unit) @t
    `compose` component @into @I @(T'I'II into Unit)
    `compose` wrap @into
   ) `compose` from `compose` yi Unit

-- TODO: desugar `fj` and move this instance to `Instances` module
instance
 ( Covariant Endo Semi Functor into t
 , Adjoint Functor into into (T'II'I tt e) (T'I'II ttt e)
 , Covariant Transformation Functor from into (T'II'I tt e `T'TT'I` t) (T'II'I tt e `TT'T'I` t)
 , forall ee . Wrapper into (I ee)
 , forall ee . Wrapper into (T'TT'I (T'II'I tt e) (T'I'II ttt e) ee)
 , forall ee . Wrapper into (T'TT'I (T'I'II ttt e) (T'II'I tt e) ee)
 , forall ee . Wrapper into (T'TT'I (T'II'I tt e) t ee)
 , forall ee . Wrapper into (TT'T'I (T'II'I tt e) t ee)
 , forall ee . Wrapper into (T'TTT'TT'I (T'I'II ttt e) (T'II'I tt e) t ee)
 ) => Mapping T'I'II T'I'II from into t (T'TTT'TT'I (T'I'II ttt e) (T'II'I tt e) t) where
 mapping = rewrap `identity` \from -> wrap @into @(T'TTT'TT'I _ _ _ _)
  `compose` fj (wrapped (map @T'I'II @T'I'II @from @into @(T'II'I tt e `T'TT'I` t) @(T'II'I tt e `TT'T'I` t) from))

instance
 ( Covariant Semi Functor from into t
 , Adjoint Functor into into (T'II'I tt e) (T'I'II ttt e)
 , Covariant Transformation Functor from into (T'II'I tt e `T'TT'I` TT'T'I t tttt) (T'II'I tt e `TT'T'I` TT'T'I t tttt)
 , Component into t (TT'T'I t tttt)
 , forall ee . Wrapper into (I ee)
 , forall ee . Wrapper into (T'TT'I (T'II'I tt e) (T'I'II ttt e) ee)
 , forall ee . Wrapper into (T'TT'I (T'I'II ttt e) (T'II'I tt e) ee)
 , forall ee . Wrapper into (TT'T'I (T'II'I tt e) (TT'T'I t tttt) ee)
 , forall ee . Wrapper into (T'TT'I (T'II'I tt e) (TT'T'I t tttt) ee)
 , forall ee . Wrapper into (TT'T'I (T'II'I tt e) tttt ee)
 , forall ee . Wrapper into (TT'T'I t tttt ee)
 , forall ee . Wrapper into (T'TTT'TT'I (T'I'II ttt e) (T'II'I tt e) (TT'T'I t tttt) ee)
 ) => Mapping T'I'II T'I'II from into t (T'TTT'TT'I (T'I'II ttt e) (T'II'I tt e) (TT'T'I t tttt)) where
 mapping = rewrap `identity` \from -> wrap @into @(T'TTT'TT'I _ _ _ _)
  `compose` fj (wrapped (map @T'I'II @T'I'II @from @into @(T'II'I tt e `T'TT'I` TT'T'I t tttt) @(T'II'I tt e `TT'T'I` TT'T'I t tttt) from))
  `compose` component @into @t @(t `TT'T'I` tttt)

instance
 ( Covariant Semi Functor from into t
 , Adjoint Functor into into (tt) (ttt)
 , Covariant Transformation Functor from into (tt `T'TT'I` TT'T'I tttt t) (tt `TT'T'I` TT'T'I tttt t)
 -- , Component into (tt `T'TT'I` TT'T'I tttt t) (tt `TT'T'I` TT'T'I tttt t)
 , Component into t (TT'T'I tttt t)
 , forall ee . Wrapper into (I ee)
 , forall ee . Wrapper into (T'TT'I (tt) (ttt) ee)
 , forall ee . Wrapper into (T'TT'I (ttt) (tt) ee)
 , forall ee . Wrapper into (TT'T'I (tt) (TT'T'I tttt t) ee)
 , forall ee . Wrapper into (T'TT'I (tt) (TT'T'I tttt t) ee)
 , forall ee . Wrapper into (TT'T'I (tt) tttt ee)
 , forall ee . Wrapper into (TT'T'I tttt t ee)
 , forall ee . Wrapper into (T'TTT'TT'I (ttt) (tt) (TT'T'I tttt t) ee)
 ) => Mapping T'I'II T'I'II from into t (T'TTT'TT'I ttt tt (tttt `TT'T'I` t)) where
 mapping = rewrap `identity` \from -> wrap @into @(T'TTT'TT'I _ _ _ _)
  `compose` fj (wrapped (map @T'I'II @T'I'II @from @into @(tt `T'TT'I` TT'T'I tttt t) @(tt `TT'T'I` TT'T'I tttt t) from))
  `compose` component @into @t @(tttt `TT'T'I` t)

instance
 ( Covariant Semi Functor from (AR) t
 , forall e . Covariant Semi Functor into (AR) (T'I'II from e)
 ) => Mapping T'I'II T'I'II from (AR) t (UU_V_T'I'II_T_II T'I'II into (AR) t r) where
 mapping = rewrap `identity` \from x -> UU_V_T'I'II_T_II (\(T'I'II e) -> fo @from (fio @into @(AR) e from) x)

instance
 ( Covariant Endo Semi Functor (AR) t
 , forall e . Covariant Endo Semi Functor (AR) (T'I'II (AR) e)
 ) => Mapping U_1_I T'I'II (AR) (AR) t (UU_V_T'I'II_T_II U_1_I (AR) (AR) t r) where
 mapping = rewrap `identity` \_ x -> UU_V_T'I'II_T_II (\(U_1_I e) -> (\_ -> e Unit) `fo` x)

instance
 ( Contravariant Semi Functor from (AR) t
 , forall e . Contravariant Semi Functor into (AR) (T'II'I from e)
 ) => Mapping T'II'I T'I'II from (AR) t (UU_V_T'I'II_T_II T'II'I into (AR) t r) where
 mapping = rewrap `identity` \from x -> UU_V_T'I'II_T_II (\(T'II'I e) -> fa @from (fai @into @(AR) e from) x)

instance Mapping T'I'II T'I'II (AR) (AR) (T'I'II (S) e `T'TT'I` L l (T'I'II (S) e)) (T'I'II (S) e) where
 mapping = rewrap `identity` \from -> \case
  T'TT'I (T'I'II (That (Labeled (T'I'II (That x))))) -> T'I'II (That `identity` from x)
  T'TT'I (T'I'II (That (Labeled (T'I'II (This e))))) -> T'I'II (This e)
  T'TT'I (T'I'II (This e)) -> T'I'II (This e)

instance Covariant Lax Monoidal Functor (AR) (AR) (P) P Void t =>
 Mapping T'I'II T'I'II (AR) (AR) (T'I'II (S) e `T'TT'I` l `L` ll `L` t) (T'I'II (S) e `TT'T'I` t) where
 mapping = rewrap `identity` \from -> rewrap `identity` \case
  T'I'II (This e) -> intro `ha` T'I'II `hv` This e
  T'I'II (That x) -> unwrap (unwrap x) `yo` from `ho` That  `ho` T'I'II

instance
 ( Covariant Lax Monoidal Functor (AR) (AR) (P) P Void t
 , Mapping T'I'II T'I'II (AR) (AR) (t `T'TT'I` Void `L` t) t
 , Mapping T'I'II T'I'II (AR) (AR) I (T'I'II (AR) e)
 ) => Mapping T'I'II T'I'II (AR) (AR) (t `T'TT'I` Recursive `L` T'I'II (S) e) t where
 mapping = rewrap `identity` \from -> \(T'TT'I x) ->
  --x `yok_'he'he` Labeled @Void
  x `yok_` Labeled @Void
    `ha__` constant @(AR) (map @T'I'II @T'I'II from (T'TT'I x))
      `la` intro @t @(AR) `ha` from
    `ha__` unwrap @(AR)
    `ha__` unwrap @(AR)

instance
 ( Mapping T'I'II T'I'II (AR) (AR) t t
 , Mapping T'I'II T'I'II (AR) (AR) (t `T'TT'I` L Void t) t
 ) => Mapping T'I'II T'I'II (AR) (AR) (t `T'TT'I` L Recursive I) t where
 mapping = rewrap `identity` \from -> \(T'TT'I x) ->
  -- x `yok'he'he` Labeled @Void `ha` constant @(AR) (map @T'I'II @T'I'II @_ @_ @_ @t from (T'TT'I x))
  x `yok` Labeled @Void `ha` constant @(AR) (map @T'I'II @T'I'II @_ @_ @_ @t from (T'TT'I x)) `ha` unwrap @(AR) `ha` unwrap @(AR)

-- TODO: generalize using adjunctions

instance (e ~ ee) => Mapping T'I'II T'I'II (AR) (AR)
  (Day T'I'II (AR) (P) P (T'I'II (U_I_UT'II'I (AR) (P)) e) (Void `L` T'I'II (U_I_UT'II'I (AR) (P)) ee) eee eeee)
  (T'I'II (U_I_UT'II'I (AR) (P)) e) where
 mapping = rewrap `identity` \from -> rewrap `identity` \case
  These (These ee eee) (T'I'II f) -> U_I_UT'II'I `li` \old ->
   let These x new = ee `he'he'hv` old in
   let These y upd  = eee `he'he'he` new in
   These (from `li` f (These x y)) upd

instance
 ( i ~ ii
 , Covariant Transformation Functor (AR) (AR) (t `T'TT'I` Void `L` t) t
 , Covariant Yoneda Functor (AR) (AR) t
 ) => Mapping T'I'II T'I'II (AR) (AR)
  (Day T'I'II (AR) (P) P
   (T'TTT'TT'I (T'I'II (AR) i) (T'II'I (P) i) t)
   (Void `L` (T'TTT'TT'I (T'I'II (AR) ii) (T'II'I (P) ii) t))
   eee eeee)
  (T'TTT'TT'I (T'I'II (AR) i) (T'II'I (P) i) t) where
 mapping = rewrap `identity` \from -> rewrap `identity` \case
  These (These (T'TTT'TT'I (T'I'II x)) (Labeled (T'TTT'TT'I (T'I'II y)))) (T'I'II f) ->
   T'I'II `identity` \old -> x old `yok` \(T'II'I (These e btw)) ->
    Labeled @Void (from `compose` f `compose` (e `lu`) `fo'fo` y btw)

-- instance
 -- ( Component (AR) (t `T'TT'I` t) t
 -- , Covariant Endo Monoidal Functor (AR) (P) P t
 -- ) => Mapping T'I'II T'I'II (AR) (AR)
  -- (Day T'I'II (AR) (P) P (T'TT'I (T'I'II (AR) a) t) (T'I'II (AR) a `T'TT'I` t) ee eee)
  -- (T'TT'I (T'I'II (AR) a) t) where
 -- mapping = rewrap `identity` \from -> rewrap `identity` \case
  -- These (These (T'TT'I (T'I'II f)) (T'TT'I (T'I'II g))) (T'I'II h) -> T'I'II `identity` \x ->
   -- yp (These (f x) (g x)) `yo` h `ho` from

instance Covariant Lax Monoidal Functor (AR)  (AR) (P) P Void t =>
 Mapping T'I'II T'I'II (AR) (AR) (T'I'II (AR) Unit) (T'I'II (S) e `TT'T'I` t) where
 mapping = rewrap `identity` \from (T'I'II f) ->
  TT'T'I `compose` intro `compose` T'I'II `compose` That `compose` from `identity` f Unit

-- TODO: Finish, it's for Halts transformer
instance Covariant Lax Monoidal Functor (AR)  (AR) (P) P Void t =>
 Mapping T'I'II T'I'II (AR) (AR)
  (Day T'I'II (AR) (P) P (T'I'II (S) e `TT'T'I` t) (Void `L` (T'I'II (S) e `TT'T'I` t)) ee eee)
  (T'I'II (S) e `TT'T'I` t) where
 mapping = rewrap `identity` \from -> rewrap `identity` \case

-- 1. t (tt (t (tt _)))
-- 2. t (t (tt (tt _)))
-- 3. t (t (tt _))
-- 4. t (tt _)
instance
 ( Covariant Endo Semi Functor into t
 , Covariant Endo Semi Functor into tt
 , Component into (t `T'TT'I` t) t
 , Component into (tt `T'TT'I` t) (tt `TT'T'I` t)
 , Covariant Transformation Functor into into (tt `T'TT'I` tt) tt
 , forall e . Wrapper into (((tt `T'TT'I` t) `T'TT'I` (tt `TT'T'I` t)) e)
 , forall e . Wrapper into (((tt `TT'T'I` t) `T'TT'I` (tt `TT'T'I` t)) e)
 , forall e . Wrapper into ((tt `T'TT'I` t) ((tt `TT'T'I` t) e))
 , forall e . Wrapper into ((t `T'TT'I` t) e)
 , forall e . Wrapper into ((tt `TT'T'I` t) e)
 , forall e . Wrapper into ((tt `T'TT'I` t) e)
 , forall e . Wrapper into ((tt `T'TT'I` tt) e)
 ) => Mapping T'I'II T'I'II into into (TT'T'I tt t `T'TT'I` TT'T'I tt t) (TT'T'I tt t) where
 mapping = rewrap `identity` \from -> rewrap
  `li` component @into @(t `T'TT'I` t) @t `compose` wrap @into
  `compose` map @T'I'II @T'I'II @into @into @t @t
  (map @T'I'II @T'I'II @into @into @t @t
    (map @T'I'II @T'I'II @into @into @(tt `T'TT'I` tt) @tt from `compose` wrap @into)
    `compose` wrapped (component @into @(tt `T'TT'I` t) @(tt `TT'T'I` t))
    `compose` map @T'I'II @T'I'II @into @into @tt @tt unwrap
   ) `compose` unwrap @into @(TT'T'I _ _ _)

-- TODO: generalize with limits
instance Covariant Endo Semi Functor (AR) t =>
 Mapping T'I'II T'I'II (AR) (AR) (T'I'II (P) e `T'TT'I` t) (T'I'II (P) e `TT'T'I` t) where
 mapping = rewrap `identity` \from -> rewrap `identity` \case
  T'I'II (These e x) -> x `yo` from `ho` These e `ho` T'I'II

-- TODO: generalize with limits
instance Covariant Endo Semi Functor (AR) t =>
 Mapping T'I'II T'I'II (AR) (AR) (T'II'I (P) e `T'TT'I` Void `L` t) (T'II'I (P) e `TT'T'I` t) where
 mapping = rewrap `identity` \from -> rewrap `identity` \case
  T'II'I (These x e) -> unwrap x `yo` from `ho` (`lu` e) `ho` T'II'I

instance Covariant Endo Semi Functor (AR) t =>
 Mapping T'I'II T'I'II (AR) (AR) (t `T'TT'I` T'I'II (AR) e) (t `TT'T'I` T'I'II (AR) e) where
 mapping = rewrap `identity` \from -> rewrap `identity` \x ->
  T'I'II `identity` \e -> x `yo` from `compose` (`li` e) `compose` unwrap

-- TODO: generalize
-- We need this instance to make `yok'yoklKL` work
-- instance {-# OVERLAPS #-} Component (AR) (T'TT'I t tt) t =>
 -- Mapping T'I'II T'I'II (AR) (AR) (T'TT'I t (Labeled l tt)) t where
 -- mapping = rewrap `identity` \from ->
  -- map @T'I'II @T'I'II @(AR) @(AR) @(T'TT'I t tt) @t from `compose` rewrap @_ @(AR) (fo @(AR) unwrap)

instance
 ( Covariant Lax Monoidal Functor (AR) (AR) (P) P Void t
 , Mapping T'I'II T'I'II (AR) (AR) (T'I'II (AR) Unit) t
 ) => Mapping T'I'II T'I'II (AR) (AR) (T'I'II (AR) Unit) (L l t) where
 mapping = rewrap `identity` \from -> rewrap `identity` \f -> intro `compose` from `identity` f Unit

instance
 ( t ~ tt
 , Covariant Lax Monoidal Functor into into u uu l t
 , Covariant Endo Semi Functor into (T'II'I u ((l `L` t) ee))
 , Covariant Endo Semi Functor into (T'I'II u (L l t e))
 , forall eee . Mapping T'I'II T'I'II into into (T'II'I (P) eee) (T'II'I (P) eee)
 , forall eee . Wrapper into (L l t eee)
 , forall eee . Wrapper into (Day T'I'II into u uu t t e ee eee)
 , forall eee . Wrapper into (Day T'I'II into u uu (L l t) (L l t) e ee eee)
 , forall eee . Wrapper into (Day T'I'II into u uu t (L l t) e ee eee)
 , forall eee eeee . Wrapper into (T'I'II u eee eeee)
 , forall eee eeee . Wrapper into (T'II'I u eee eeee)
 , forall eee eeee . Wrapper into (T'II'I (P) eee eeee)
 ) => Mapping T'I'II T'I'II into into (Day T'I'II into u uu (L l t) (L l tt) e ee) (L l t) where
 mapping = rewrap `identity` \from -> rewrap `li`
   map @T'I'II @T'I'II @into @into @(Day T'I'II into u uu t (l `L` tt) _ _) @t from
   `compose` wrap `compose` foi (foi @into @into unwrap)

instance
 ( Covariant Transformation Functor (AR) (AR) t tt
 , Covariant Transformation Functor (AR) (AR) tt t
 ) => Component (AT) t tt where
 component = U_I_UU_II_T'II'I `identity` \x ->
  map @T'I'II @T'I'II @(AR) @(AR) @t @tt identity x
  `lu` map @T'I'II @T'I'II @(AR) @(AR) @tt @t identity

instance {-# OVERLAPPABLE #-}
 Mapping T'I'II T'I'II (AR) (AR) t t
 => Mapping T'I'II T'I'II (AT) (AR) t t where
 mapping = rewrap `identity` \(U_I_UU_II_T'II'I from) x ->
  map @T'I'II @T'I'II @(AR) @(AR) @t @t (this `compose` from) x

instance Mapping T'II'I T'I'II (AT) (AR)
 (T'II'I (U_I_UT'II'I (AR) (P)) e)
 (T'II'I (U_I_UT'II'I (AR) (P)) e) where
 mapping = rewrap `identity` \(U_I_UU_II_T'II'I from) ->
  rewrap `compose` rewrap `identity` \state old ->
   let (These new f) = from old in f `fio` state new

-- TODO: I'm not sure about this instance
instance Mapping T'II'I T'I'II (AT) (AT)
 (T'II'I (U_I_UT'II'I (AR) (P)) i)
 (T'II'I (U_I_UT'II'I (AR) (P)) i) where
 mapping = rewrap `compose` rewrap `identity` \from x ->
  These (map @T'II'I @T'I'II (U_I_UU_II_T'II'I from) x)
   (constant @(AR) x)

-- a `AR__` o `P` (o `AR` a)

-- (t `T'TT'I` Void `L` ll `L` tt) `AR__` (t `TT'T'I` tt) o `P` ((t `TT'T'I` tt) o `AR` (t `T'TT'I` Void `L` ll `L` tt))

-- instance
 -- ( Mapping T'I'II T'I'II (AR) (AR) (t `TT'T'I` tt) (t `T'TT'I` l `L` ll `L` tt)
 -- , Mapping T'I'II T'I'II (AR) (AR) (t `T'TT'I` l `L` ll `L` tt) (t `TT'T'I` tt)
 -- ) => Mapping T'I'II T'I'II (AT) (AT) (t `T'TT'I` l `L` ll `L` tt) (t `TT'T'I` tt) where
 -- mapping = rewrap `compose` rewrap `identity` \from x ->
  -- map @T'I'II @T'I'II @(AR) @(AR) @(t `T'TT'I` l `L` ll `L` tt) @(t `TT'T'I` tt) (this `ha` from) x
  -- `lu` _

-- TODO: generalize over categories
instance {-# OVERLAPPABLE #-}
 (Setoid (AR) (Supertype e), Wrapper (AR) e)
 => Setoid (AR) e where
 equality (These x xx) = equality (unwrap x `lu` unwrap xx)
  `yoi` (`yoi` wrap @(AR)) `ho` (`yio` wrap @(AR))
  `yio` wrap @(AR)

instance {-# OVERLAPS #-} Setoid (AR) Unit where
 equality _ = That Unit

instance {-# OVERLAPS #-} (Setoid (AR) e, Setoid (AR) ee) => Setoid (AR) (e `S` ee) where
 equality (These (This x) (This xx)) = equality (x `lu` xx) `yoi` (`yio` This) `ho` (`yoi` This) `yio` This
 equality (These (That x) (That xx)) = equality (x `lu` xx) `yoi` (`yio` That) `ho` (`yoi` That) `yio` That
 equality (These x xx) = This (These x xx)

instance {-# OVERLAPS #-} (Setoid (AR) e, Setoid (AR) ee) => Setoid (AR) (e `P` ee) where
 equality (These (These x xx) (These xxx xxxx)) = case equality (x `lu` xxx) `lu` equality (xx `lu` xxxx) of
  These (That x') (That xx') -> That (These x' xx')
  These _ _ -> This ((x `lu` xx) `lu` (xxx `lu` xxxx))
