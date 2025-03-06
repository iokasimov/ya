{-# OPTIONS_GHC -fno-warn-orphans #-}
{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE UndecidableInstances #-}
module Ya.Algebra (module Exports) where

import Ya.Algebra.Abstract as Exports
import Ya.Algebra.Definition as Exports
import Ya.Algebra.Instances as Exports ()
import Ya.Algebra.Operators as Exports

-- 1. t (R_U_I_T_I P t (L l (L ll tt _)))
-- 2. t (tt (R_U_I_T_I P t _))
-- 3. t (L l (L ll tt (R_U_I_T_I P t _)))
-- 4. tt (t (R_U_I_T_I P t _))
instance
 ( Covariant Endo Semi Functor AR t
 , Covariant Endo Monoidal Functor AR P P tt
 , Covariant Transformation Functor AR AR (t `T'TT'I` L l (L ll tt)) (t `TT'T'I` tt)
 , Covariant Transformation Functor AR AR (R_U_I_T_I P t `T'TT'I` L l (L ll tt)) (R_U_I_T_I P t `TT'T'I` tt)
 ) => Mapping U_I_II U_I_II AR AR
  ((t `T'TT'I` R_U_I_T_I P t) `T'TT'I` L l (L ll tt))
  ((t `T'TT'I` R_U_I_T_I P t) `TT'T'I` tt) where
 mapping = rewrap / \from -> rewrap / \x -> unwrap x
  `yo` wrapped (map @U_I_II @U_I_II @AR @AR
   @(R_U_I_T_I P t `T'TT'I` L l (L ll tt))
   @(R_U_I_T_I P t `TT'T'I` tt) from)
  `ho` wrap @AR @(L ll tt (R_U_I_T_I P t _))
  `ho` wrap @AR @(L l (L ll tt) (R_U_I_T_I P t _))
  `yi` wrapped (map @U_I_II @U_I_II @AR @AR @(t `T'TT'I` L l (L ll tt)) @(t `TT'T'I` tt) identity)
  `yo` wrap @AR @(T'TT'I t (R_U_I_T_I P t) _)

-- TODO: reduce a number of transformations here
-- 1. (R_U_I_T_I P t (L l tt _))
-- 2. tt  _ `P` t (Recursive (U_I_T_II t P (L l tt _)))
-- 3. tt _ `P` t (R_U_I_T_I P t (L l tt _))
-- 4. tt _ `P` t (tt (R_U_I_T_I P t _))
-- 5. tt _ `P` t (L l tt (R_U_I_T_I P t _))
-- 6. tt _ `P` tt (t (R_U_I_T_I P t _))
-- 7. tt (R_U_I_T_I P t _)

instance
 ( Covariant Endo Semi Functor AR t
 , Covariant Endo Semi Functor AR tt
 , Covariant Endo Monoidal Functor AR P P tt
 , Covariant Transformation Functor AR AR (t `T'TT'I` Unit `L` ll `L` tt) (t `TT'T'I` tt)
 ) => Mapping U_I_II U_I_II AR AR
  (R_U_I_T_I P t `T'TT'I` L Unit (L ll tt))
  (R_U_I_T_I P t `TT'T'I` tt) where
 mapping = rewrap / \from -> rewrap / \(R_U_I_T_I (Recursive (U_I_T_II (These x xs)))) ->
    unwrap (unwrap x) `yo` from
     `lu_`xs
      `yo` wrap @AR @(R_U_I_T_I _ _ _)
      `ho` wrapped (map @U_I_II @U_I_II @AR @AR @(R_U_I_T_I P t `T'TT'I` L Unit (L ll tt)) @(R_U_I_T_I P t `TT'T'I` tt) from)
      `ho` wrap @AR @(L ll tt _)
      `ho` wrap @AR @(L Unit (L ll tt) _)
      `yi` wrapped (map @U_I_II @U_I_II @AR @AR @(t `T'TT'I` L () (L ll tt)) @(t `TT'T'I` tt) (unwrap @AR @(R_U_I_T_I _ _ _)))
     `yp_'yo` wrap @AR @(R_U_I_T_I _ _ _) `ha` wrap @AR @(Recursive _) `ha` wrap @AR @(U_I_T_II _ _ _ _)

instance
 ( Covariant Endo Semi Functor AR t
 , Covariant Endo Semi Functor AR tt
 , Covariant Endo Monoidal Functor AR P P tt
 , Transformation U_I_II Functor AR AR (t `T'TT'I` L (Unit `P` Unit) (L ll tt)) (t `TT'T'I` tt)
 ) => Mapping U_I_II U_I_II AR AR
  (R_U_I_T_I P t `T'TT'I` L (Unit `P` Unit) (L ll tt))
  (R_U_I_T_I P t `TT'T'I` tt) where
 mapping = rewrap / \from -> rewrap
  / \(R_U_I_T_I (Recursive (U_I_T_II (These x xs)))) ->
   (These
    `ho_'ho` wrap @AR @(U_I_T_II _ _ _ _)
    `ho` wrap @AR @(Recursive _)
    `ho` wrap @AR @(R_U_I_T_I _ _ _))
   `fo` (unwrap (unwrap x) `yo` from)
   `fc` (xs
      `yo` wrap @AR @(R_U_I_T_I _ _ _)
      `ho` wrapped (map @U_I_II @U_I_II @AR @AR
       @(R_U_I_T_I P t `T'TT'I` L (Unit `P` Unit) (L ll tt))
       @(R_U_I_T_I P t `TT'T'I` tt) from)
      `ho` wrap @AR @(L ll tt _)
      `ho` wrap @AR @(L (Unit `P` Unit) (L ll tt) _)
      `yi` wrapped (map @U_I_II @U_I_II @AR @AR @(t `T'TT'I` L (Unit `P` Unit) (L ll tt)) @(t `TT'T'I` tt) (unwrap @AR @(R_U_I_T_I _ _ _)))
    )

-- TODO: try to simplify
instance
 Mapping U_I_II U_I_II AR AR
  (Day U_I_II AR P P t t (Recursive (U_I_T_II t P e)) (Recursive (U_I_T_II t P ee))) t =>
 Mapping U_I_II U_I_II AR AR
  (Day U_I_II AR P P (R_U_I_T_I P t) (R_U_I_T_I P t) e ee) (R_U_I_T_I P t) where
 mapping = rewrap / \from -> rewrap / \case
  These (These e ee) (U_I_II f) ->
   let These e_ e__ = he'he'he e in
   let These ee_ ee__ = he'he'he ee in
   Recursive `compose` U_I_T_II / These
    (from `compose` f / These e_ ee_)
    (day @U_I_II @AR @t @P @P identity
     (unwrap
      `compose` day @U_I_II @AR
       @(R_U_I_T_I P t) @P @P
        identity (from `compose` f)
      `compose` fio R_U_I_T_I
      `compose` foi R_U_I_T_I)
     / These e__ ee__)

instance
 (Initial AR, Covariant Endo Monoidal Functor AR P S t) =>
 Mapping U_I_II U_I_II AR AR (U_I_II AR Unit) (R_U_I_T_I P t) where
 mapping = rewrap / \from (U_I_II f) ->
  R_U_I_T_I `compose` Recursive `compose` U_I_T_II
   / These (from / f Unit) (empty @t `yo` initial' @AR)

instance
 ( Mapping U_I_II U_I_II AR AR (Day U_I_II AR P P t t (R_U_I_T_I P t e) (R_U_I_T_I P t ee)) t
 , Mapping U_I_II U_I_II AR AR (Day U_I_II AR P P t t (Recursive (U_I_T_II t P e)) (Recursive (U_I_T_II t P ee))) t
 ) => Mapping U_I_II U_I_II AR AR (Day U_I_II AR P P (t `T'TT'I` R_U_I_T_I P t) (t `T'TT'I` R_U_I_T_I P t) e ee) (t `T'TT'I` R_U_I_T_I P t) where
 mapping = rewrap / \from -> rewrap / \case
  These (These (T'TT'I e) (T'TT'I ee)) (U_I_II f) ->
    day @U_I_II @AR @t @P @P identity
     (day @U_I_II @AR @(R_U_I_T_I P t) @P @P identity (from `compose` f))
      (These e ee)

instance
 ( Covariant Endo Monoidal Functor AR P P t
 , Covariant Endo Monoidal Functor AR P P (R_U_I_T_I P tt)
 ) => Mapping U_I_II U_I_II AR AR (U_I_II AR Unit) (t `T'TT'I` R_U_I_T_I P tt) where
 mapping = rewrap / \from (U_I_II f) -> T'TT'I /
  enter @t `yu` (enter @(R_U_I_T_I P tt) `yo` from `compose` f)

-- TODO: try to avoid mapping twice datastructure here
instance
 ( Covariant Endo Semi Functor AR t
 , Mapping U_I_II U_I_II AR AR (Day U_I_II AR P SP t t (R_U_I_T_I P t e) (R_U_I_T_I P t ee)) t
 , Mapping U_I_II U_I_II AR AR (Day U_I_II AR P SP t t (Recursive (U_I_T_II t P e)) (Recursive (U_I_T_II t P ee))) t
 ) => Mapping U_I_II U_I_II AR AR (Day U_I_II AR P SP (t `T'TT'I` R_U_I_T_I P t) (t `T'TT'I` R_U_I_T_I P t) e ee) (t `T'TT'I` R_U_I_T_I P t) where
 mapping = rewrap / \from -> rewrap / \case
  These (These (T'TT'I e) (T'TT'I ee)) (U_I_II f) ->
    (day @U_I_II @AR @t @P @SP identity
     (\case
      U_U_I_II_UU_I_II (This (This x)) -> x `yo` from `compose` f `compose` U_U_I_II_UU_I_II `compose` This `compose` This
      U_U_I_II_UU_I_II (This (That x)) -> x `yo` from `compose` f `compose` U_U_I_II_UU_I_II `compose` This `compose` That
      U_U_I_II_UU_I_II (That x) -> day @U_I_II @AR @(R_U_I_T_I P t) @P @SP identity (from `compose` f) x
     )
      (These e ee)
    )

-- TODO: try to avoid mapping twice datastructure here
instance
 ( Covariant Endo Semi Functor AR t
 , Mapping U_I_II U_I_II AR AR (Day U_I_II AR P SP t t (Recursive (U_I_T_II t P e)) (Recursive (U_I_T_II t P ee))) t
 ) => Mapping U_I_II U_I_II AR AR (Day U_I_II AR P SP (R_U_I_T_I P t) (R_U_I_T_I P t) e ee) (R_U_I_T_I P t) where
 mapping = rewrap / \from -> rewrap / \case
  These (These e ee) (U_I_II f) ->
   let These e_ e__ = he'he'he e in
   let These ee_ ee__ = he'he'he ee in
   Recursive `compose` U_I_T_II / These
    (from `compose` f `compose` U_U_I_II_UU_I_II `compose` That / These e_ ee_)
    (day @U_I_II @AR @t @P @SP identity
     (unwrap @AR `compose` \case
      U_U_I_II_UU_I_II (This (This x)) -> R_U_I_T_I x `yo` from `compose` f `compose` U_U_I_II_UU_I_II `compose` This `compose` This
      U_U_I_II_UU_I_II (This (That x)) -> R_U_I_T_I x `yo` from `compose` f `compose` U_U_I_II_UU_I_II `compose` This `compose` That
      U_U_I_II_UU_I_II (That (These x xx)) -> day @U_I_II @AR @(R_U_I_T_I P t) @P @SP identity (from `compose` f)
       (These (R_U_I_T_I x) (R_U_I_T_I xx))
     )
     / These e__ ee__)

instance (Initial AR, Covariant Endo Monoidal Functor AR P S t) =>
 Mapping U_I_II U_I_II AR AR (U_I_II AR Void) (t `T'TT'I` R_U_I_T_I P tt) where
 mapping = rewrap / \_ _ -> T'TT'I (empty @t `yo` initial' @AR)

-- TODO: generalize this instance
instance Mapping U_II_I U_I_II AT AR
 (U_II_I (U_I_UU_II_I AR P) e)
 (U_II_I (U_I_UU_II_I AR P) e) where
 mapping = rewrap / \(U_I_UU_II_U_II_I from) ->
  rewrap `compose` rewrap `identity` \state old ->
   let (These new f) = from old in f `fio` state new

instance Mapping U_I_II U_I_II AT AT (U_I_II P e) (U_I_II P e) where
 mapping = rewrap `compose` rewrap / \from (U_I_II (These e x)) ->
   let s = from x in U_I_II (These e (this s)) `lu` fo (that s)

instance Mapping U_I_II U_I_II AT AT (U_II_I P e) (U_II_I P e) where
 mapping = rewrap `compose` rewrap / \from (U_II_I (These x e)) ->
   let s = from x in U_II_I (These (this s) e) `lu` fo (that s)

-- TODO: I'm not really sure about this instance... it could easily lead to an error!
instance Mapping U_I_II U_I_II AT AT I (U_I_I P) where
 mapping = rewrap `compose` rewrap / \from (Identity x) ->
   let s = from x in U_I_I (this s `lu`this s) `lu` (\(U_I_I (These _ _)) -> Identity (that s (this s)))

instance Mapping U_I_II U_I_II AT AT (U_I_II P e) I where
 mapping = rewrap `compose` rewrap / \from (U_I_II (These e x)) ->
   let s = from x in Identity (this s) `lu` (U_I_II `compose` (e `lu`) `compose` that s `compose` unwrap)

instance Mapping U_I_II U_I_II AT AT (U_II_I P e) I where
 mapping = rewrap `compose` rewrap / \from (U_II_I (These x e)) ->
   let s = from x in Identity (this s) `lu` (U_II_I `compose` (`lu` e) `compose` that s `compose` unwrap)

-- TODO: I should alse test how attributes behave on sums

-- This instance for normal state propagation. How unnormal should look like?
instance (e ~ ee) =>
 Mapping U_I_II U_I_II AR AR
 (U_I_II (U_I_UU_II_I AR P) e `T'TT'I` L Unit `WR` U_I_II (U_I_UU_II_I AR P) ee)
 (U_I_II (U_I_UU_II_I AR P) e) where
 mapping = rewrap / \from -> rewrap `compose` rewrap / \(U_I_UU_II_I state) old ->
    let These trn btw = state old in
    let These res new = unwrap (unwrap (unwrap trn)) btw in
        These (from res) new

instance Mapping U_I_II U_I_II AR AR
 (U_I_II (U_I_UU_II_I AR P) e `T'TT'I` L (Unit `P` Unit) `WR` U_I_II (U_I_UU_II_I AR P) e)
 (U_I_II (U_I_UU_II_I AR P) e) where
 mapping = rewrap / \from -> rewrap `compose` rewrap / \(U_I_UU_II_I state) old ->
    let These trn btw = state old in
    let These res _ = unwrap (unwrap (unwrap trn)) btw in
        These (from res) old

instance (Covariant Endo Monoidal Functor AR P P t, e ~ ee)
 => Mapping U_I_II U_I_II AR AR
  (U_I_II (U_I_UU_II_I AR P) ee)
  (T'TTT'TT'I (U_I_II AR e) (U_II_I P e) t) where
 mapping = rewrap / \from (U_I_II (U_I_UU_II_I x)) ->
  wrap @_ @(T'TTT'TT'I _ _ _ _)
  `compose` wrap @_ @(U_I_II _ _ _)
  `identity` (yu enter
   `compose` map @U_I_II @U_I_II from
   `compose` wrap @_ @(U_II_I _ _ _)
   `compose` x)

instance {-# OVERLAPPABLE #-} Covariant Transformation Functor AR AR (T'TT'I t tt) t => Mapping U_I_II U_I_II AR AR
 (T'TT'I (U_I_II AR e `T'TT'I` t) tt) (U_I_II AR e `T'TT'I` t) where
 mapping = rewrap / \from -> rewrap `compose` rewrap /
  \(U_I_II f) e -> map @U_I_II @U_I_II @AR @AR @(t `T'TT'I` tt) @t from (T'TT'I (f e))

instance {-# OVERLAPS #-} Covariant Endo Semi Functor AR t => Mapping U_I_II U_I_II AR AR
 (T'TT'I (U_I_II AR e `T'TT'I` t) (U_I_II AR e)) (U_I_II AR e `T'TT'I` t) where
 mapping = rewrap / \from -> rewrap `compose` rewrap /
  \(U_I_II f) e -> f e `yo` unwrap @AR `ho` (`li` e) `ho` from

-- NOTE: this version allow different type of states, but it requires providing types to make it compile
-- 1. U_I_II AR old (t (U_II_I P btw))

instance
 ( Covariant Endo Semi Functor AR t
 , Covariant Transformation Functor AR AR (t `T'TT'I` L () t) t
 ) => Mapping U_I_II U_I_II AR AR
 (T'TT'I
  ((U_I_II AR old `T'TTT'TT'I` U_II_I P btw) t)
  (L () ((U_I_II AR btw `T'TTT'TT'I` U_II_I P new) t))
 )
 (T'TTT'TT'I (U_I_II AR old) (U_II_I P new) t) where
 mapping = rewrap / \from -> rewrap `compose` rewrap /
  \(U_I_II x) -> component @AR @(t `T'TT'I` L () t) @t
  `compose` wrap @AR @(T'TT'I t (L () t) _)
  `compose` map @U_I_II @U_I_II @AR @AR @t @t
   (wrap @AR @(L () t _) `compose` fd @AR @AR (unwrap @AR @(T'TTT'TT'I (U_I_II AR btw) (U_II_I P new) t _) `compose` fo from `compose` unwrap @AR @(L () _ _)))
  `compose` x

-- TODO: try to use adjunctions here
instance
 ( Covariant Endo Monoidal Functor AR P P tt
 , Covariant Transformation Functor AR AR (tt `T'TT'I` L () tt) tt
 , e ~ ee
 ) => Mapping U_I_II U_I_II AR AR
 (T'TT'I
  (T'TTT'TT'I (U_I_II AR e) (U_II_I P e) tt)
  (L () (U_I_II (U_I_UU_II_I AR P) ee))
 )
 (T'TTT'TT'I (U_I_II AR e) (U_II_I P e) tt) where
  mapping = rewrap / \from -> rewrap `compose` rewrap / \(U_I_II x) ->
    \old -> x old `yok` \(U_II_I (These (Labeled (U_I_II (U_I_UU_II_I f))) btw))
      -> Labeled @() (yu (enter @tt) / U_II_I (f btw) `yo` from)

instance
 ( Covariant Endo Monoidal Functor AR P P tt
 , Covariant Transformation Functor AR AR (tt `T'TT'I` L () tt) tt
 , e ~ ee
 ) => Mapping U_I_II U_I_II AR AR
 (T'TT'I
  (T'TTT'TT'I (U_I_II AR e) (U_II_I P e) tt)
  (L (() `P` ()) (U_I_II (U_I_UU_II_I AR P) ee))
 )
 (T'TTT'TT'I (U_I_II AR e) (U_II_I P e) tt) where
  mapping = rewrap / \from -> rewrap `compose` rewrap / \(U_I_II x) ->
    \old -> x old `yok` \(U_II_I (These (Labeled (U_I_II (U_I_UU_II_I f))) btw))
      -> Labeled @() (yu (enter @tt) / U_II_I (f btw `yiu` old) `yo` from)

-- TODO: introduce a label
instance
 ( Covariant Functor into into t
 , Covariant Endo Semi Functor into ttt
 , Mapping U_I_II U_I_II into into (t `T'TT'I` L l t) t
 , Mapping U_I_II U_I_II into into (tt `T'TT'I` L l t) (tt `TT'T'I` t)
 , forall ee . Wrapper into ((tt `T'TT'I` L l t) ee)
 , forall ee . Wrapper into (L l t ee)
 , forall ee . Wrapper into (L l t (tt ee))
 , forall ee . Wrapper into (T'TTT'TT'I ttt (tt) t ee)
 , forall ee . Wrapper into ((tt `T'TT'I` t) ee)
 , forall ee . Wrapper into ((tt `TT'T'I` t) ee)
 , forall ee . Wrapper into ((t `T'TT'I` L l t) ee)
 , forall ee . Wrapper into (T'TT'I (T'TTT'TT'I ttt tt t) (L l t) ee)
 ) => Mapping U_I_II U_I_II into into
  (T'TTT'TT'I ttt tt t `T'TT'I` L l t)
  (T'TTT'TT'I ttt tt t) where
 mapping = rewrap / \from -> rewrap /
  map @U_I_II @U_I_II @into @into @ttt
   (component @into @(t `T'TT'I` L l t) @t `compose` wrap @into
    `compose` map @U_I_II @U_I_II @into @into @t
     (wrap @into @(L l t _) `compose` wrapped (map @U_I_II @U_I_II @into @into @(tt `T'TT'I` L l t) @(tt `TT'T'I` t) from))
    )
  `compose` unwrap @into

-- TODO: introduce a label
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
 ) => Mapping U_I_II U_I_II into into
  (T'TTT'TT'I t ttt (TT'T'I tt'tt tt't) `T'TT'I` L l tt't)
  (T'TTT'TT'I t ttt (TT'T'I tt'tt tt't)) where
 mapping = rewrap / \from -> rewrap /
  map @U_I_II @U_I_II @into @into @t @t
   (wrap @into @(TT'T'I _ _ _)
    `compose` component @into @(tt't `T'TT'I` L l tt't) @tt't
    `compose` wrap @into @(T'TT'I tt't (L l tt't) _)
    `compose` map @U_I_II @U_I_II @into @into @tt't @tt't (wrap @into @(L l tt't _))
    `compose` map @U_I_II @U_I_II @into @into @tt't
     (wrapped (component @into @(tt'tt `T'TT'I` L l tt't) @(tt'tt `TT'T'I` tt't))
     `compose` map @U_I_II @U_I_II @into @into @(tt'tt) @(tt'tt) (wrap @into @(L l tt't _)))
    `compose` unwrap @into @(TT'T'I tt'tt tt't _)
    `compose` map @U_I_II @U_I_II @into @into @(TT'T'I tt'tt tt't) @(TT'T'I tt'tt tt't)
     (wrapped (map @U_I_II @U_I_II @into @into @(ttt `T'TT'I` L l tt't) @(ttt `TT'T'I` tt't) from))
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
 ) => Mapping U_I_II U_I_II into into
  (T'TTT'TT'I t tt (TT'T'I ttt't ttt'tt) `T'TT'I` L l ttt't)
  (T'TTT'TT'I t tt (TT'T'I ttt't ttt'tt)) where
 mapping = rewrap / \from -> rewrap /
  map @U_I_II @U_I_II @into @into @t @t
   (wrap @into @(TT'T'I _ _ _)
    `compose` map @U_I_II @U_I_II @into @into @ttt'tt
     (component @into @(ttt't `T'TT'I` L l ttt't) @ttt't
     `compose` wrap @into @(T'TT'I _ _ _)
     `compose` map @U_I_II @U_I_II @into @into @ttt't (wrap @into @(L l ttt't _))
     )
    `compose` unwrap @into @(TT'T'I ttt't ttt'tt _)
    `compose` map @U_I_II @U_I_II @into @into @(ttt't `TT'T'I` ttt'tt) @(ttt't `TT'T'I` ttt'tt)
     (wrapped (map @U_I_II @U_I_II @into @into @(tt `T'TT'I` L l ttt't) @(tt `TT'T'I` ttt't) from))
   )
  `compose` unwrap @into

instance
 ( Covariant Endo Monoidal Functor AR P P t
 , Covariant Endo Semi Functor AR tt
 ) => Mapping U_I_II U_I_II AR AR tt (tt `TT'T'I` t) where
 mapping = rewrap / \from -> wrap @AR @((tt `TT'T'I` t) _)
  `compose` component @AR @(U_I_II AR Unit) @t
  `compose` component @AR @I @(U_I_II AR Unit)
  `compose` wrap @AR
  `compose` map @U_I_II @U_I_II @AR @AR @tt @tt from

-- instance Mapping U_I_II U_I_II AR AR (U_II_I P e `T'TT'I` L (U_I_II S () ()) tt) (U_II_I P e `TT'T'I` tt) =>
 -- Mapping U_I_II U_I_II AR AR
  -- (U_I_II (U_I_UU_II_I AR P) e `T'TT'I` tt)
  -- (T'TTT'TT'I (U_I_II AR e) (U_II_I P e) tt) where
 -- mapping = rewrap / \from (T'TT'I (U_I_II (U_I_UU_II_I x))) ->
  -- T'TTT'TT'I `compose` U_I_II / \old -> wrapped @AR
   -- `li` map @U_I_II @U_I_II @AR @AR @(U_II_I P e `T'TT'I` L (U_I_II S () ()) tt) @(U_II_I P e `TT'T'I` tt) from
   -- `li` U_II_I (x old)

instance Covariant Endo Monoidal Functor AR P P t =>
 Mapping U_I_II U_I_II AR AR (U_I_II AR Unit) (U_I_II AR e `T'TT'I` t) where
 mapping = rewrap / \from -> rewrap / \f -> U_I_II / \_ -> yu enter `compose` from `li` f Unit

instance
 ( Covariant Yoneda Functor into into I
 , Covariant Endo Semi Functor into (U_I_II into e)
 , Adjoint Functor into into (U_II_I t e) (U_I_II tt e)
 , forall ee . Wrapper into (U_II_I t e ee)
 , forall ee . Wrapper into (U_I_II into Unit ee)
 , forall ee . Wrapper into (U_I_II tt e (t ee e))
 , forall ee . Wrapper into (U_I_UU_II_I tt t e ee)
 , forall ee . Wrapper into (U_I_II (U_I_UU_II_I tt t) e ee)
 , forall ee . Wrapper into (T'TT'I (U_I_II tt e) (U_II_I t e) ee)
 , forall ee . Wrapper into (T'TT'I (U_II_I t e) (U_I_II tt e) ee)
 , forall ee . Wrapper into (I ee)
 ) => Mapping U_I_II U_I_II into into (U_I_II into Unit) (U_I_II (U_I_UU_II_I tt t) e) where
 mapping = rewrap `identity` \from -> rewrap
  / wrap @into @(U_I_UU_II_I _ _ _ _)
   `compose` hd @into @into identity
   `compose` from
   `compose` yi Unit

instance
 ( Covariant Yoneda Functor into into I
 , Covariant Endo Monoidal Functor into tt tt t
 , Covariant Endo Semi Functor into t
 , Adjoint Functor into into (U_II_I tt e) (U_I_II ttt e)
 , Component into I (U_I_II into Unit)
 , Component into (U_I_II into Unit) t
 , forall ee . Wrapper into (I ee)
 , forall ee . Wrapper into (U_I_II into Unit ee)
 , forall ee . Wrapper into (T'TT'I (U_I_II ttt e) (U_II_I tt e) ee)
 , forall ee . Wrapper into (T'TTT'TT'I (U_I_II ttt e) (U_II_I tt e) t ee)
 ) => Mapping U_I_II U_I_II into into (U_I_II into Unit) (T'TTT'TT'I (U_I_II ttt e) (U_II_I tt e) t) where
 mapping = rewrap / \from -> rewrap
  / fj @into @into
   (component @into @(U_I_II into Unit) @t
    `compose` component @into @I @(U_I_II into Unit)
    `compose` wrap @into
   ) `compose` from `compose` yi Unit

-- TODO: desugar `fj` and move this instance to `Instances` module
instance
 ( Covariant Endo Semi Functor into t
 , Adjoint Functor into into (U_II_I tt e) (U_I_II ttt e)
 , Covariant Transformation Functor from into (U_II_I tt e `T'TT'I` t) (U_II_I tt e `TT'T'I` t)
 , forall ee . Wrapper into (I ee)
 , forall ee . Wrapper into (T'TT'I (U_II_I tt e) (U_I_II ttt e) ee)
 , forall ee . Wrapper into (T'TT'I (U_I_II ttt e) (U_II_I tt e) ee)
 , forall ee . Wrapper into (T'TT'I (U_II_I tt e) t ee)
 , forall ee . Wrapper into (TT'T'I (U_II_I tt e) t ee)
 , forall ee . Wrapper into (T'TTT'TT'I (U_I_II ttt e) (U_II_I tt e) t ee)
 ) => Mapping U_I_II U_I_II from into t (T'TTT'TT'I (U_I_II ttt e) (U_II_I tt e) t) where
 mapping = rewrap / \from -> wrap @into @(T'TTT'TT'I _ _ _ _)
  `compose` fj (wrapped (map @U_I_II @U_I_II @from @into @(U_II_I tt e `T'TT'I` t) @(U_II_I tt e `TT'T'I` t) from))

instance
 ( Covariant Semi Functor from into t
 , Adjoint Functor into into (U_II_I tt e) (U_I_II ttt e)
 , Covariant Transformation Functor from into (U_II_I tt e `T'TT'I` TT'T'I t tttt) (U_II_I tt e `TT'T'I` TT'T'I t tttt)
 , Component into t (TT'T'I t tttt)
 , forall ee . Wrapper into (I ee)
 , forall ee . Wrapper into (T'TT'I (U_II_I tt e) (U_I_II ttt e) ee)
 , forall ee . Wrapper into (T'TT'I (U_I_II ttt e) (U_II_I tt e) ee)
 , forall ee . Wrapper into (TT'T'I (U_II_I tt e) (TT'T'I t tttt) ee)
 , forall ee . Wrapper into (T'TT'I (U_II_I tt e) (TT'T'I t tttt) ee)
 , forall ee . Wrapper into (TT'T'I (U_II_I tt e) tttt ee)
 , forall ee . Wrapper into (TT'T'I t tttt ee)
 , forall ee . Wrapper into (T'TTT'TT'I (U_I_II ttt e) (U_II_I tt e) (TT'T'I t tttt) ee)
 ) => Mapping U_I_II U_I_II from into t (T'TTT'TT'I (U_I_II ttt e) (U_II_I tt e) (TT'T'I t tttt)) where
 mapping = rewrap / \from -> wrap @into @(T'TTT'TT'I _ _ _ _)
  `compose` fj (wrapped (map @U_I_II @U_I_II @from @into @(U_II_I tt e `T'TT'I` TT'T'I t tttt) @(U_II_I tt e `TT'T'I` TT'T'I t tttt) from))
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
 ) => Mapping U_I_II U_I_II from into t (T'TTT'TT'I ttt tt (tttt `TT'T'I` t)) where
 mapping = rewrap / \from -> wrap @into @(T'TTT'TT'I _ _ _ _)
  `compose` fj (wrapped (map @U_I_II @U_I_II @from @into @(tt `T'TT'I` TT'T'I tttt t) @(tt `TT'T'I` TT'T'I tttt t) from))
  `compose` component @into @t @(tttt `TT'T'I` t)

instance
 ( Covariant Semi Functor from AR t
 , forall e . Covariant Semi Functor into AR (U_I_II from e)
 ) => Mapping U_I_II U_I_II from AR t (UU_V_U_I_II_T_II U_I_II into AR t r) where
 mapping = rewrap / \from x -> UU_V_U_I_II_T_II (\(U_I_II e) -> fo @from (fio @into @AR e from) x)

instance
 ( Covariant Endo Semi Functor AR t
 , forall e . Covariant Endo Semi Functor AR (U_I_II AR e)
 ) => Mapping U_1_I U_I_II AR AR t (UU_V_U_I_II_T_II U_1_I AR AR t r) where
 mapping = rewrap / \_ x -> UU_V_U_I_II_T_II (\(U_1_I e) -> (\_ -> e Unit) `fo` x)

instance
 ( Contravariant Semi Functor from AR t
 , forall e . Contravariant Semi Functor into AR (U_II_I from e)
 ) => Mapping U_II_I U_I_II from AR t (UU_V_U_I_II_T_II U_II_I into AR t r) where
 mapping = rewrap / \from x -> UU_V_U_I_II_T_II (\(U_II_I e) -> fa @from (fai @into @AR e from) x)

instance Mapping U_I_II U_I_II AR AR (U_I_II S e `T'TT'I` L l (U_I_II S e)) (U_I_II S e) where
 mapping = rewrap / \from -> \case
  T'TT'I (U_I_II (That (Labeled (U_I_II (That x))))) -> U_I_II (That / from x)
  T'TT'I (U_I_II (That (Labeled (U_I_II (This e))))) -> U_I_II (This e)
  T'TT'I (U_I_II (This e)) -> U_I_II (This e)

instance Covariant Endo Monoidal Functor AR P P t =>
 Mapping U_I_II U_I_II AR AR (U_I_II S e `T'TT'I` L l (L ll t)) (U_I_II S e `TT'T'I` t) where
 mapping = rewrap / \from -> rewrap / \case
  U_I_II (This e) -> yu enter (U_I_II `li` This e)
  U_I_II (That x) -> unwrap (unwrap x) `yo` from `ho` That  `ho` U_I_II

instance
 ( Covariant Endo Monoidal Functor AR P P t
 , Mapping U_I_II U_I_II AR AR (t `T'TT'I` L () t) t
 , Mapping U_I_II U_I_II AR AR I (U_I_II AR e)
 ) => Mapping U_I_II U_I_II AR AR (t `T'TT'I` L Recursive (U_I_II S e)) t where
 mapping = rewrap / \from -> \(T'TT'I x) ->
  x `yok_'he'he` Labeled @()
    `ha__` constant @AR (map @U_I_II @U_I_II from (T'TT'I x))
      `la` yu (enter @t) `ha` from

instance
 ( Mapping U_I_II U_I_II AR AR t t
 , Mapping U_I_II U_I_II AR AR (t `T'TT'I` L () t) t
 ) => Mapping U_I_II U_I_II AR AR (t `T'TT'I` L Recursive I) t where
 mapping = rewrap / \from -> \(T'TT'I x) ->
  x `yok'he'he` Labeled @() `ha` constant @AR (map @U_I_II @U_I_II @_ @_ @_ @t from (T'TT'I x))

-- TODO: generalize using adjunctions
instance Mapping U_I_II U_I_II AR AR
  (Day U_I_II AR P P
   (U_I_II (U_I_UU_II_I AR P) e)
   (U_I_II (U_I_UU_II_I AR P) e) ee eee)
  (U_I_II (U_I_UU_II_I AR P) e) where
 mapping = rewrap / \from -> rewrap / \case
  These (These ee eee) (U_I_II f) -> U_I_UU_II_I `li` \old ->
   let These x new = ee `he'he` old in
   let These y upd  = eee `he'he` new in
   These (from `li` f (These x y)) upd

instance
 ( Covariant Transformation Functor AR AR (t `T'TT'I` L () t) t
 , Covariant Yoneda Functor AR AR t
 ) => Mapping U_I_II U_I_II AR AR
  (Day U_I_II AR P P
   (T'TTT'TT'I (U_I_II AR e) (U_II_I P e) t)
   (T'TTT'TT'I (U_I_II AR e) (U_II_I P e) t)
   ee eee)
  (T'TTT'TT'I (U_I_II AR e) (U_II_I P e) t) where
 mapping = rewrap / \from -> rewrap / \case
  These (These (T'TTT'TT'I (U_I_II x)) (T'TTT'TT'I (U_I_II y))) (U_I_II f) ->
   U_I_II / \old -> x old `yok` \(U_II_I (These e btw)) ->
    Labeled @() (from `compose` f `compose` (e `lu`) `fo'fo` y btw)

instance
 ( Component AR (t `T'TT'I` t) t
 , Covariant Endo Monoidal Functor AR P P t
 ) => Mapping U_I_II U_I_II AR AR
  (Day U_I_II AR P P (T'TT'I (U_I_II AR a) t) (U_I_II AR a `T'TT'I` t) ee eee)
  (T'TT'I (U_I_II AR a) t) where
 mapping = rewrap / \from -> rewrap / \case
  These (These (T'TT'I (U_I_II f)) (T'TT'I (U_I_II g))) (U_I_II h) -> U_I_II / \x ->
   yp (These (f x) (g x)) `yo` h `ho` from

instance Covariant Endo Monoidal Functor AR P P t =>
 Mapping U_I_II U_I_II AR AR (U_I_II AR Unit) (TT'T'I (U_I_II S e) t) where
 mapping = rewrap / \from (U_I_II f) -> TT'T'I (yu enter (U_I_II (That (from (f Unit)))))

-- TODO: Finish, it's for Halts transformer
instance Covariant Endo Monoidal Functor AR P P t =>
 Mapping U_I_II U_I_II AR AR
  (Day U_I_II AR P P (TT'T'I (U_I_II S e) t) (TT'T'I (U_I_II S e) t) ee eee)
  (TT'T'I (U_I_II S e) t) where
 mapping = rewrap / \from -> rewrap / \case

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
 ) => Mapping U_I_II U_I_II into into (TT'T'I tt t `T'TT'I` TT'T'I tt t) (TT'T'I tt t) where
 mapping = rewrap / \from -> rewrap
  / component @into @(t `T'TT'I` t) @t `compose` wrap @into
  `compose` map @U_I_II @U_I_II @into @into @t @t
  (map @U_I_II @U_I_II @into @into @t @t
    (map @U_I_II @U_I_II @into @into @(tt `T'TT'I` tt) @tt from `compose` wrap @into)
    `compose` wrapped (component @into @(tt `T'TT'I` t) @(tt `TT'T'I` t))
    `compose` map @U_I_II @U_I_II @into @into @tt @tt unwrap
   ) `compose` unwrap @into @(TT'T'I _ _ _)

-- TODO: generalize with limits
instance Covariant Endo Monoidal Functor AR P P t =>
 Mapping U_I_II U_I_II AR AR (U_I_II P e `T'TT'I` t) (U_I_II P e `TT'T'I` t) where
 mapping = rewrap / \from -> rewrap / \case
  U_I_II (These e x) -> x `yo` from `ho` These e `ho` U_I_II

-- TODO: generalize with limits
instance Covariant Endo Monoidal Functor AR P P t =>
 Mapping U_I_II U_I_II AR AR (U_II_I P e `T'TT'I` L () t) (U_II_I P e `TT'T'I` t) where
 mapping = rewrap / \from -> rewrap / \case
  U_II_I (These x e) -> unwrap x `yo` from `ho` (`lu` e) `ho` U_II_I

instance Covariant Endo Semi Functor AR t =>
 Mapping U_I_II U_I_II AR AR (t `T'TT'I` U_I_II AR e) (t `TT'T'I` U_I_II AR e) where
 mapping = rewrap / \from -> rewrap / \x ->
  U_I_II / \e -> x `yo` from `compose` (`li` e) `compose` unwrap

-- TODO: generalize
-- We need this instance to make `yok'yoklKL` work
-- instance {-# OVERLAPS #-} Component AR (T'TT'I t tt) t =>
 -- Mapping U_I_II U_I_II AR AR (T'TT'I t (Labeled l tt)) t where
 -- mapping = rewrap / \from ->
  -- map @U_I_II @U_I_II @AR @AR @(T'TT'I t tt) @t from `compose` rewrap @_ @AR (fo @AR unwrap)

instance Setoid AR i => Setoid AR (I i) where
 equality (These (Identity x) (Identity xx)) = equality (x `lu` xx)
  `yoi` (`yoi` Identity) `ho` (`yio` Identity)
  `yio` Identity

instance Setoid AR Unit where
 equality _ = That Unit

instance (Setoid AR e, Setoid AR ee) => Setoid AR (e `S` ee) where
 equality (These (This x) (This xx)) = equality (x `lu` xx) `yoi` (`yio` This) `ho` (`yoi` This) `yio` This
 equality (These (That x) (That xx)) = equality (x `lu` xx) `yoi` (`yio` That) `ho` (`yoi` That) `yio` That
 equality (These x xx) = This (These x xx)

instance (Setoid AR e, Setoid AR ee) => Setoid AR (e `P` ee) where
 equality (These (These x xx) (These xxx xxxx)) = case equality (x `lu` xxx) `lu`equality (xx `lu` xxxx) of
  These (That x') (That xx') -> That (These x' xx')
  These _ _ -> This ((x `lu` xx) `lu` (xxx `lu` xxxx))

instance
 ( Setoid AR (u e ee)
 ) => Setoid AR (U_I_II u e ee) where
 equality (These x xx) = equality (unwrap x `lu` unwrap xx)
  `yoi` (`yio` U_I_II) `ho` (`yoi` U_I_II) `yio` U_I_II

instance
 ( Setoid AR e
 , Setoid AR (t (Recursive (U_I_T_II t P e)))
 ) => Setoid AR (U_I_T_II t P e (Recursive (U_I_T_II t P e))) where
 equality (These x xx) = equality (unwrap x `lu` unwrap xx)
  `yoi` (`yio` U_I_T_II) `ho` (`yoi` U_I_T_II) `yio` U_I_T_II

instance
 ( Setoid AR e
 , Setoid AR (t (Recursive (U_I_T_II t P e)))
 ) => Setoid AR (Recursive (U_I_T_II t P e)) where
 equality (These x xx) = equality (unwrap x `lu` unwrap xx)
  `yoi` (`yio` Recursive) `ho` (`yoi` Recursive) `yio` Recursive

instance Setoid AR (Recursive (U_I_T_II t P e))
 => Setoid AR (R_U_I_T_I P t e) where
 equality (These x xx) = equality (unwrap x `lu` unwrap xx)
  `yoi` (`yio` R_U_I_T_I) `ho` (`yoi` R_U_I_T_I) `yio` R_U_I_T_I

instance
 ( Covariant Endo Monoidal Functor AR P P t
 , Mapping U_I_II U_I_II AR AR (U_I_II AR Unit) t
 ) => Mapping U_I_II U_I_II AR AR (U_I_II AR Unit) (L l t) where
 mapping = rewrap / \from -> rewrap / \f -> (yu enter `compose` from `li` f Unit)

instance
 ( Mapping U_I_II U_I_II into into (Day U_I_II into u uu t t e ee) t
 , Covariant Endo Semi Functor into (U_II_I u (t ee))
 , Covariant Endo Semi Functor into (U_I_II u (L l t e))
 , forall eee . Mapping U_I_II U_I_II into into (U_II_I P eee) (U_II_I P eee)
 , forall eee . Wrapper into (L l t eee)
 , forall eee . Wrapper into (Day U_I_II into u uu t t e ee eee)
 , forall eee . Wrapper into (Day U_I_II into u uu (L l t) (L l t) e ee eee)
 , forall eee eeee . Wrapper into (U_I_II u eee eeee)
 , forall eee eeee . Wrapper into (U_II_I u eee eeee)
 , forall eee eeee . Wrapper into (U_II_I P eee eeee)
 ) => Mapping U_I_II U_I_II into into (Day U_I_II into u uu (L l t) (L l t) e ee) (L l t) where
 mapping = rewrap / \from -> rewrap /
   map @U_I_II @U_I_II @into @into @(Day U_I_II into u uu t t _ _) @t from
   `compose` wrap `compose` foi (foi @into @into unwrap `compose` fio @into @into unwrap)

instance
 ( Covariant Transformation Functor AR AR t tt
 , Covariant Transformation Functor AR AR tt t
 ) => Component AT t tt where
 component = U_I_UU_II_U_II_I / \x ->
  map @U_I_II @U_I_II @AR @AR @t @tt identity x
  `lu` map @U_I_II @U_I_II @AR @AR @tt @t identity
