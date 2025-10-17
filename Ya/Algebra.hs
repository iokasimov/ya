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
 ( Covariant Endo Semi Functor (AR) t
 , Covariant Endo Semi Functor (AR) tt
 , Covariant Endo Semi Functor (AR) ttt
 , Covariant Transformation Functor (AR) (AR) (t `T'TT'I` ttt `L` ttt `T` lll `L` t `T` l) (t `TT'T'I` ttt)
 , Covariant Transformation Functor (AR) (AR) (tt `T'TT'I` ttt `L` ttt `T` lll `L` tt `T` l) (tt `TT'T'I` ttt)
 , Covariant Lax Monoidal Functor (AR) (AR) (P) (P) lll ttt
 ) => Mapping T'I'II T'I'II (AR) (AR)
  (T'TT'I'TTT'I P t tt `T'TT'I` ttt `L` ttt `T` lll `L` T'TT'I'TTT'I P t tt `T` l)
  (T'TT'I'TTT'I P t tt `TT'T'I` ttt) where
 mapping = rewrap `identity` \from -> rewrap `identity` \(T'TT'I'TTT'I (These x xx)) ->
  x `yo` wrap @(AR) @(ttt `L` ttt `T` lll `L` t `T` l `T` _)
     `ha` unwrap @(AR) @(ttt `L` ttt `T` lll `L` T'TT'I'TTT'I P t tt `T` l `T` _)
     `yi` wrapped (map @T'I'II @T'I'II @(AR) @(AR) @(t `T'TT'I` ttt `L` ttt `T` lll `L` t `T` l) @(t `TT'T'I` ttt) from)
  `lu_`
  xx `yo` wrap @(AR) @(ttt `L` ttt `T` lll `L` tt `T` l `T` _)
     `ha` unwrap @(AR) @(ttt `L` ttt `T` lll `L` T'TT'I'TTT'I P t tt `T` l `T` _)
     `yi` wrapped (map @T'I'II @T'I'II @(AR) @(AR) @(tt `T'TT'I` ttt `L` ttt `T` lll `L` tt `T` l) @(tt `TT'T'I` ttt) from)
     `ho` wrap @(AR) @(ttt `L` ttt `T` lll `T` _)
  `yi_` day @T'I'II @(AR) @lll @ttt @ttt @(P) @(P) identity T'TT'I'TTT'I

instance
 ( Covariant Endo Semi Functor (AR) t
 , Covariant Endo Semi Functor (AR) tt
 , Covariant Endo Semi Functor (AR) ttt
 , Covariant Transformation Functor (AR) (AR) (t `T'TT'I` ttt `L` ttt `T` ll `L` t `T` l) (t `TT'T'I` ttt)
 , Covariant Transformation Functor (AR) (AR) (tt `T'TT'I` ttt `L` ttt `T` ll `L` tt `T` l) (tt `TT'T'I` ttt)
 ) => Mapping T'I'II T'I'II (AR) (AR)
  (T'TT'I'TTT'I S t tt `T'TT'I` ttt `L` ttt `T` ll `L` T'TT'I'TTT'I S t tt `T` l)
  (T'TT'I'TTT'I S t tt `TT'T'I` ttt) where
 mapping = rewrap `identity` \from -> rewrap `identity` \(T'TT'I'TTT'I x) -> case x of
  This xx -> xx
   `yo` wrap @(AR) @(ttt `L` ttt `T` ll `L` t `T` l `T` _)
   `ha` unwrap @(AR) @(ttt `L` ttt `T` ll `L` T'TT'I'TTT'I S t tt `T` l `T` _)
   `yi` wrapped (map @T'I'II @T'I'II @(AR) @(AR) @(t `T'TT'I` ttt `L` ttt `T` ll `L` t `T` l) @(t `TT'T'I` ttt) from)
   `yo` T'TT'I'TTT'I `ha` This
  That xx -> xx
   `yo` wrap @(AR) @(ttt `L` ttt `T` ll `L` tt `T` l `T` _)
   `ha` unwrap @(AR) @(ttt `L` ttt `T` ll `L` T'TT'I'TTT'I S t tt `T` l `T` _)
   `yi` wrapped (map @T'I'II @T'I'II @(AR) @(AR) @(tt `T'TT'I` ttt `L` ttt `T` ll `L` tt `T` l) @(tt `TT'T'I` ttt) from)
   `yo` T'TT'I'TTT'I `ha` That

instance
 ( Covariant Lax Monoidal Functor (AR) (AR) (P) P Void (S'I'II Unit)
 ) => Mapping T'I'II T'I'II (AR) (AR)
 (Day T'I'II (AR) (P) (S) (F'T'I'TT'I (T'II'I P) (S'I'II Unit)) (F'T'I'TT'I (T'II'I P) (S'I'II Unit) `L` F'T'I'TT'I (T'II'I P) (S'I'II Unit) `T` Void) i ii)
 (F'T'I'TT'I (T'II'I P) (S'I'II Unit)) where
 mapping = rewrap `identity` \from -> rewrap `identity` \(These (These i ii) (T'I'II f)) ->
  let These xs x = unwrap `compose` unwrap `compose` unwrap `compose` unwrap `identity` i in
  let These ys _ = unwrap `compose` unwrap `compose` unwrap `compose` unwrap `compose` unwrap `identity` ii in
  Recursive `compose` T'TT'I `compose` T'II'I `identity` These
   (day @T'I'II @(AR) @Void @(S'I'II Unit) @(S'I'II Unit) @(P) @P identity
    (unwrap `compose` day @T'I'II @(AR) @Void @(F'T'I'TT'I (T'II'I P) _) @(F'T'I'TT'I (T'II'I P) _) @(P) @(S) identity (from `compose` f)
     `compose` fio (wrap `compose` F'T'I'TT'I) `compose` foi F'T'I'TT'I)
    `identity` These xs (wrap ys))
   (from `compose` f `identity` This x)

instance
 ( Covariant Lax Monoidal Functor (AR) (AR) (P) P Void (S'I'II Unit)
 -- , Covariant Endo Monoidal Functor (AR) (P) (S) Void (F'T'I'TT'I (T'II'I P) (S'I'II Unit))
 ) => Mapping T'I'II T'I'II (AR) (AR) (Day T'I'II (AR) (P) (S)
  (S'I'II Unit `T'TT'I` F'T'I'TT'I (T'II'I P) (S'I'II Unit))
  ((S'I'II Unit `T'TT'I` F'T'I'TT'I (T'II'I P) (S'I'II Unit)) `L` (S'I'II Unit `T'TT'I` F'T'I'TT'I (T'II'I P) (S'I'II Unit)) `T` Void)
 i ii)
 (S'I'II Unit `T'TT'I` F'T'I'TT'I (T'II'I P) (S'I'II Unit)) where
 mapping = rewrap `identity` \from -> rewrap `identity` \(These (These i (Label ii)) (T'I'II f)) ->
  (day @T'I'II @(AR) @Void @(S'I'II Unit) @(S'I'II Unit) @(P) @P identity
     (day @T'I'II @(AR) @Void @(F'T'I'TT'I (T'II'I P) _) @(F'T'I'TT'I (T'II'I P) _) @(P) @(S) identity (from `compose` f)
  `compose` fio @(AR) wrap)
     `li_` unwrap i `lu` wrap (unwrap ii))

-- 1. t (F'T'I'TT'I (T'II'I P) t ((tt `L` tt `T` ll `L` (t `T'TT'I` F'T'I'TT'I (T'II'I P) t) `T` l `T` _)))
-- 2. t (tt (F'T'I'TT'I (T'II'I P) t _))
-- 3. t (tt `L` tt `T` ll `L` t `T` l `T` (F'T'I'TT'I (T'II'I P) t _))
-- 4. tt (t (F'T'I'TT'I (T'II'I P) t _))

-- TODO: refactor, make these transformations more efficient
instance
 ( Covariant Endo Semi Functor (AR) t
 , Covariant Lax Monoidal Functor (AR) (AR) (P) P Void tt
 , Covariant Transformation Functor (AR) (AR) (t `T'TT'I` tt `L` tt `T` ll `L` t `T` l) (t `TT'T'I` tt)
 , Covariant Transformation Functor (AR) (AR) (F'T'I'TT'I (T'II'I P) t `T'TT'I` tt `L` tt `T` ll `L` F'T'I'TT'I (T'II'I P) t `T` l) (F'T'I'TT'I (T'II'I P) t `TT'T'I` tt)
 ) => Mapping T'I'II T'I'II (AR) (AR)
  ((t `T'TT'I` F'T'I'TT'I (T'II'I P) t) `T'TT'I` tt `L` tt `T` ll `L` (t `T'TT'I` F'T'I'TT'I (T'II'I P) t) `T` l)
  ((t `T'TT'I` F'T'I'TT'I (T'II'I P) t) `TT'T'I` tt) where
 mapping = rewrap `identity` \from -> rewrap `identity` \x -> unwrap x
  `yo'yo` rewrap @(AR) @_ @(tt `L` tt `T` ll `L` F'T'I'TT'I (T'II'I P) t `T` l `T` _) identity
  `yo` wrapped (map @T'I'II @T'I'II @(AR) @(AR)
   @(F'T'I'TT'I (T'II'I P) t `T'TT'I` tt `L` tt `T` ll `L` F'T'I'TT'I (T'II'I P) t `T` l)
   @(F'T'I'TT'I (T'II'I P) t `TT'T'I` tt) from)
  `ho` wrap @(AR) @(tt `L` tt `T` ll `T` _)
  `ho` wrap @(AR) @(tt `L` tt `T` ll `L` t `T` l `T` _)
  `yi` wrapped (map @T'I'II @T'I'II @(AR) @(AR) @(t `T'TT'I` tt `L` tt `T` ll `L` t `T` l) @(t `TT'T'I` tt) identity)
  `yo` wrap @(AR) @(t `T'TT'I` F'T'I'TT'I (T'II'I P) t `T'I_` _)

-- State (List item) `L` State (List item) `T` Void) `L` List `T` (Void `P` Void)

-- TODO: reduce a number of transformations here
-- 1. (F'T'I'TT'I (T'II'I P) t (L l tt _))
-- 2. tt  _ `P` t (Recursive (T'I'TT'II (P) t (L l tt _)))
-- 3. tt _ `P` t (F'T'I'TT'I (T'II'I P) t (L l tt _))
-- 4. tt _ `P` t (tt (F'T'I'TT'I (T'II'I P) t _))
-- 5. tt _ `P` t (L l tt (F'T'I'TT'I (T'II'I P) t _))
-- 6. tt _ `P` tt (t (F'T'I'TT'I (T'II'I P) t _))
-- 7. tt (F'T'I'TT'I (T'II'I P) t _)

instance
 ( Covariant Endo Semi Functor (AR) t
 , Covariant Endo Semi Functor (AR) tt
 , Covariant Lax Monoidal Functor (AR) (AR) (P) P Void tt
 , Covariant Transformation Functor (AR) (AR) (t `T'TT'I` tt `L` tt `T` ll `L` t `T` Void) (t `TT'T'I` tt)
 ) => Mapping T'I'II T'I'II (AR) (AR) (F'T'I'TT'I (T'II'I P) t `T'TT'I` tt `L` tt `T` ll `L` F'T'I'TT'I (T'II'I P) t `T` (Void `P` Void)) (F'T'I'TT'I (T'II'I P) t `TT'T'I` tt) where
 mapping = rewrap `identity` \from -> rewrap `identity` \(F'T'I'TT'I (Recursive (T'TT'I (T'II'I (These xs x))))) ->
    (xs
      `yo` wrap @(AR) @(F'T'I'TT'I _ _ _)
      `ho` wrapped (map @T'I'II @T'I'II @(AR) @(AR)
        @(F'T'I'TT'I (T'II'I P) t `T'TT'I` tt `L` tt `T` ll `L` F'T'I'TT'I (T'II'I P) t `T` (Void `P` Void))
        @(F'T'I'TT'I (T'II'I P) t `TT'T'I` tt) from)
      `ho` wrap @(AR) @(tt `L` tt `T` ll `T` _)
      `ho` wrap @(AR) @(tt `L` tt `T` ll `L` t `T` (Void) `T` _)
      `yi` wrapped (map @T'I'II @T'I'II @(AR) @(AR) @(t `T'TT'I` tt `L` tt `T` ll `L` t `T` (Void)) @(t `TT'T'I` tt) (unwrap @(AR) @(F'T'I'TT'I _ _ _)))
     `lu_` unwrap (unwrap x) `yo` from `yi` wrap @(AR) @(_ `L` _ `T` Void `T` _))
     `yp_'yo` wrap @(AR) @(F'T'I'TT'I _ _ _)
      `ha` wrap @(AR) @(Recursive _)
      `ha` wrap @(AR) @(T'TT'I _ _ _)
      `ha` wrap @(AR) @(T'II'I _ _ _)

instance
 ( Covariant Endo Semi Functor (AR) t
 , Covariant Endo Semi Functor (AR) tt
 , Covariant Lax Monoidal Functor (AR) (AR) (P) P Void tt
 , Transformation T'I'II Functor (AR) (AR) (t `T'TT'I` tt `L` tt `T` ll `L` t `T` Void) (t `TT'T'I` tt)
 ) => Mapping T'I'II T'I'II (AR) (AR)
  (F'T'I'TT'I (T'II'I P) t `T'TT'I` tt `L` tt `T` ll `L` F'T'I'TT'I (T'II'I P) t `T` (Void))
  (F'T'I'TT'I (T'II'I P) t `TT'T'I` tt) where
 mapping = rewrap `identity` \from -> rewrap
  `identity` \(F'T'I'TT'I (Recursive (T'TT'I (T'II'I (These xs x))))) ->
   (These
    `ho_'ho` (wrap @(AR) @(T'TT'I _ _ _) `compose` wrap @(AR) @(T'II'I _ _ _))
    `ho` wrap @(AR) @(Recursive _)
    `ho` wrap @(AR) @(F'T'I'TT'I _ _ _))
   `fo` (xs
      `yo` wrap @(AR) @(F'T'I'TT'I _ _ _)
      `ho` wrapped (map @T'I'II @T'I'II @(AR) @(AR)
       @(F'T'I'TT'I (T'II'I P) t `T'TT'I` tt `L` tt `T` ll `L` F'T'I'TT'I (T'II'I P) t `T` (Void))
       @(F'T'I'TT'I (T'II'I P) t `TT'T'I` tt) from)
      `ho` wrap @(AR) @(tt `L` tt `T` ll `T` _)
      `ho` wrap @(AR) @(tt `L` tt `T` ll `L` t `T` Void `T` _)
      `yi` wrapped (map @T'I'II @T'I'II @(AR) @(AR) @(t `T'TT'I` tt `L` tt `T` ll `L` t `T` Void) @(t `TT'T'I` tt) (unwrap @(AR) @(F'T'I'TT'I _ _ _)))
    )
    `fc` (unwrap (unwrap x) `yo` from)

instance
 ( Covariant Endo Semi Functor (AR) t
 , Covariant Endo Semi Functor (AR) tt
 , Covariant Transformation Functor (AR) (AR) (t `T'TT'I` tt `L` tt `T` ll `L` t `T` Void) (t `TT'T'I` tt)
 ) => Mapping T'I'II T'I'II (AR) (AR)
  (F'T'I'TT'I (T'I'II S) t `T'TT'I` tt `L` tt `T` ll `L` F'T'I'TT'I (T'I'II S) t `T` Void)
  (F'T'I'TT'I (T'I'II S) t `TT'T'I` tt) where
 mapping = rewrap `identity` \from -> rewrap `identity` \(F'T'I'TT'I (Recursive (T'TT'I (T'I'II x)))) -> case x of
  This xx -> unwrap (unwrap xx) `yo` F'T'I'TT'I `ha` Recursive `ha` T'TT'I `ha` T'I'II `ha` This `ha` from
  That xx -> xx
   `yo` F'T'I'TT'I
   `ho` wrapped (map @T'I'II @T'I'II @(AR) @(AR)
    @(F'T'I'TT'I (T'I'II S) t `T'TT'I` tt `L` tt `T` ll `L` F'T'I'TT'I (T'I'II S) t `T` Void)
    @(F'T'I'TT'I (T'I'II S) t `TT'T'I` tt) from)
   `ho` wrap @(AR) @(tt `L` tt `T` ll `T` _)
   `ho` wrap @(AR) @(tt `L` tt `T` ll `L` t `T` Void `T` _)
   `yi` wrapped (map @T'I'II @T'I'II @(AR) @(AR)
     @(t `T'TT'I` tt `L` tt `T` ll `L` t `T` Void)
     @(t `TT'T'I` tt)
     (unwrap @(AR) @(F'T'I'TT'I _ _ _)))
   `yo` F'T'I'TT'I `ha` Recursive `ha` T'TT'I `ha` T'I'II `ha` That

-- TODO: try to simplify
instance
 ( Covariant Lax Monoidal Functor (AR) (AR) (P) P Void t
 , Covariant Lax Monoidal Functor (AR) (AR) (P) P Void (F'T'I'TT'I (T'II'I P) t)
 ) => Mapping T'I'II T'I'II (AR) (AR) (Day T'I'II (AR) (P) P (F'T'I'TT'I (T'II'I P) t) (F'T'I'TT'I (T'II'I P) t `L` F'T'I'TT'I (T'II'I P) t `T` Void) e ee) (F'T'I'TT'I (T'II'I P) t) where
 mapping = rewrap `identity` \from -> rewrap `identity` \case
  These (These e ee) (T'I'II f) ->
   let These e__ e_ = unwrap `compose` unwrap `compose` unwrap `compose` unwrap `identity` e in
   let These ee__ ee_ = unwrap `compose` unwrap `compose` unwrap `compose` unwrap `compose` unwrap `identity` ee in
   Recursive `compose` T'TT'I `compose` T'II'I `identity` These
    (day @T'I'II @(AR) @Void @t @t @(P) @P identity
     (unwrap
      `compose` day @T'I'II @(AR) @Void @(F'T'I'TT'I (T'II'I P) t) @(F'T'I'TT'I (T'II'I P) t) @(P) @P identity (from `compose` f)
      `compose` fio (wrap `compose` F'T'I'TT'I)
      `compose` foi F'T'I'TT'I)
     `identity` These e__ (wrap ee__))
    (from `compose` f `identity` These e_ ee_)

instance (Initial (AR), Covariant Lax Monoidal Functor (AR) (AR) (P) (S) Void t) =>
 Mapping T'I'II T'I'II (AR) (AR) (T'I'II (AR) Unit) (F'T'I'TT'I (T'II'I P) t) where
 mapping = rewrap `identity` \from (T'I'II f) ->
  F'T'I'TT'I `compose` Recursive `compose` T'TT'I `compose` T'II'I
   `identity` These (empty @t `yo` initial' @(AR)) (from `identity` f Unit)

instance
 ( Covariant Lax Monoidal Functor (AR) (AR) (P) P Void t
 , Covariant Lax Monoidal Functor (AR) (AR) (P) P Void (F'T'I'TT'I (T'II'I P) t)
 ) => Mapping T'I'II T'I'II (AR) (AR) (Day T'I'II (AR) (P) P (t `T'TT'I` F'T'I'TT'I (T'II'I P) t) ((t `T'TT'I` F'T'I'TT'I (T'II'I P) t) `L` (t `T'TT'I` F'T'I'TT'I (T'II'I P) t) `T` Void) e ee) (t `T'TT'I` F'T'I'TT'I (T'II'I P) t) where
 mapping = rewrap `identity` \from -> rewrap `identity` \case
  These (These (T'TT'I e) (Label (T'TT'I ee))) (T'I'II f) ->
    day @T'I'II @(AR) @Void @t @t @(P) @P identity
     (day @T'I'II @(AR) @Void @(F'T'I'TT'I (T'II'I P) t) @(F'T'I'TT'I (T'II'I P) t) @(P) @P identity (from `compose` f) `compose` fio @(AR) wrap)
      (These e (wrap ee))

instance
 ( Covariant Lax Monoidal Functor (AR) (AR) (P) P Void t
 , Covariant Lax Monoidal Functor (AR) (AR) (P) P Void (F'T'I'TT'I (T'II'I P) tt)
 ) => Mapping T'I'II T'I'II (AR) (AR) (T'I'II (AR) Unit) (t `T'TT'I` F'T'I'TT'I (T'II'I P) tt) where
 mapping = rewrap `identity` \from (T'I'II f) -> T'TT'I `li`
  intro @t @(AR) `compose` intro @(F'T'I'TT'I (T'II'I P) tt) @(AR) `compose` from `compose` f `identity` Unit

-- TODO: try to avoid mapping a datastructure twice here
instance
 ( Covariant Endo Semi Functor (AR) t
 , Covariant Lax Monoidal Functor (AR) (AR) (P) (R) Void t
 ) => Mapping T'I'II T'I'II (AR) (AR) (Day T'I'II (AR) (P) (R) (t `T'TT'I` F'T'I'TT'I (T'II'I P) t) ((t `T'TT'I` F'T'I'TT'I (T'II'I P) t) `L` (t `T'TT'I` F'T'I'TT'I (T'II'I P) t) `T` Void) e ee) (t `T'TT'I` F'T'I'TT'I (T'II'I P) t) where
 mapping = rewrap `identity` \from -> rewrap `identity` \case
  These (These (T'TT'I e) (Label (T'TT'I ee))) (T'I'II f) ->
    (day @T'I'II @(AR) @Void @t @t @(P) @(R) identity
     (\case
      U_T'I'II_UT'I'II (This (This x)) -> x `yo` from `compose` f `compose` U_T'I'II_UT'I'II `compose` This `compose` This
      U_T'I'II_UT'I'II (This (That x)) -> x `yo` from `compose` f `compose` U_T'I'II_UT'I'II `compose` This `compose` That
      U_T'I'II_UT'I'II (That x) -> day @T'I'II @(AR) @Void @(F'T'I'TT'I (T'II'I P) t) @(F'T'I'TT'I (T'II'I P) t) @(P) @(R) identity (from `compose` f) (fio @(AR) wrap x)
     )
      (These e (wrap @(AR) ee))
    )

-- TODO: try to avoid mapping twice datastructure here
instance
 ( Covariant Endo Semi Functor (AR) t
 , Covariant Lax Monoidal Functor (AR) (AR) (P) (R) Void t
  -- TODO: I hope it doesn't produce cycles
 -- , Covariant Monoidal Functor (AR) (AR) (P) (R) Void (F'T'I'TT'I (T'II'I P) t)
 ) => Mapping T'I'II T'I'II (AR) (AR) (Day T'I'II (AR) (P) (R) (F'T'I'TT'I (T'II'I P) t) (F'T'I'TT'I (T'II'I P) t `L` F'T'I'TT'I (T'II'I P) t `T` Void) e ee) (F'T'I'TT'I (T'II'I P) t) where
 mapping = rewrap `identity` \from -> rewrap `identity` \case
  These (These e ee) (T'I'II f) ->
   let These e__ e_ = unwrap `compose` unwrap `compose` unwrap `compose` unwrap `identity` e in
   let These ee__ ee_ = unwrap `compose` unwrap `compose` unwrap `compose` unwrap `compose` unwrap `identity` ee in
   Recursive `compose` T'TT'I `compose` T'II'I `identity` These
    (day @T'I'II @(AR) @Void @t @t @(P) @(R) identity
     (unwrap @(AR) `compose` \case
      U_T'I'II_UT'I'II (This (This x)) -> F'T'I'TT'I x `yo` from `compose` f `compose` U_T'I'II_UT'I'II `compose` This `compose` This
      U_T'I'II_UT'I'II (This (That x)) -> F'T'I'TT'I x `yo` from `compose` f `compose` U_T'I'II_UT'I'II `compose` This `compose` That
      U_T'I'II_UT'I'II (That (These x xx)) -> day @T'I'II @(AR) @Void @(F'T'I'TT'I (T'II'I P) t) @(F'T'I'TT'I (T'II'I P) t) @(P) @(R) identity (from `compose` f) (F'T'I'TT'I x `lu` wrap (F'T'I'TT'I xx))
     )
     `identity` These e__ (wrap ee__))
    (from `compose` f `compose` U_T'I'II_UT'I'II `compose` That `identity` These e_ ee_)

instance (Initial (AR), Covariant Lax Monoidal Functor (AR) (AR) (P) (S) Void t) =>
 Mapping T'I'II T'I'II (AR) (AR) (T'I'II (AR) Void) (t `T'TT'I` F'T'I'TT'I (T'II'I P) tt) where
 mapping = rewrap `identity` \_ _ -> T'TT'I (empty @t `yo` initial' @(AR))

instance Mapping T'I'II T'I'II (AT) (AT) (P'I'II e) (P'I'II e) where
 mapping = rewrap `compose` rewrap `identity` \from (T'I'II (These e x)) ->
   let s = from x in T'I'II (These e (this s)) `lu` fo (that s)

instance Mapping T'I'II T'I'II (AT) (AT) (T'II'I (P) e) (T'II'I (P) e) where
 mapping = rewrap `compose` rewrap `identity` \from (T'II'I (These x e)) ->
   let s = from x in T'II'I (These (this s) e) `lu` fo (that s)

-- TODO: I'm not really sure about this instance... it could easily lead to an error!
instance Mapping T'I'II T'I'II (AT) (AT) I (T'I'I (P)) where
 mapping = rewrap `compose` rewrap `identity` \from (Identity x) ->
   let s = from x in T'I'I (this s `lu`this s) `lu` (\(T'I'I (These _ _)) -> Identity (that s (this s)))

instance Mapping T'I'II T'I'II (AT) (AT) (P'I'II e) I where
 mapping = rewrap `compose` rewrap `identity` \from (T'I'II (These e x)) ->
   let s = from x in Identity (this s) `lu` (T'I'II `compose` (e `lu`) `compose` that s `compose` unwrap)

instance Mapping T'I'II T'I'II (AT) (AT) (T'II'I (P) e) I where
 mapping = rewrap `compose` rewrap `identity` \from (T'II'I (These x e)) ->
   let s = from x in Identity (this s) `lu` (T'II'I `compose` (`lu` e) `compose` that s `compose` unwrap)

-- TODO: I should alse test how attributes behave on sums

-- This instance for normal state propagation. How unnormal should look like?
instance (e ~ ee) =>
 Mapping T'I'II T'I'II (AR) (AR)
 (T'I'II (T'I'TT'II'I (AR) (P)) e `T'TT'I` T'I'II (T'I'TT'II'I (AR) (P)) ee `L` T'I'II (T'I'TT'II'I (AR) (P)) ee `T` Void)
 (T'I'II (T'I'TT'II'I (AR) (P)) e) where
 mapping = rewrap `identity` \from -> rewrap `compose` rewrap `identity` \(T'I'TT'II'I state) old ->
    let These trn btw = state old in
    let These res new = unwrap (unwrap (unwrap trn)) btw in
        These (from res) new

-- T'I'II (T'I'TT'II'I (AR) (P))

instance (e ~ ee) => Mapping T'I'II T'I'II (AR) (AR)
 (T'I'II (T'I'TT'II'I (AR) (P)) e `T'TT'I` T'I'II (T'I'TT'II'I (AR) (P)) ee `L` T'I'II (T'I'TT'II'I (AR) (P)) ee `T` (Void `P` Void))
 (T'I'II (T'I'TT'II'I (AR) (P)) e) where
 mapping = rewrap `identity` \from -> rewrap `compose` rewrap `identity` \(T'I'TT'II'I state) old ->
    let These trn btw = state old in
    let These res _ = unwrap (unwrap (unwrap trn)) btw in
        These (from res) old

instance (Covariant Lax Monoidal Functor (AR) (AR) (P) (P) Void t, e ~ ee)
 => Mapping T'I'II T'I'II (AR) (AR)
  (T'I'II (T'I'TT'II'I (AR) (P)) ee)
  (T'TTT'TT'I (T'I'II (AR) e) (T'II'I (P) e) t) where
 mapping = rewrap `identity` \from (T'I'II (T'I'TT'II'I x)) ->
  wrap @_ @(T'TTT'TT'I _ _ _ _) `compose` wrap @_ @(T'I'II _ _ _)
  `identity` (intro `compose` map @T'I'II @T'I'II from `compose` wrap @_ @(T'II'I _ _ _) `compose` x)

instance {-# OVERLAPPABLE #-} Covariant Transformation Functor (AR) (AR) (t `T'TT'I` tt `L` tt `T` ll) t => Mapping T'I'II T'I'II (AR) (AR)
 (T'I'II (AR) e `T'TT'I` t `T'TT'I_` tt `L` tt `T` ll) (T'I'II (AR) e `T'TT'I` t) where
 mapping = rewrap `identity` \from -> rewrap `compose` rewrap `identity`
  \(T'I'II f) e -> map @T'I'II @T'I'II @(AR) @(AR) @(t `T'TT'I` tt `L` tt `T` ll) @t from (T'TT'I (f e))

instance {-# OVERLAPS #-}
 Covariant Endo Semi Functor (AR) t
 => Mapping T'I'II T'I'II (AR) (AR) (T'I'II (AR) e `T'TT'I` t `T'TT'I_` T'I'II (AR) e `L` T'I'II (AR) e `T` Void) (T'I'II (AR) e `T'TT'I` t) where
 mapping = rewrap `identity` \from -> rewrap `compose` rewrap `identity`
  \(T'I'II f) e -> f e `yo` unwrap @(AR) `ho` unwrap @(AR) `ho` (`li` e) `ho` from

instance {-# OVERLAPPABLE #-}
 Covariant Transformation Functor (AR) (AR) (t `T'TT'I` t `L` t `T` Void) t
 => Mapping T'I'II T'I'II (AR) (AR) (T'I'II (AR) e `T'TT'I` t `T'TT'I_` (T'I'II (AR) e `T'TT'I` t) `L` (T'I'II (AR) e `T'TT'I` t) `T` Void) (T'I'II (AR) e `T'TT'I` t) where
 mapping = rewrap `identity` \from -> rewrap `compose` rewrap `identity`
  \(T'I'II f) e ->
   map @T'I'II @T'I'II @AR @AR @(t `T'TT'I` t `L` t `T` Void) @t from `compose` wrap
   `compose` map @T'I'II @T'I'II @AR @AR @t @t (wrap @AR @(t `L` t `T` Void `T` _) `compose` yi e `compose` unwrap `compose` unwrap `compose` unwrap)
   `identity` f e

-- NOTE: this version allow different type of states, but it requires providing types to make it compile
-- 1. T'I'II (AR) old (t (T'II'I (P) btw))

instance
 ( Covariant Endo Semi Functor (AR) t
 , Covariant Transformation Functor (AR) (AR) (t `T'TT'I` t `L` t `T` Void) t
 ) => Mapping T'I'II T'I'II (AR) (AR)
 (T'TTT'TT'I (T'I'II (AR) old) (T'II'I (P) btw) t `T'TT'I` (T'TTT'TT'I (T'I'II (AR) btw) (T'II'I (P) new) t `L` T'TTT'TT'I (T'I'II (AR) btw) (T'II'I (P) new) t `T` Void))
 (T'TTT'TT'I (T'I'II (AR) old) (T'II'I (P) new) t) where
 mapping = rewrap `identity` \from -> rewrap `compose` rewrap `identity`
  \(T'I'II x) -> component @(AR) @(t `T'TT'I` t `L` t `T` Void) @t
  `compose` wrap @(AR) @(t `T'TT'I` t `L` t `T` Void `T'I_` _)
  `compose` map @T'I'II @T'I'II @(AR) @(AR) @t @t
   (wrap @(AR) @(t `L` t `T` Void `T` _)
    `compose` fd @(AR) @(AR) (unwrap @(AR) @(T'TTT'TT'I (T'I'II (AR) btw) (T'II'I (P) new) t _)
    `compose` fo from
    `compose` unwrap @(AR) @(_ `L` _ `T` Void `T` _)))
  `compose` x

-- TODO: try to use adjunctions here
instance
 ( Covariant Lax Monoidal Functor (AR) (AR) (P) P Void tt
 , Covariant Transformation Functor (AR) (AR) (tt `T'TT'I` tt `L` tt `T` Void) tt
 , e ~ ee
 ) => Mapping T'I'II T'I'II (AR) (AR)
 (T'TTT'TT'I (T'I'II (AR) e) (T'II'I (P) e) tt `T'TT'I` T'I'II (T'I'TT'II'I (AR) (P)) ee `L` T'I'II (T'I'TT'II'I (AR) (P)) ee `T` Void)
 (T'TTT'TT'I (T'I'II (AR) e) (T'II'I (P) e) tt) where
  mapping = rewrap `identity` \from -> rewrap `compose` rewrap `identity` \(T'I'II x) ->
    \old -> x old `yok` \(T'II'I (These (Label @_ @_ @Void (T'I'II (T'I'TT'II'I f))) btw))
      -> (Label @_ @_ @Void `compose` intro @tt) `identity` (T'II'I (f btw) `yo` from)

instance
 ( Covariant Lax Monoidal Functor (AR) (AR) (P) P Void tt
 , Covariant Transformation Functor (AR) (AR) (tt `T'TT'I` tt `L` tt `T` Void) tt
 , e ~ ee
 ) => Mapping T'I'II T'I'II (AR) (AR)
 (T'TTT'TT'I (T'I'II (AR) e) (T'II'I (P) e) tt `T'TT'I`
  T'I'II (T'I'TT'II'I (AR) (P)) ee `L` T'I'II (T'I'TT'II'I (AR) (P)) ee `T` (Void `P` Void)
 )
 (T'TTT'TT'I (T'I'II (AR) e) (T'II'I (P) e) tt) where
  mapping = rewrap `identity` \from -> rewrap `compose` rewrap `identity` \(T'I'II x) ->
    \old -> x old `yok` \(T'II'I (These (Label @_ @_ @(Void `P` Void) (T'I'II (T'I'TT'II'I f))) btw))
      -> (Label @_ @_ @Void `compose` intro @tt @(AR)) `identity` (T'II'I (f btw `yiu` old) `yo` from)

instance
 ( Covariant Functor into into tt
 , Covariant Functor into into ttt
 , Covariant Endo Semi Functor into t
 , Covariant Endo Transformation Functor into (tt `T'TT'I` tt `L` tt `T` l) tt
 , Covariant Endo Transformation Functor into (ttt `T'TT'I` tt `L` tt `T` l `L` ttt `T` l) (ttt `TT'T'I` tt)
 , forall e . Wrapper into (ttt `T'TT'I` tt `L` tt `T` l `T'I_` e)
 , forall e . Wrapper into (tt `L` tt `T` l `T` e)
 , forall e . Wrapper into (T'TTT'TT'I t ttt tt e)
 , forall e . Wrapper into (ttt `T'TT'I` tt `T'I_` e)
 , forall e . Wrapper into (ttt `TT'T'I` tt `T'I_` e)
 , forall e . Wrapper into (tt `T'TT'I` tt `L` tt `T` l `T'I_` e)
 , forall e . Wrapper into (ttt `T'TT'I` tt `L` tt `T` l `L` ttt `T` l `T'I_` e)
 , forall e . Wrapper into (tt `L` tt `T` l `L` ttt `T` l `T` e)
 , forall e . Wrapper into (T'TTT'TT'I t ttt tt `T'TT'I` tt `L` tt `T` l `T'I_` e)
 ) => Mapping T'I'II T'I'II into into (T'TTT'TT'I t ttt tt `T'TT'I` tt `L` tt `T` l) (T'TTT'TT'I t ttt tt) where
 mapping = rewrap `identity` \from -> rewrap `identity`
  map @T'I'II @T'I'II @into @into @t
   (component @into @(tt `T'TT'I` tt `L` tt `T` l) @tt `compose` wrap @into
    `compose` map @T'I'II @T'I'II @into @into @tt
     (wrap @into @(tt `L` tt `T` l `T` _)
      `compose` wrapped (map @T'I'II @T'I'II @into @into @(ttt `T'TT'I` tt `L` tt `T` l `L` ttt `T` l) @(ttt `TT'T'I` tt) from)
      `compose` map @T'I'II @T'I'II @into @into @ttt (wrap)
     )
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
 , Covariant Endo Semi Functor into ttt
 , Covariant Endo Transformation Functor into (tt't `T'TT'I` tt't `L` tt't `T` l) tt't
 , Covariant Endo  Transformation Functor into (ttt `T'TT'I` tt't `L` tt't `T` l `L` ttt `T` l) (ttt `TT'T'I` tt't)
 , Covariant Endo Transformation Functor into (tt'tt `T'TT'I` tt't `L` tt't `T` l `L` tt'tt `T` Void) (tt'tt `TT'T'I` tt't)
 , forall ee . Wrapper into (tt't `L` tt't `T` l `T` ee)
 , forall ee . Wrapper into (ttt `T'TT'I` tt't `L` tt't `T` l `T'I_` ee)
 , forall ee . Wrapper into (ttt `TT'T'I` tt't `T'I_` ee)
 , forall ee . Wrapper into (tt'tt `T'TT'I` tt't `L` tt't `T` l `T'I_` ee)
 , forall ee . Wrapper into (tt'tt `TT'T'I` tt't `T'I_` ee)
 , forall ee . Wrapper into (tt't `T'TT'I` tt't `L` tt't `T` l `T'I_` ee)
 , forall ee . Wrapper into (tt't `L` tt't `T` l `L` tt'tt `T` Void `T'I_` ee)
 , forall ee . Wrapper into (ttt `T'TT'I` tt't `L` tt't `T` l `L` ttt `T` l `T'I_` ee)
 , forall ee . Wrapper into (tt't `L` tt't `T` l `L` ttt `T` l `T'I_` ee)
 , forall ee . Wrapper into (tt'tt `T'TT'I` tt't `L` tt't `T` l `L` tt'tt `T` Void `T'I_` ee)
 , forall ee . Wrapper into (T'TTT'TT'I t ttt (tt'tt `TT'T'I` tt't) `T'TT'I` tt't `L` tt't `T` l `T'I_` ee)
 , forall ee . Wrapper into (T'TTT'TT'I t ttt (tt'tt `TT'T'I` tt't) ee)
 ) => Mapping T'I'II T'I'II into into
  (T'TTT'TT'I t ttt (tt'tt `TT'T'I` tt't) `T'TT'I` tt't `L` tt't `T` l)
  (T'TTT'TT'I t ttt (tt'tt `TT'T'I` tt't)) where
 mapping = rewrap `identity` \from -> rewrap `identity`
  map @T'I'II @T'I'II @into @into @t @t
   (wrap @into @(TT'T'I _ _ _)
    `compose` component @into @(tt't `T'TT'I` tt't `L` tt't `T` l) @tt't
    `compose` wrap @into @(tt't `T'TT'I` tt't `L` tt't `T` l `T'I_` _)
    `compose` map @T'I'II @T'I'II @into @into @tt't @tt't (wrap @into @(tt't `L` tt't `T` l `T` _))
    `compose` map @T'I'II @T'I'II @into @into @tt't
     (wrapped (component @into @(tt'tt `T'TT'I` tt't `L` tt't `T` l `L` tt'tt `T` Void) @(tt'tt `TT'T'I` tt't))
     `compose` map @T'I'II @T'I'II @into @into @(tt'tt) @(tt'tt)
      (wrap @into `compose` wrap @into @(tt't `L` tt't `T` l `T` _))
    )
    `compose` unwrap @into @(TT'T'I tt'tt tt't _)
    `compose` map @T'I'II @T'I'II @into @into @(TT'T'I tt'tt tt't) @(TT'T'I tt'tt tt't)
     (wrapped (map @T'I'II @T'I'II @into @into @(ttt `T'TT'I` tt't `L` tt't `T` l `L` ttt `T` l) @(ttt `TT'T'I` tt't) from)
     `compose` map @T'I'II @T'I'II @into @into @ttt @ttt wrap)
   )
  `compose` unwrap @into

-- TODO: introduce a label
-- 1. t (ttt'tt (ttt't (tt (ttt't _))))
-- 2. t (ttt'tt (ttt't (ttt't (tt _))))
-- 4. t (ttt'tt (ttt't (tt _)))
instance
 ( Covariant Functor into into ttt't
 , Covariant Endo Semi Functor into t
 , Covariant Endo Semi Functor into tt
 , Covariant Endo Semi Functor into ttt'tt
 , Covariant Endo Transformation Functor into (ttt't `T'TT'I` ttt't `L` ttt't `T` l) ttt't
 , Covariant Endo Transformation Functor into (tt `T'TT'I` ttt't `L` ttt't `T` l `L` tt `T` l) (tt `TT'T'I` ttt't)
 , forall e . Wrapper into ((ttt't `T'TT'I` ttt't `L` ttt't `T` l) e)
 , forall e . Wrapper into ((tt `T'TT'I` ttt't `L` ttt't `T` l `L` tt `T` l) e)
 , forall e . Wrapper into (ttt't `L` ttt't `T` l `T` e)
 , forall e . Wrapper into (ttt't `L` ttt't `T` l `L` tt `T` l `T` e)
 , forall e . Wrapper into (T'TT'I ttt't ttt't e)
 , forall e . Wrapper into (T'TT'I ttt't ttt'tt e)
 , forall e . Wrapper into (T'TT'I (T'TTT'TT'I t tt (TT'T'I ttt't ttt'tt)) (ttt't `L` ttt't `T` l) e)
 , forall e . Wrapper into (TT'T'I tt ttt't e)
 , forall e . Wrapper into (TT'T'I ttt't ttt'tt e)
 , forall e . Wrapper into (T'TTT'TT'I t tt (TT'T'I ttt't ttt'tt) e)
 ) => Mapping T'I'II T'I'II into into
  (T'TTT'TT'I t tt (ttt't `TT'T'I` ttt'tt) `T'TT'I` ttt't `L` ttt't `T` l)
  (T'TTT'TT'I t tt (ttt't `TT'T'I` ttt'tt)) where
 mapping = rewrap `identity` \from -> rewrap `identity`
  map @T'I'II @T'I'II @into @into @t @t
   (wrap @into @(TT'T'I _ _ _)
    `compose` map @T'I'II @T'I'II @into @into @ttt'tt
     (component @into @(ttt't `T'TT'I` ttt't `L` ttt't `T` l) @ttt't
     `compose` wrap @into @(T'TT'I _ _ _)
     `compose` map @T'I'II @T'I'II @into @into @ttt't (wrap @into @(ttt't `L` ttt't `T` l `T` _))
     )
    `compose` unwrap @into @(TT'T'I ttt't ttt'tt _)
    `compose` map @T'I'II @T'I'II @into @into @(ttt't `TT'T'I` ttt'tt) @(ttt't `TT'T'I` ttt'tt)
     (wrapped (map @T'I'II @T'I'II @into @into @(tt `T'TT'I` ttt't `L` ttt't `T` l `L` tt `T` l) @(tt `TT'T'I` ttt't) from) `compose` map @T'I'II @T'I'II @into @into @tt @tt wrap)
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

-- instance Mapping T'I'II T'I'II (AR) (AR) (T'II'I (P) e `T'TT'I` L (S'I'II () ()) tt) (T'II'I (P) e `TT'T'I` tt) =>
 -- Mapping T'I'II T'I'II (AR) (AR)
  -- (T'I'II (T'I'TT'II'I (AR) (P)) e `T'TT'I` tt)
  -- (T'TTT'TT'I (T'I'II (AR) e) (T'II'I (P) e) tt) where
 -- mapping = rewrap `identity` \from (T'TT'I (T'I'II (T'I'TT'II'I x))) ->
  -- T'TTT'TT'I `compose` T'I'II `identity` \old -> wrapped @(AR)
   -- `li` map @T'I'II @T'I'II @(AR) @(AR) @(T'II'I (P) e `T'TT'I` L (S'I'II () ()) tt) @(T'II'I (P) e `TT'T'I` tt) from
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
 , forall e . Wrapper into (T'I'TT'II'I tt t i e)
 , forall e . Wrapper into (T'I'II (T'I'TT'II'I tt t) i e)
 , forall e . Wrapper into (T'TT'I (T'I'II tt i) (T'II'I t i) e)
 , forall e . Wrapper into (T'TT'I (T'II'I t i) (T'I'II tt i) e)
 , forall e . Wrapper into (I e)
 ) => Mapping T'I'II T'I'II into into (T'I'II into Unit) (T'I'II (T'I'TT'II'I tt t) i) where
 mapping = rewrap `identity` \from -> rewrap
  `li` wrap @into @(T'I'TT'II'I _ _ _ _)
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

instance Mapping T'I'II T'I'II (AR) (AR) (S'I'II e `T'TT'I` S'I'II e `L` S'I'II e `T` l) (S'I'II e) where
 mapping = rewrap `identity` \from -> \case
  T'TT'I (T'I'II (That (Label (T'I'II (That x))))) -> T'I'II (That `identity` from x)
  T'TT'I (T'I'II (That (Label (T'I'II (This e))))) -> T'I'II (This e)
  T'TT'I (T'I'II (This e)) -> T'I'II (This e)

instance Covariant Lax Monoidal Functor (AR) (AR) (P) P Void t =>
 Mapping T'I'II T'I'II (AR) (AR) (S'I'II e `T'TT'I` t `L` t `T` ll `L` S'I'II e `T` l) (S'I'II e `TT'T'I` t) where
 mapping = rewrap `identity` \from -> rewrap `identity` \case
  T'I'II (This e) -> intro `ha` T'I'II `hv` This e
  T'I'II (That x) -> unwrap (unwrap x) `yo` from `ho` That  `ho` T'I'II

 -- (T'TT'I
 --  (T'TTT'TT'I (T'I'II AR shift) (T'II'I P shift) (T'I Reach shift)) 
 --  (T'TTT'TT'I (T'I'II AR shift) (T'II'I P shift) (T'I Reach shift) `L` T'TTT'TT'I (T'I'II AR shift) (T'II'I P shift) (T'I Reach shift) `T` Void)
 -- )
 -- (T'TTT'TT'I (T'I'II AR shift) (T'II'I P shift) (T'I Reach shift))

instance
 ( Covariant Lax Monoidal Functor (AR) (AR) (P) P Void t
 , Mapping T'I'II T'I'II (AR) (AR) (t `T'TT'I` t `L` t `T` Void) t
 , Mapping T'I'II T'I'II (AR) (AR) I (T'I'II (AR) e)
 ) => Mapping T'I'II T'I'II (AR) (AR) (t `T'TT'I` S'I'II e `L` S'I'II e `T` Recursive) t where
 mapping = rewrap `identity` \from -> \(T'TT'I x) ->
  x `yok_` Label @_ @_ @Void
    `ha__` constant @(AR) (map @T'I'II @T'I'II from (T'TT'I x))
      `la` intro @t @(AR) `ha` from
    `ha__` unwrap @(AR)
    `ha__` unwrap @(AR)

instance
 ( Mapping T'I'II T'I'II (AR) (AR) t t
 , Mapping T'I'II T'I'II (AR) (AR) (t `T'TT'I` t `L` t `T` Void) t
 ) => Mapping T'I'II T'I'II (AR) (AR) (t `T'TT'I` I `L` I `T` Recursive) t where
 mapping = rewrap `identity` \from -> \(T'TT'I x) ->
  -- x `yok'he'he` Label `ha` constant @(AR) (map @T'I'II @T'I'II @_ @_ @_ @t from (T'TT'I x))
  x `yok` Label @_ @_ @Void `ha` constant @(AR) (map @T'I'II @T'I'II @_ @_ @_ @t from (T'TT'I x)) `ha` unwrap @(AR) `ha` unwrap @(AR)

-- TODO: generalize using adjunctions

instance (e ~ ee) => Mapping T'I'II T'I'II (AR) (AR)
  (Day T'I'II (AR) (P) P (T'I'II (T'I'TT'II'I (AR) (P)) e) (T'I'II (T'I'TT'II'I (AR) (P)) ee `L` T'I'II (T'I'TT'II'I (AR) (P)) ee `T` Void) eee eeee)
  (T'I'II (T'I'TT'II'I (AR) (P)) e) where
 mapping = rewrap `identity` \from -> rewrap `identity` \case
  These (These ee eee) (T'I'II f) -> T'I'TT'II'I `li` \old ->
   let These x new = ee `he'he'hv` old in
   let These y upd  = eee `he'he'he` new in
   These (from `li` f (These x y)) upd

instance (e ~ ee) => Mapping T'I'II T'I'II (AR) (AR)
  (Day T'I'II (AR) (P) P (T'I'II (T'I'TT'II'I (AR) (P)) e) (T'I'II (T'I'TT'II'I (AR) (P)) ee `L` T'I'II (T'I'TT'II'I (AR) (P)) ee `T` (Void `P` Void)) eee eeee)
  (T'I'II (T'I'TT'II'I (AR) (P)) e) where
 mapping = rewrap `identity` \from -> rewrap `identity` \case
  These (These ee eee) (T'I'II f) -> T'I'TT'II'I `li` \old ->
   let These x _ = ee `he'he'hv` old in
   let These y _  = eee `he'he'he` old in
   These (from `li` f (These x y)) old

instance
 ( i ~ ii
 , Covariant Transformation Functor (AR) (AR) (t `T'TT'I` t `L` t `T` Void) t
 , Covariant Yoneda Functor (AR) (AR) t
 ) => Mapping T'I'II T'I'II (AR) (AR)
  (Day T'I'II (AR) (P) P (T'TTT'TT'I (T'I'II (AR) i) (T'II'I (P) i) t)
   (T'TTT'TT'I (T'I'II (AR) ii) (T'II'I (P) ii) t `L` T'TTT'TT'I (T'I'II (AR) ii) (T'II'I (P) ii) t `T` Void) eee eeee)
  (T'TTT'TT'I (T'I'II (AR) i) (T'II'I (P) i) t) where
 mapping = rewrap `identity` \from -> rewrap `identity` \case
  These (These (T'TTT'TT'I (T'I'II x)) (Label (T'TTT'TT'I (T'I'II y)))) (T'I'II f) ->
   T'I'II `identity` \old -> x old `yok` \(T'II'I (These e btw)) ->
    Label @_ @_ @Void (from `compose` f `compose` (e `lu`) `fo'fo` y btw)

instance
 ( i ~ ii
 , Covariant Transformation Functor (AR) (AR) (t `T'TT'I` t `L` t `T` Void) t
 , forall e ee . Mapping T'I'II T'I'II (AR) (AR) (Covariant Day (AR) (P) (P) t (t `L` t `T` Void) e ee) t
 , Covariant Yoneda Functor (AR) (AR) t
 ) => Mapping T'I'II T'I'II (AR) (AR)
  (Day T'I'II (AR) (P) P (T'TTT'TT'I (T'I'II (AR) i) (T'II'I (P) i) t) (t `L` t `T` Void) eee eeee)
  (T'TTT'TT'I (T'I'II (AR) i) (T'II'I (P) i) t) where
 mapping = rewrap `identity` \from -> rewrap `identity` \case
  These (These (T'TTT'TT'I (T'I'II x)) xx) (T'I'II f) ->
   T'I'II `identity` \old ->
    day @T'I'II @(AR) @Void @t @t @(P) @(P) identity
    (\(These i ii) -> i `yo` (`lu` ii) `ho` f `ho` from)
    (x old `lu` xx)

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
 Mapping T'I'II T'I'II (AR) (AR) (T'I'II (AR) Unit) (S'I'II e `TT'T'I` t) where
 mapping = rewrap `identity` \from (T'I'II f) ->
  TT'T'I `compose` intro `compose` T'I'II `compose` That `compose` from `identity` f Unit

-- TODO: Finish, it's for Halts transformer
instance Covariant Lax Monoidal Functor (AR)  (AR) (P) P Void t =>
 Mapping T'I'II T'I'II (AR) (AR)
  (Day T'I'II (AR) (P) P (S'I'II e `TT'T'I` t) ((S'I'II e `TT'T'I` t) `L` (S'I'II e `TT'T'I` t) `T` Void) ee eee)
  (S'I'II e `TT'T'I` t) where
 mapping = rewrap `identity` \from -> rewrap `identity` \case

-- 1. t (tt (t (tt _)))
-- 2. t (t (tt (tt _)))
-- 3. t (t (tt _))
-- 4. t (tt _)
-- instance
--  ( Covariant Endo Semi Functor into t
--  , Covariant Endo Semi Functor into tt
--  , Covariant Endo Transformation Functor into (t `T'TT'I` t `L` t `T` Void) t
--  , Covariant Endo Transformation Functor into (tt `T'TT'I` t `L` t `T` Void `L` tt `T` Void) (tt `TT'T'I` t)
--  , Covariant Endo Transformation Functor into (tt `T'TT'I` tt) tt
--  , forall e . Wrapper into (((tt `T'TT'I` t) `T'TT'I` (tt `TT'T'I` t)) e)
--  , forall e . Wrapper into (((tt `TT'T'I` t) `T'TT'I` (tt `TT'T'I` t) `L` (tt `TT'T'I` t) `T` Void) e)
--  , forall e . Wrapper into ((tt `T'TT'I` t) ((tt `TT'T'I` t) e))
--  , forall e . Wrapper into (t `T'TT'I` t `L` t `T` Void `T'I_` e)
--  , forall e . Wrapper into (tt `TT'T'I` t `T'I_` e)
--  , forall e . Wrapper into (tt `T'TT'I` t `L` t `T` Void `L` tt `T` Void `T'I_` e)
--  , forall e . Wrapper into (tt `T'TT'I` t `L` t `T` Void `T'I_` e)
--  , forall e . Wrapper into (tt `T'TT'I` tt `T'I_` e)
--  , forall e . Wrapper into (t `L` t `T` Void `L` tt `T` Void `T` e)
--  , forall e . Wrapper into (t `L` t `T` Void `T` e)
--  , forall e . Wrapper into ((tt `TT'T'I` t) `L` (tt `TT'T'I` t) `T` Void `T` e)
--  ) => Mapping T'I'II T'I'II into into ((tt `TT'T'I` t) `T'TT'I` (tt `TT'T'I` t) `L` (tt `TT'T'I` t) `T` Void) (tt `TT'T'I` t) where
--  mapping = rewrap `identity` \from -> rewrap
--   `li` component @into @(t `T'TT'I` t `L` t `T` Void) @t
--   `compose` wrap @into
--   `compose` map @T'I'II @T'I'II @into @into @t @t
--   (wrap @_ @(t `L` t `T` Void `T` _)
--    `compose` map @T'I'II @T'I'II @into @into @t @t
--     (map @T'I'II @T'I'II @into @into @(tt `T'TT'I` tt) @tt from `compose` wrap @into)
--     `compose` wrapped (component @into @(tt `T'TT'I` t `L` t `T` Void `L` tt `T` Void) @(tt `TT'T'I` t))
--     `compose` map @T'I'II @T'I'II @into @into @tt @tt
--      (wrap @into @(t `L` t `T` Void `L` tt `T` Void `T` _) `compose` wrap @into @(t `L` t `T` Void `T` _) `compose` unwrap `compose` unwrap)
--    )
--    `compose` unwrap @into @(TT'T'I _ _ _)

-- TODO: generalize with limits
instance Covariant Endo Semi Functor (AR) t =>
 Mapping T'I'II T'I'II (AR) (AR) (P'I'II e `T'TT'I` t `L` t `T` Void `L` P'II'I e `T` Void) (P'I'II e `TT'T'I` t) where
 mapping = rewrap `identity` \from -> rewrap `identity` \case
  T'I'II (These e x) -> unwrap (unwrap x) `yo` from `ho` These e `ho` T'I'II

-- TODO: generalize with limits
instance Covariant Endo Semi Functor (AR) t =>
 Mapping T'I'II T'I'II (AR) (AR) (P'II'I e `T'TT'I` t `L` t `T` Void `L` P'II'I e `T` Void) (P'II'I e `TT'T'I` t) where
 mapping = rewrap `identity` \from -> rewrap `identity` \case
  T'II'I (These x e) -> unwrap (unwrap x) `yo` from `ho` (`lu` e) `ho` T'II'I

-- instance Covariant Endo Semi Functor (AR) t =>
--  Mapping T'I'II T'I'II (AR) (AR) (t `T'TT'I` T'I'II (AR) e `L` T'I'II (AR) e `T` Void `L` t `T` Void) (t `TT'T'I` T'I'II (AR) e) where
--  mapping = rewrap `identity` \from -> rewrap `identity` \x ->
--   T'I'II `identity` \e -> x `yo` from `compose` (`li` e) `compose` unwrap

-- TODO: generalize
-- We need this instance to make `yok'yoklKL` work
-- instance {-# OVERLAPS #-} Component (AR) (T'TT'I t tt) t =>
 -- Mapping T'I'II T'I'II (AR) (AR) (T'TT'I t (Label l tt)) t where
 -- mapping = rewrap `identity` \from ->
  -- map @T'I'II @T'I'II @(AR) @(AR) @(T'TT'I t tt) @t from `compose` rewrap @_ @(AR) (fo @(AR) unwrap)

instance
 ( Covariant Lax Monoidal Functor (AR) (AR) (P) P Void t
 , Mapping T'I'II T'I'II (AR) (AR) (T'I'II (AR) Unit) t
 ) => Mapping T'I'II T'I'II (AR) (AR) (T'I'II (AR) Unit) (t `L` t `T` l) where
 mapping = rewrap `identity` \from -> rewrap `identity` \f -> intro `compose` from `identity` f Unit

instance
 ( forall e ee . Covariant Transformation Functor into into (Covariant Day into u uu t (tt `L` tt `T` ll) e ee) t
 , Covariant Endo Semi Functor into (T'II'I u (tt `L` tt `T` ll `T` ee))
 , Covariant Endo Semi Functor into (T'I'II u (t `L` t `T` l `T` e))
 , forall eee . Mapping T'I'II T'I'II into into (T'II'I (P) eee) (T'II'I (P) eee)
 , forall eee . Wrapper into (t `L` t `T` l `T` eee)
 , forall eee . Wrapper into (Day T'I'II into u uu t t e ee eee)
 , forall eee . Wrapper into (Day T'I'II into u uu (t `L` t `T` l) (tt `L` tt `T` ll) e ee eee)
 , forall eee . Wrapper into (Day T'I'II into u uu t (tt `L` tt `T` ll) e ee eee)
 , forall eee eeee . Wrapper into (T'I'II u eee eeee)
 , forall eee eeee . Wrapper into (T'II'I u eee eeee)
 , forall eee eeee . Wrapper into (T'II'I (P) eee eeee)
 ) => Mapping T'I'II T'I'II into into (Day T'I'II into u uu (t `L` t `T` l) (tt `L` tt `T` ll) e ee) (t `L` t `T` l) where
 mapping = rewrap `identity` \from -> rewrap `li`
   map @T'I'II @T'I'II @into @into @(Day T'I'II into u uu t (tt `L` tt `T` ll) _ _) @t from
   `compose` wrap `compose` foi (foi @into @into unwrap)

instance
 ( Covariant Transformation Functor (AR) (AR) t tt
 , Covariant Transformation Functor (AR) (AR) tt t
 ) => Component (AT) t tt where
 component = T'I'TT'II'T'II'I `identity` \x ->
  map @T'I'II @T'I'II @(AR) @(AR) @t @tt identity x
  `lu` map @T'I'II @T'I'II @(AR) @(AR) @tt @t identity

instance {-# OVERLAPPABLE #-}
 Mapping T'I'II T'I'II (AR) (AR) t t
 => Mapping T'I'II T'I'II (AT) (AR) t t where
 mapping = rewrap `identity` \(T'I'TT'II'T'II'I from) x ->
  map @T'I'II @T'I'II @(AR) @(AR) @t @t (this `compose` from) x

instance Mapping T'II'I T'I'II (AT) (AR)
 (T'II'I (T'I'TT'II'I (AR) (P)) e)
 (T'II'I (T'I'TT'II'I (AR) (P)) e) where
 mapping = rewrap `identity` \(T'I'TT'II'T'II'I from) ->
  rewrap `compose` rewrap `identity` \state old ->
   let (These new f) = from old in f `fio` state new

-- TODO: I'm not sure about this instance
instance Mapping T'II'I T'I'II (AT) (AT)
 (T'II'I (T'I'TT'II'I (AR) (P)) i)
 (T'II'I (T'I'TT'II'I (AR) (P)) i) where
 mapping = rewrap `compose` rewrap `identity` \from x ->
  These (map @T'II'I @T'I'II (T'I'TT'II'T'II'I from) x)
   (constant @(AR) x)

-- instance
 -- ( Mapping T'I'II T'I'II (AR) (AR) (t `TT'T'I` tt) (t `T'TT'I` tt `L` tt `T` ll `L` t `T` l)
 -- , Mapping T'I'II T'I'II (AR) (AR) (t `T'TT'I` tt `L` tt `T` ll `L` t `T` l) (t `TT'T'I` tt)
 -- ) => Mapping T'I'II T'I'II (AT) (AT) (t `T'TT'I` tt `L` tt `T` ll `L` t `T` l) (t `TT'T'I` tt) where
 -- mapping = rewrap `compose` rewrap `identity` \from x ->
  -- map @T'I'II @T'I'II @(AR) @(AR) @(t `T'TT'I` tt `L` tt `T` ll `L` t `T` l) @(t `TT'T'I` tt) (this `ha` from) x
  -- `lu` _

-- TODO: try to generalise
instance
 ( Covariant Endo Semi Functor (AR) t
 , Covariant Endo Semi Functor (AR) tt
 , Mapping T'I'II T'I'II (AR) (AR) t (t `T'TT'I` t `L` t `T` Void)
 , Mapping T'I'II T'I'II (AR) (AR) tt (tt `T'TT'I` tt `L` tt `T` Void)
 ) => Mapping T'I'II T'I'II (AR) (AR) (t `S'T'I'TT'I` tt) ((t `S'T'I'TT'I` tt) `T'TT'I` (t `S'T'I'TT'I` tt) `L` (t `S'T'I'TT'I` tt) `T` Void) where
 mapping = rewrap `hv` \from -> T'TT'I'TTT'I `ho` T'TT'I
  `ha____` map @T'I'II @T'I'II @AR @AR @t @(t `T'TT'I` t `L` t `T` Void) from
    `ho__` unwrap @AR @(t `T'TT'I` t `L` t `T` Void `T'I_` _)
    `ho__'yo` rewrap @AR @(t `L` t `T` Void `T` _) @((t `S'T'I'TT'I` tt) `L` (t `S'T'I'TT'I` tt) `T` Void `T` _) `hv_` This `ho` T'TT'I'TTT'I
    `ho__` This
    `la__` map @T'I'II @T'I'II @AR @AR @tt @(tt `T'TT'I` tt `L` tt `T` Void) from
    `ho__` unwrap @AR @(tt `T'TT'I` tt `L` tt `T` Void `T'I_` _)
    `ho__'yo` rewrap @AR @(tt `L` tt `T` Void `T` _) @((t `S'T'I'TT'I` tt) `L` (t `S'T'I'TT'I` tt) `T` Void `T` _) `hv_` That `ho` T'TT'I'TTT'I
    `ho__` That

-- TODO: try to generalise
instance
 ( Covariant Endo Semi Functor (AR) t
 , Covariant Endo Semi Functor (AR) tt
 , Mapping T'I'II T'I'II (AR) (AR) t (t `T'TT'I` t `L` t `T` Void)
 , Mapping T'I'II T'I'II (AR) (AR) tt (tt `T'TT'I` tt `L` tt `T` Void)
 ) => Mapping T'I'II T'I'II (AR) (AR) (t `P'T'I'TT'I` tt) ((t `P'T'I'TT'I` tt) `T'TT'I` (t `P'T'I'TT'I` tt) `L` (t `P'T'I'TT'I` tt) `T` Void) where
 mapping = rewrap `hv` \from -> T'TT'I'TTT'I `ho` T'TT'I
  `ha____` (is `ho'he` this
    `ho` map @T'I'II @T'I'II @AR @AR @t @(t `T'TT'I` t `L` t `T` Void) from
    `ho` unwrap @AR @(t `T'TT'I` t `L` t `T` Void `T'I_` _)
    `lo` is `ho'he` that `ho'yo` from
   `ho__` (\(These x xx) -> x `yo` rewrap ((`lu_` xx) `ho` T'TT'I'TTT'I)))
   `lo__` (is `ho'he` that
    `ho` map @T'I'II @T'I'II @AR @AR @tt @(tt `T'TT'I` tt `L` tt `T` Void) from
    `ho` unwrap @AR @(tt `T'TT'I` tt `L` tt `T` Void `T'I_` _)
    `lo` is `ho'he` this `ho'yo` from
   `ho__` (\(These x xx) -> x `yo` rewrap ((xx `lu_`) `ho` T'TT'I'TTT'I)))

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

type instance Supertype (e `P` (ee `P` eee)) = e `P` ee `P` eee

instance Elicitable T'II'I (AR) (e `P` (ee `P` eee))
 where elicit = T'II'I (\(These (These x xx) xxx) -> These x (These xx xxx))

instance Elicitable T'I'II (AR) (e `P` (ee `P` eee))
 where elicit = T'I'II (\(These x (These xx xxx)) -> These (These x xx) xxx)

type instance Supertype (e `S` (ee `S` eee)) = e `S` ee `S` eee

instance Elicitable T'II'I (AR) (e `S` (ee `S` eee))
 where elicit = T'II'I (This `la` (That `ha` This) `la_` That `ha` That)

instance Elicitable T'I'II (AR) (e `S` (ee `S` eee))
 where elicit = T'I'II (This `ha` This `la_` This `ha` That `la` That)
