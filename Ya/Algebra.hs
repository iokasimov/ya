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
 mapping = rewrap `identity` \source -> rewrap `identity` \(T'TT'I'TTT'I (These x xx)) ->
  x `yo` wrap @(AR) @(ttt `L` ttt `T` lll `L` t `T` l `T` _)
     `ha` super @(AR) @(ttt `L` ttt `T` lll `L` T'TT'I'TTT'I P t tt `T` l `T` _)
     `yv` wrapped (map @T'I'II @T'I'II @(AR) @(AR) @(t `T'TT'I` ttt `L` ttt `T` lll `L` t `T` l) @(t `TT'T'I` ttt) source)
  `hjd_`
  xx `yo` wrap @(AR) @(ttt `L` ttt `T` lll `L` tt `T` l `T` _)
     `ha` super @(AR) @(ttt `L` ttt `T` lll `L` T'TT'I'TTT'I P t tt `T` l `T` _)
     `yv` wrapped (map @T'I'II @T'I'II @(AR) @(AR) @(tt `T'TT'I` ttt `L` ttt `T` lll `L` tt `T` l) @(tt `TT'T'I` ttt) source)
     `ho` wrap @(AR) @(ttt `L` ttt `T` lll `T` _)
  `yv_` day @T'I'II @(AR) @lll @ttt @ttt @(P) @(P) identity T'TT'I'TTT'I

instance
 ( Covariant Endo Semi Functor (AR) t
 , Covariant Endo Semi Functor (AR) tt
 , Covariant Endo Semi Functor (AR) ttt
 , Covariant Transformation Functor (AR) (AR) (t `T'TT'I` ttt `L` ttt `T` ll `L` t `T` l) (t `TT'T'I` ttt)
 , Covariant Transformation Functor (AR) (AR) (tt `T'TT'I` ttt `L` ttt `T` ll `L` tt `T` l) (tt `TT'T'I` ttt)
 ) => Mapping T'I'II T'I'II (AR) (AR)
  (T'TT'I'TTT'I S t tt `T'TT'I` ttt `L` ttt `T` ll `L` T'TT'I'TTT'I S t tt `T` l)
  (T'TT'I'TTT'I S t tt `TT'T'I` ttt) where
 mapping = rewrap `identity` \source -> rewrap `identity` \(T'TT'I'TTT'I x) -> case x of
  This xx -> xx
   `yo` wrap @(AR) @(ttt `L` ttt `T` ll `L` t `T` l `T` _)
   `ha` super @(AR) @(ttt `L` ttt `T` ll `L` T'TT'I'TTT'I S t tt `T` l `T` _)
   `yv` wrapped (map @T'I'II @T'I'II @(AR) @(AR) @(t `T'TT'I` ttt `L` ttt `T` ll `L` t `T` l) @(t `TT'T'I` ttt) source)
   `yo` T'TT'I'TTT'I `ha` This
  That xx -> xx
   `yo` wrap @(AR) @(ttt `L` ttt `T` ll `L` tt `T` l `T` _)
   `ha` super @(AR) @(ttt `L` ttt `T` ll `L` T'TT'I'TTT'I S t tt `T` l `T` _)
   `yv` wrapped (map @T'I'II @T'I'II @(AR) @(AR) @(tt `T'TT'I` ttt `L` ttt `T` ll `L` tt `T` l) @(tt `TT'T'I` ttt) source)
   `yo` T'TT'I'TTT'I `ha` That

instance
 ( Covariant Lax Monoidal Functor (AR) (AR) (P) P Void (S'I'II Unit)
 ) => Mapping T'I'II T'I'II (AR) (AR)
 (Day T'I'II (AR) (P) (S) (F'T'I'TT'I (T'II'I P) (S'I'II Unit)) (F'T'I'TT'I (T'II'I P) (S'I'II Unit) `L` F'T'I'TT'I (T'II'I P) (S'I'II Unit) `T` Void) i ii)
 (F'T'I'TT'I (T'II'I P) (S'I'II Unit)) where
 mapping = rewrap `identity` \source -> rewrap `identity` \(These (These i ii) (T'I'II f)) ->
  let These xs x = super `compose` super `compose` super `compose` super `identity`i in
  let These ys _ = super `compose` super `compose` super `compose` super `compose` super `identity`ii in
  Recursive `compose` T'TT'I `compose` T'II'I `identity`These
   (day @T'I'II @(AR) @Void @(S'I'II Unit) @(S'I'II Unit) @(P) @P identity
    (super `compose` day @T'I'II @(AR) @Void @(F'T'I'TT'I (T'II'I P) _) @(F'T'I'TT'I (T'II'I P) _) @(P) @(S) identity (source `compose` f)
     `compose` fio (wrap `compose` F'T'I'TT'I) `compose` foi F'T'I'TT'I)
    `identity`These xs (wrap ys))
   (source `compose` f `identity`This x)

instance
 ( Covariant Lax Monoidal Functor (AR) (AR) (P) P Void (S'I'II Unit)
 -- , Covariant Endo Monoidal Functor (AR) (P) (S) Void (F'T'I'TT'I (T'II'I P) (S'I'II Unit))
 ) => Mapping T'I'II T'I'II (AR) (AR) (Day T'I'II (AR) (P) (S)
  (S'I'II Unit `T'TT'I` F'T'I'TT'I (T'II'I P) (S'I'II Unit))
  ((S'I'II Unit `T'TT'I` F'T'I'TT'I (T'II'I P) (S'I'II Unit)) `L` (S'I'II Unit `T'TT'I` F'T'I'TT'I (T'II'I P) (S'I'II Unit)) `T` Void)
 i ii)
 (S'I'II Unit `T'TT'I` F'T'I'TT'I (T'II'I P) (S'I'II Unit)) where
 mapping = rewrap `identity` \source -> rewrap `identity` \(These (These i (Label ii)) (T'I'II f)) ->
  (day @T'I'II @(AR) @Void @(S'I'II Unit) @(S'I'II Unit) @(P) @P identity
     (day @T'I'II @(AR) @Void @(F'T'I'TT'I (T'II'I P) _) @(F'T'I'TT'I (T'II'I P) _) @(P) @(S) identity (source `compose` f)
  `compose` fio @(AR) wrap)
     `hc__` super i `hjd` wrap (super ii))

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
 mapping = rewrap `identity` \source -> rewrap `identity` \x -> super x
  `yo'yo` rewrap @(AR) @_ @(tt `L` tt `T` ll `L` F'T'I'TT'I (T'II'I P) t `T` l `T` _) identity
  `yo` wrapped (map @T'I'II @T'I'II @(AR) @(AR)
   @(F'T'I'TT'I (T'II'I P) t `T'TT'I` tt `L` tt `T` ll `L` F'T'I'TT'I (T'II'I P) t `T` l)
   @(F'T'I'TT'I (T'II'I P) t `TT'T'I` tt) source)
  `ho` wrap @(AR) @(tt `L` tt `T` ll `T` _)
  `ho` wrap @(AR) @(tt `L` tt `T` ll `L` t `T` l `T` _)
  `yv` wrapped (map @T'I'II @T'I'II @(AR) @(AR) @(t `T'TT'I` tt `L` tt `T` ll `L` t `T` l) @(t `TT'T'I` tt) identity)
  `yo` wrap @(AR) @(t `T'TT'I` F'T'I'TT'I (T'II'I P) t `T'I_` _)

-- State (hc_st item) `L` State (hc_st item) `T` Void) `L` hc_st `T` (Void `P` Void)

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
 mapping = rewrap `identity` \source -> rewrap `identity` \(F'T'I'TT'I (Recursive (T'TT'I (T'II'I (These xs x))))) ->
    (xs
      `yo` wrap @(AR) @(F'T'I'TT'I _ _ _)
      `ho` wrapped (map @T'I'II @T'I'II @(AR) @(AR)
        @(F'T'I'TT'I (T'II'I P) t `T'TT'I` tt `L` tt `T` ll `L` F'T'I'TT'I (T'II'I P) t `T` (Void `P` Void))
        @(F'T'I'TT'I (T'II'I P) t `TT'T'I` tt) source)
      `ho` wrap @(AR) @(tt `L` tt `T` ll `T` _)
      `ho` wrap @(AR) @(tt `L` tt `T` ll `L` t `T` (Void) `T` _)
      `yv` wrapped (map @T'I'II @T'I'II @(AR) @(AR) @(t `T'TT'I` tt `L` tt `T` ll `L` t `T` (Void)) @(t `TT'T'I` tt) (super @(AR) @(F'T'I'TT'I _ _ _)))
     `hjd_` super (super x) `yo` source `yv` wrap @(AR) @(_ `L` _ `T` Void `T` _))
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
 mapping = rewrap `identity` \source -> rewrap
  `identity` \(F'T'I'TT'I (Recursive (T'TT'I (T'II'I (These xs x))))) ->
   (These
    `ho_'ho` (wrap @(AR) @(T'TT'I _ _ _) `compose` wrap @(AR) @(T'II'I _ _ _))
    `ho` wrap @(AR) @(Recursive _)
    `ho` wrap @(AR) @(F'T'I'TT'I _ _ _))
   `fo` (xs
      `yo` wrap @(AR) @(F'T'I'TT'I _ _ _)
      `ho` wrapped (map @T'I'II @T'I'II @(AR) @(AR)
       @(F'T'I'TT'I (T'II'I P) t `T'TT'I` tt `L` tt `T` ll `L` F'T'I'TT'I (T'II'I P) t `T` (Void))
       @(F'T'I'TT'I (T'II'I P) t `TT'T'I` tt) source)
      `ho` wrap @(AR) @(tt `L` tt `T` ll `T` _)
      `ho` wrap @(AR) @(tt `L` tt `T` ll `L` t `T` Void `T` _)
      `yv` wrapped (map @T'I'II @T'I'II @(AR) @(AR) @(t `T'TT'I` tt `L` tt `T` ll `L` t `T` Void) @(t `TT'T'I` tt) (super @(AR) @(F'T'I'TT'I _ _ _)))
    )
    `fc` (super (super x) `yo` source)

instance
 ( Covariant Endo Semi Functor (AR) t
 , Covariant Endo Semi Functor (AR) tt
 , Covariant Transformation Functor (AR) (AR) (t `T'TT'I` tt `L` tt `T` ll `L` t `T` Void) (t `TT'T'I` tt)
 ) => Mapping T'I'II T'I'II (AR) (AR)
  (F'T'I'TT'I (T'I'II S) t `T'TT'I` tt `L` tt `T` ll `L` F'T'I'TT'I (T'I'II S) t `T` Void)
  (F'T'I'TT'I (T'I'II S) t `TT'T'I` tt) where
 mapping = rewrap `identity` \source -> rewrap `identity` \(F'T'I'TT'I (Recursive (T'TT'I (T'I'II x)))) -> case x of
  This xx -> super (super xx) `yo` F'T'I'TT'I `ha` Recursive `ha` T'TT'I `ha` T'I'II `ha` This `ha` source
  That xx -> xx
   `yo` F'T'I'TT'I
   `ho` wrapped (map @T'I'II @T'I'II @(AR) @(AR)
    @(F'T'I'TT'I (T'I'II S) t `T'TT'I` tt `L` tt `T` ll `L` F'T'I'TT'I (T'I'II S) t `T` Void)
    @(F'T'I'TT'I (T'I'II S) t `TT'T'I` tt) source)
   `ho` wrap @(AR) @(tt `L` tt `T` ll `T` _)
   `ho` wrap @(AR) @(tt `L` tt `T` ll `L` t `T` Void `T` _)
   `yv` wrapped (map @T'I'II @T'I'II @(AR) @(AR)
     @(t `T'TT'I` tt `L` tt `T` ll `L` t `T` Void)
     @(t `TT'T'I` tt)
     (super @(AR) @(F'T'I'TT'I _ _ _)))
   `yo` F'T'I'TT'I `ha` Recursive `ha` T'TT'I `ha` T'I'II `ha` That

-- TODO: try to simphc_fy
instance
 ( Covariant Lax Monoidal Functor (AR) (AR) (P) P Void t
 , Covariant Lax Monoidal Functor (AR) (AR) (P) P Void (F'T'I'TT'I (T'II'I P) t)
 ) => Mapping T'I'II T'I'II (AR) (AR) (Day T'I'II (AR) (P) P (F'T'I'TT'I (T'II'I P) t) (F'T'I'TT'I (T'II'I P) t `L` F'T'I'TT'I (T'II'I P) t `T` Void) e ee) (F'T'I'TT'I (T'II'I P) t) where
 mapping = rewrap `identity` \source -> rewrap `identity` \case
  These (These e ee) (T'I'II f) ->
   let These e__ e_ = super `compose` super `compose` super `compose` super `identity`e in
   let These ee__ ee_ = super `compose` super `compose` super `compose` super `compose` super `identity`ee in
   Recursive `compose` T'TT'I `compose` T'II'I `identity`These
    (day @T'I'II @(AR) @Void @t @t @(P) @P identity
     (super
      `compose` day @T'I'II @(AR) @Void @(F'T'I'TT'I (T'II'I P) t) @(F'T'I'TT'I (T'II'I P) t) @(P) @P identity (source `compose` f)
      `compose` fio (wrap `compose` F'T'I'TT'I)
      `compose` foi F'T'I'TT'I)
     `identity`These e__ (wrap ee__))
    (source `compose` f `identity`These e_ ee_)

instance (Initial (AR), Covariant Lax Monoidal Functor (AR) (AR) (P) (S) Void t) =>
 Mapping T'I'II T'I'II (AR) (AR) (T'I'II (AR) Unit) (F'T'I'TT'I (T'II'I P) t) where
 mapping = rewrap `identity` \source (T'I'II f) ->
  F'T'I'TT'I `compose` Recursive `compose` T'TT'I `compose` T'II'I
   `identity`These (empty @t `yo` initial @(AR)) (source `identity`f Unit)

instance
 ( Covariant Lax Monoidal Functor (AR) (AR) (P) P Void t
 , Covariant Lax Monoidal Functor (AR) (AR) (P) P Void (F'T'I'TT'I (T'II'I P) t)
 ) => Mapping T'I'II T'I'II (AR) (AR) (Day T'I'II (AR) (P) P (t `T'TT'I` F'T'I'TT'I (T'II'I P) t) ((t `T'TT'I` F'T'I'TT'I (T'II'I P) t) `L` (t `T'TT'I` F'T'I'TT'I (T'II'I P) t) `T` Void) e ee) (t `T'TT'I` F'T'I'TT'I (T'II'I P) t) where
 mapping = rewrap `identity` \source -> rewrap `identity` \case
  These (These (T'TT'I e) (Label (T'TT'I ee))) (T'I'II f) ->
    day @T'I'II @(AR) @Void @t @t @(P) @P identity
     (day @T'I'II @(AR) @Void @(F'T'I'TT'I (T'II'I P) t) @(F'T'I'TT'I (T'II'I P) t) @(P) @P identity (source `compose` f) `compose` fio @(AR) wrap)
      (These e (wrap ee))

instance
 ( Covariant Lax Monoidal Functor (AR) (AR) (P) P Void t
 , Covariant Lax Monoidal Functor (AR) (AR) (P) P Void (F'T'I'TT'I (T'II'I P) tt)
 ) => Mapping T'I'II T'I'II (AR) (AR) (T'I'II (AR) Unit) (t `T'TT'I` F'T'I'TT'I (T'II'I P) tt) where
 mapping = rewrap `identity` \source (T'I'II f) -> T'TT'I `hc_`
  intro @t @(AR) `compose` intro @(F'T'I'TT'I (T'II'I P) tt) @(AR) `compose` source `compose` f `identity`Unit

-- TODO: try to avoid mapping a datastructure twice here
instance
 ( Covariant Endo Semi Functor (AR) t
 , Covariant Lax Monoidal Functor (AR) (AR) (P) (W) Void t
 ) => Mapping T'I'II T'I'II (AR) (AR) (Day T'I'II (AR) (P) (W) (t `T'TT'I` F'T'I'TT'I (T'II'I P) t) ((t `T'TT'I` F'T'I'TT'I (T'II'I P) t) `L` (t `T'TT'I` F'T'I'TT'I (T'II'I P) t) `T` Void) e ee) (t `T'TT'I` F'T'I'TT'I (T'II'I P) t) where
 mapping = rewrap `identity` \source -> rewrap `identity` \case
  These (These (T'TT'I e) (Label (T'TT'I ee))) (T'I'II f) ->
    (day @T'I'II @(AR) @Void @t @t @(P) @(W) identity
     (\case
      U_T'I'II_UT'I'II (This (This x)) -> x `yo` source `compose` f `compose` U_T'I'II_UT'I'II `compose` This `compose` This
      U_T'I'II_UT'I'II (This (That x)) -> x `yo` source `compose` f `compose` U_T'I'II_UT'I'II `compose` This `compose` That
      U_T'I'II_UT'I'II (That x) -> day @T'I'II @(AR) @Void @(F'T'I'TT'I (T'II'I P) t) @(F'T'I'TT'I (T'II'I P) t) @(P) @(W) identity (source `compose` f) (fio @(AR) wrap x)
     )
      (These e (wrap @(AR) ee))
    )

-- TODO: try to avoid mapping twice datastructure here
instance
 ( Covariant Endo Semi Functor (AR) t
 , Covariant Lax Monoidal Functor (AR) (AR) (P) (W) Void t
  -- TODO: I hope it doesn't produce cycles
 -- , Covariant Monoidal Functor (AR) (AR) (P) (W) Void (F'T'I'TT'I (T'II'I P) t)
 ) => Mapping T'I'II T'I'II (AR) (AR) (Day T'I'II (AR) (P) (W) (F'T'I'TT'I (T'II'I P) t) (F'T'I'TT'I (T'II'I P) t `L` F'T'I'TT'I (T'II'I P) t `T` Void) e ee) (F'T'I'TT'I (T'II'I P) t) where
 mapping = rewrap `identity` \source -> rewrap `identity` \case
  These (These e ee) (T'I'II f) ->
   let These e__ e_ = super `compose` super `compose` super `compose` super `identity`e in
   let These ee__ ee_ = super `compose` super `compose` super `compose` super `compose` super `identity`ee in
   Recursive `compose` T'TT'I `compose` T'II'I `identity`These
    (day @T'I'II @(AR) @Void @t @t @(P) @(W) identity
     (super @(AR) `compose` \case
      U_T'I'II_UT'I'II (This (This x)) -> F'T'I'TT'I x `yo` source `compose` f `compose` U_T'I'II_UT'I'II `compose` This `compose` This
      U_T'I'II_UT'I'II (This (That x)) -> F'T'I'TT'I x `yo` source `compose` f `compose` U_T'I'II_UT'I'II `compose` This `compose` That
      U_T'I'II_UT'I'II (That (These x xx)) -> day @T'I'II @(AR) @Void @(F'T'I'TT'I (T'II'I P) t) @(F'T'I'TT'I (T'II'I P) t) @(P) @(W) identity (source `compose` f) (F'T'I'TT'I x `hjd` wrap (F'T'I'TT'I xx))
     )
     `identity`These e__ (wrap ee__))
    (source `compose` f `compose` U_T'I'II_UT'I'II `compose` That `identity`These e_ ee_)

instance (Initial (AR), Covariant Lax Monoidal Functor (AR) (AR) (P) (S) Void t) =>
 Mapping T'I'II T'I'II (AR) (AR) (T'I'II (AR) Void) (t `T'TT'I` F'T'I'TT'I (T'II'I P) tt) where
 mapping = rewrap `identity` \_ _ -> T'TT'I (empty @t `yo` initial @(AR))

instance Mapping T'I'II T'I'II (AT) (AT) (P'I'II e) (P'I'II e) where
 mapping = rewrap `compose` rewrap `identity` \source (T'I'II (These e x)) ->
   let s = source x in T'I'II (These e (this s)) `hjd` fo (that s)

instance Mapping T'I'II T'I'II (AT) (AT) (T'II'I (P) e) (T'II'I (P) e) where
 mapping = rewrap `compose` rewrap `identity` \source (T'II'I (These x e)) ->
   let s = source x in T'II'I (These (this s) e) `hjd` fo (that s)

-- TODO: I'm not really sure about this instance... it could easily lead to an error!
instance Mapping T'I'II T'I'II (AT) (AT) I (T'I'I (P)) where
 mapping = rewrap `compose` rewrap `identity` \source (Identity x) ->
   let s = source x in T'I'I (this s `hjd`this s) `hjd` (\(T'I'I (These _ _)) -> Identity (that s (this s)))

instance Mapping T'I'II T'I'II (AT) (AT) (P'I'II e) I where
 mapping = rewrap `compose` rewrap `identity` \source (T'I'II (These e x)) ->
   let s = source x in Identity (this s) `hjd` (T'I'II `compose` (e `hjd`) `compose` that s `compose` super)

instance Mapping T'I'II T'I'II (AT) (AT) (T'II'I (P) e) I where
 mapping = rewrap `compose` rewrap `identity` \source (T'II'I (These x e)) ->
   let s = source x in Identity (this s) `hjd` (T'II'I `compose` (`hjd` e) `compose` that s `compose` super)

-- TODO: I should alse test how attributes behave on sums

-- This instance for normal state propagation. How unnormal should look hc_ke?
instance (e ~ ee) =>
 Mapping T'I'II T'I'II (AR) (AR)
 (T'I'II (T'I'TT'II'I (AR) (P)) e `T'TT'I` T'I'II (T'I'TT'II'I (AR) (P)) ee `L` T'I'II (T'I'TT'II'I (AR) (P)) ee `T` Void)
 (T'I'II (T'I'TT'II'I (AR) (P)) e) where
 mapping = rewrap `identity` \source -> rewrap `compose` rewrap `identity` \(T'I'TT'II'I state) old ->
    let These trn btw = state old in
    let These res new = super (super (super trn)) btw in
        These (source res) new

-- T'I'II (T'I'TT'II'I (AR) (P))

instance (e ~ ee) => Mapping T'I'II T'I'II (AR) (AR)
 (T'I'II (T'I'TT'II'I (AR) (P)) e `T'TT'I` T'I'II (T'I'TT'II'I (AR) (P)) ee `L` T'I'II (T'I'TT'II'I (AR) (P)) ee `T` (Void `P` Void))
 (T'I'II (T'I'TT'II'I (AR) (P)) e) where
 mapping = rewrap `identity` \source -> rewrap `compose` rewrap `identity` \(T'I'TT'II'I state) old ->
    let These trn btw = state old in
    let These res _ = super (super (super trn)) btw in
        These (source res) old

instance (Covariant Lax Monoidal Functor (AR) (AR) (P) (P) Void t, e ~ ee)
 => Mapping T'I'II T'I'II (AR) (AR)
  (T'I'II (T'I'TT'II'I (AR) (P)) ee)
  (T'TTT'TT'I (T'I'II (AR) e) (T'II'I (P) e) t) where
 mapping = rewrap `identity` \source (T'I'II (T'I'TT'II'I x)) ->
  wrap @_ @(T'TTT'TT'I _ _ _ _) `compose` wrap @_ @(T'I'II _ _ _)
  `identity`(intro `compose` map @T'I'II @T'I'II source `compose` wrap @_ @(T'II'I _ _ _) `compose` x)

instance {-# OVERLAPPABLE #-} Covariant Transformation Functor (AR) (AR) (t `T'TT'I` tt `L` tt `T` ll) t => Mapping T'I'II T'I'II (AR) (AR)
 (T'I'II (AR) e `T'TT'I` t `T'TT'I_` tt `L` tt `T` ll) (T'I'II (AR) e `T'TT'I` t) where
 mapping = rewrap `identity` \source -> rewrap `compose` rewrap `identity`
  \(T'I'II f) e -> map @T'I'II @T'I'II @(AR) @(AR) @(t `T'TT'I` tt `L` tt `T` ll) @t source (T'TT'I (f e))

instance {-# OVERLAPS #-}
 Covariant Endo Semi Functor (AR) t
 => Mapping T'I'II T'I'II (AR) (AR) (T'I'II (AR) e `T'TT'I` t `T'TT'I_` T'I'II (AR) e `L` T'I'II (AR) e `T` Void) (T'I'II (AR) e `T'TT'I` t) where
 mapping = rewrap `identity` \source -> rewrap `compose` rewrap `identity`
  \(T'I'II f) e -> f e `yo` super @(AR) `ho` super @(AR) `ho` (`hc_` e) `ho` source

instance {-# OVERLAPPABLE #-}
 Covariant Transformation Functor (AR) (AR) (t `T'TT'I` t `L` t `T` Void) t
 => Mapping T'I'II T'I'II (AR) (AR) (T'I'II (AR) e `T'TT'I` t `T'TT'I_` (T'I'II (AR) e `T'TT'I` t) `L` (T'I'II (AR) e `T'TT'I` t) `T` Void) (T'I'II (AR) e `T'TT'I` t) where
 mapping = rewrap `identity` \source -> rewrap `compose` rewrap `identity`
  \(T'I'II f) e ->
   map @T'I'II @T'I'II @AR @AR @(t `T'TT'I` t `L` t `T` Void) @t source `compose` wrap
   `compose` map @T'I'II @T'I'II @AR @AR @t @t (wrap @AR @(t `L` t `T` Void `T` _) `compose` yv e `compose` super `compose` super `compose` super)
   `identity`f e

-- NOTE: this version allow different type of states, but it requires providing types to make it compile
-- 1. T'I'II (AR) old (t (T'II'I (P) btw))

instance
 ( Covariant Endo Semi Functor (AR) t
 , Covariant Transformation Functor (AR) (AR) (t `T'TT'I` t `L` t `T` Void) t
 ) => Mapping T'I'II T'I'II (AR) (AR)
 (T'TTT'TT'I (T'I'II (AR) old) (T'II'I (P) btw) t `T'TT'I` (T'TTT'TT'I (T'I'II (AR) btw) (T'II'I (P) new) t `L` T'TTT'TT'I (T'I'II (AR) btw) (T'II'I (P) new) t `T` Void))
 (T'TTT'TT'I (T'I'II (AR) old) (T'II'I (P) new) t) where
 mapping = rewrap `identity` \source -> rewrap `compose` rewrap `identity`
  \(T'I'II x) -> component @(AR) @(t `T'TT'I` t `L` t `T` Void) @t
  `compose` wrap @(AR) @(t `T'TT'I` t `L` t `T` Void `T'I_` _)
  `compose` map @T'I'II @T'I'II @(AR) @(AR) @t @t
   (wrap @(AR) @(t `L` t `T` Void `T` _)
    `compose` fd @(AR) @(AR) (super @(AR) @(T'TTT'TT'I (T'I'II (AR) btw) (T'II'I (P) new) t _)
    `compose` fo source
    `compose` super @(AR) @(_ `L` _ `T` Void `T` _)))
  `compose` x

-- TODO: try to use adjunctions here
instance
 ( Covariant Lax Monoidal Functor (AR) (AR) (P) P Void tt
 , Covariant Transformation Functor (AR) (AR) (tt `T'TT'I` tt `L` tt `T` Void) tt
 , e ~ ee
 ) => Mapping T'I'II T'I'II (AR) (AR)
 (T'TTT'TT'I (T'I'II (AR) e) (T'II'I (P) e) tt `T'TT'I` T'I'II (T'I'TT'II'I (AR) (P)) ee `L` T'I'II (T'I'TT'II'I (AR) (P)) ee `T` Void)
 (T'TTT'TT'I (T'I'II (AR) e) (T'II'I (P) e) tt) where
  mapping = rewrap `identity` \source -> rewrap `compose` rewrap `identity` \(T'I'II x) ->
    \old -> x old `yok` \(T'II'I (These (Label @_ @_ @Void (T'I'II (T'I'TT'II'I f))) btw))
      -> (Label @_ @_ @Void `compose` intro @tt) `identity`(T'II'I (f btw) `yo` source)

instance
 ( Covariant Lax Monoidal Functor (AR) (AR) (P) P Void tt
 , Covariant Transformation Functor (AR) (AR) (tt `T'TT'I` tt `L` tt `T` Void) tt
 , e ~ ee
 ) => Mapping T'I'II T'I'II (AR) (AR)
 (T'TTT'TT'I (T'I'II (AR) e) (T'II'I (P) e) tt `T'TT'I`
  T'I'II (T'I'TT'II'I (AR) (P)) ee `L` T'I'II (T'I'TT'II'I (AR) (P)) ee `T` (Void `P` Void)
 )
 (T'TTT'TT'I (T'I'II (AR) e) (T'II'I (P) e) tt) where
  mapping = rewrap `identity` \source -> rewrap `compose` rewrap `identity` \(T'I'II x) ->
    \old -> x old `yok` \(T'II'I (These (Label @_ @_ @(Void `P` Void) (T'I'II (T'I'TT'II'I f))) btw))
      -> (Label @_ @_ @Void `compose` intro @tt @(AR)) `identity`(T'II'I (f btw `yiu` old) `yo` source)

instance
 ( Covariant Functor target target tt
 , Covariant Functor target target ttt
 , Covariant Endo Semi Functor target t
 , Covariant Endo Transformation Functor target (tt `T'TT'I` tt `L` tt `T` l) tt
 , Covariant Endo Transformation Functor target (ttt `T'TT'I` tt `L` tt `T` l `L` ttt `T` l) (ttt `TT'T'I` tt)
 , forall e . Wrapper target (ttt `T'TT'I` tt `L` tt `T` l `T'I_` e)
 , forall e . Wrapper target (tt `L` tt `T` l `T` e)
 , forall e . Wrapper target (T'TTT'TT'I t ttt tt e)
 , forall e . Wrapper target (ttt `T'TT'I` tt `T'I_` e)
 , forall e . Wrapper target (ttt `TT'T'I` tt `T'I_` e)
 , forall e . Wrapper target (tt `T'TT'I` tt `L` tt `T` l `T'I_` e)
 , forall e . Wrapper target (ttt `T'TT'I` tt `L` tt `T` l `L` ttt `T` l `T'I_` e)
 , forall e . Wrapper target (tt `L` tt `T` l `L` ttt `T` l `T` e)
 , forall e . Wrapper target (T'TTT'TT'I t ttt tt `T'TT'I` tt `L` tt `T` l `T'I_` e)
 ) => Mapping T'I'II T'I'II target target (T'TTT'TT'I t ttt tt `T'TT'I` tt `L` tt `T` l) (T'TTT'TT'I t ttt tt) where
 mapping = rewrap `identity` \source -> rewrap `identity`
  map @T'I'II @T'I'II @target @target @t
   (component @target @(tt `T'TT'I` tt `L` tt `T` l) @tt `compose` wrap @target
    `compose` map @T'I'II @T'I'II @target @target @tt
     (wrap @target @(tt `L` tt `T` l `T` _)
      `compose` wrapped (map @T'I'II @T'I'II @target @target @(ttt `T'TT'I` tt `L` tt `T` l `L` ttt `T` l) @(ttt `TT'T'I` tt) source)
      `compose` map @T'I'II @T'I'II @target @target @ttt (wrap)
     )
    )
  `compose` super @target

-- TODO: rename type variables
-- 1. t (tt't (tt'tt (ttt (L l tt't _))))
-- 2. t (tt't (tt'tt (tt't (ttt _))))
-- 3. t (tt't (tt't (tt'tt (ttt _))))
-- 4. t (tt't (tt'tt (ttt _)))
instance
 ( Covariant Functor target target tt'tt
 , Covariant Endo Semi Functor target t
 , Covariant Endo Semi Functor target tt't
 , Covariant Endo Semi Functor target ttt
 , Covariant Endo Transformation Functor target (tt't `T'TT'I` tt't `L` tt't `T` l) tt't
 , Covariant Endo  Transformation Functor target (ttt `T'TT'I` tt't `L` tt't `T` l `L` ttt `T` l) (ttt `TT'T'I` tt't)
 , Covariant Endo Transformation Functor target (tt'tt `T'TT'I` tt't `L` tt't `T` l `L` tt'tt `T` Void) (tt'tt `TT'T'I` tt't)
 , forall ee . Wrapper target (tt't `L` tt't `T` l `T` ee)
 , forall ee . Wrapper target (ttt `T'TT'I` tt't `L` tt't `T` l `T'I_` ee)
 , forall ee . Wrapper target (ttt `TT'T'I` tt't `T'I_` ee)
 , forall ee . Wrapper target (tt'tt `T'TT'I` tt't `L` tt't `T` l `T'I_` ee)
 , forall ee . Wrapper target (tt'tt `TT'T'I` tt't `T'I_` ee)
 , forall ee . Wrapper target (tt't `T'TT'I` tt't `L` tt't `T` l `T'I_` ee)
 , forall ee . Wrapper target (tt't `L` tt't `T` l `L` tt'tt `T` Void `T'I_` ee)
 , forall ee . Wrapper target (ttt `T'TT'I` tt't `L` tt't `T` l `L` ttt `T` l `T'I_` ee)
 , forall ee . Wrapper target (tt't `L` tt't `T` l `L` ttt `T` l `T'I_` ee)
 , forall ee . Wrapper target (tt'tt `T'TT'I` tt't `L` tt't `T` l `L` tt'tt `T` Void `T'I_` ee)
 , forall ee . Wrapper target (T'TTT'TT'I t ttt (tt'tt `TT'T'I` tt't) `T'TT'I` tt't `L` tt't `T` l `T'I_` ee)
 , forall ee . Wrapper target (T'TTT'TT'I t ttt (tt'tt `TT'T'I` tt't) ee)
 ) => Mapping T'I'II T'I'II target target
  (T'TTT'TT'I t ttt (tt'tt `TT'T'I` tt't) `T'TT'I` tt't `L` tt't `T` l)
  (T'TTT'TT'I t ttt (tt'tt `TT'T'I` tt't)) where
 mapping = rewrap `identity` \source -> rewrap `identity`
  map @T'I'II @T'I'II @target @target @t @t
   (wrap @target @(TT'T'I _ _ _)
    `compose` component @target @(tt't `T'TT'I` tt't `L` tt't `T` l) @tt't
    `compose` wrap @target @(tt't `T'TT'I` tt't `L` tt't `T` l `T'I_` _)
    `compose` map @T'I'II @T'I'II @target @target @tt't @tt't (wrap @target @(tt't `L` tt't `T` l `T` _))
    `compose` map @T'I'II @T'I'II @target @target @tt't
     (wrapped (component @target @(tt'tt `T'TT'I` tt't `L` tt't `T` l `L` tt'tt `T` Void) @(tt'tt `TT'T'I` tt't))
     `compose` map @T'I'II @T'I'II @target @target @(tt'tt) @(tt'tt)
      (wrap @target `compose` wrap @target @(tt't `L` tt't `T` l `T` _))
    )
    `compose` super @target @(TT'T'I tt'tt tt't _)
    `compose` map @T'I'II @T'I'II @target @target @(TT'T'I tt'tt tt't) @(TT'T'I tt'tt tt't)
     (wrapped (map @T'I'II @T'I'II @target @target @(ttt `T'TT'I` tt't `L` tt't `T` l `L` ttt `T` l) @(ttt `TT'T'I` tt't) source)
     `compose` map @T'I'II @T'I'II @target @target @ttt @ttt wrap)
   )
  `compose` super @target

-- TODO: introduce a label
-- 1. t (ttt'tt (ttt't (tt (ttt't _))))
-- 2. t (ttt'tt (ttt't (ttt't (tt _))))
-- 4. t (ttt'tt (ttt't (tt _)))
instance
 ( Covariant Functor target target ttt't
 , Covariant Endo Semi Functor target t
 , Covariant Endo Semi Functor target tt
 , Covariant Endo Semi Functor target ttt'tt
 , Covariant Endo Transformation Functor target (ttt't `T'TT'I` ttt't `L` ttt't `T` l) ttt't
 , Covariant Endo Transformation Functor target (tt `T'TT'I` ttt't `L` ttt't `T` l `L` tt `T` l) (tt `TT'T'I` ttt't)
 , forall e . Wrapper target ((ttt't `T'TT'I` ttt't `L` ttt't `T` l) e)
 , forall e . Wrapper target ((tt `T'TT'I` ttt't `L` ttt't `T` l `L` tt `T` l) e)
 , forall e . Wrapper target (ttt't `L` ttt't `T` l `T` e)
 , forall e . Wrapper target (ttt't `L` ttt't `T` l `L` tt `T` l `T` e)
 , forall e . Wrapper target (T'TT'I ttt't ttt't e)
 , forall e . Wrapper target (T'TT'I ttt't ttt'tt e)
 , forall e . Wrapper target (T'TT'I (T'TTT'TT'I t tt (TT'T'I ttt't ttt'tt)) (ttt't `L` ttt't `T` l) e)
 , forall e . Wrapper target (TT'T'I tt ttt't e)
 , forall e . Wrapper target (TT'T'I ttt't ttt'tt e)
 , forall e . Wrapper target (T'TTT'TT'I t tt (TT'T'I ttt't ttt'tt) e)
 ) => Mapping T'I'II T'I'II target target
  (T'TTT'TT'I t tt (ttt't `TT'T'I` ttt'tt) `T'TT'I` ttt't `L` ttt't `T` l)
  (T'TTT'TT'I t tt (ttt't `TT'T'I` ttt'tt)) where
 mapping = rewrap `identity` \source -> rewrap `identity`
  map @T'I'II @T'I'II @target @target @t @t
   (wrap @target @(TT'T'I _ _ _)
    `compose` map @T'I'II @T'I'II @target @target @ttt'tt
     (component @target @(ttt't `T'TT'I` ttt't `L` ttt't `T` l) @ttt't
     `compose` wrap @target @(T'TT'I _ _ _)
     `compose` map @T'I'II @T'I'II @target @target @ttt't (wrap @target @(ttt't `L` ttt't `T` l `T` _))
     )
    `compose` super @target @(TT'T'I ttt't ttt'tt _)
    `compose` map @T'I'II @T'I'II @target @target @(ttt't `TT'T'I` ttt'tt) @(ttt't `TT'T'I` ttt'tt)
     (wrapped (map @T'I'II @T'I'II @target @target @(tt `T'TT'I` ttt't `L` ttt't `T` l `L` tt `T` l) @(tt `TT'T'I` ttt't) source) `compose` map @T'I'II @T'I'II @target @target @tt @tt wrap)
   )
  `compose` super @target

instance
 ( Covariant Lax Monoidal Functor (AR) (AR) (P) P Void t
 , Covariant Endo Semi Functor (AR) tt
 ) => Mapping T'I'II T'I'II (AR) (AR) tt (tt `TT'T'I` t) where
 mapping = rewrap `identity` \source -> wrap @(AR) @((tt `TT'T'I` t) _)
  `compose` component @(AR) @(T'I'II (AR) Unit) @t
  `compose` component @(AR) @I @(T'I'II (AR) Unit)
  `compose` wrap @(AR)
  `compose` map @T'I'II @T'I'II @(AR) @(AR) @tt @tt source

-- instance Mapping T'I'II T'I'II (AR) (AR) (T'II'I (P) e `T'TT'I` L (S'I'II () ()) tt) (T'II'I (P) e `TT'T'I` tt) =>
 -- Mapping T'I'II T'I'II (AR) (AR)
  -- (T'I'II (T'I'TT'II'I (AR) (P)) e `T'TT'I` tt)
  -- (T'TTT'TT'I (T'I'II (AR) e) (T'II'I (P) e) tt) where
 -- mapping = rewrap `identity` \source (T'TT'I (T'I'II (T'I'TT'II'I x))) ->
  -- T'TTT'TT'I `compose` T'I'II `identity` \old -> wrapped @(AR)
   -- `hc_` map @T'I'II @T'I'II @(AR) @(AR) @(T'II'I (P) e `T'TT'I` L (S'I'II () ()) tt) @(T'II'I (P) e `TT'T'I` tt) source
   -- `hc_` T'II'I (x old)

instance Covariant Lax Monoidal Functor (AR) (AR) (P) P Void t =>
 Mapping T'I'II T'I'II (AR) (AR) (T'I'II (AR) Unit) (T'I'II (AR) e `T'TT'I` t) where
 mapping = rewrap `identity` \source -> rewrap `identity` \f -> T'I'II `identity` \_ -> intro `compose` source `hc_` f Unit

-- instance
--  ( Covariant Yoneda Functor target target I
--  , Covariant Endo Semi Functor target (T'I'II target i)
--  , Adjoint Functor target target (T'II'I t i) (T'I'II tt i)
--  , forall e . Wrapper target (T'II'I t i e)
--  , forall e . Wrapper target (T'I'II target Unit e)
--  , forall e . Wrapper target (T'I'II tt i e)
--  , forall e . Wrapper target (T'I'TT'II'I tt t i e)
--  , forall e . Wrapper target (T'I'II (T'I'TT'II'I tt t) i e)
--  , forall e . Wrapper target (T'TT'I (T'I'II tt i) (T'II'I t i) e)
--  , forall e . Wrapper target (T'TT'I (T'II'I t i) (T'I'II tt i) e)
--  , forall e . Wrapper target (I e)
--  ) => Mapping T'I'II T'I'II target target (T'I'II target Unit) (T'I'II (T'I'TT'II'I tt t) i) where
--  mapping = rewrap `identity` \source -> rewrap
--   `hc_` wrap @target @(T'I'TT'II'I _ _ _ _)
--    `compose` fij @target @target identity
--    `compose` source
--    `compose` yv Unit

instance
 ( Covariant Yoneda Functor (AR) (AR) I
 , Covariant Endo Semi Functor (AR) (T'I'II (AR) i)
 , Adjoint Functor (AR) (AR) (T'II'I t i) (T'I'II tt i)
 , forall e . Wrapper (AR) (T'II'I t i e)
 , forall e . Wrapper (AR) (T'I'II (AR) Unit e)
 , forall e . Wrapper (AR) (T'I'II tt i e)
 , forall e . Wrapper (AR) (T'I'TT'II'I tt t i e)
 , forall e . Wrapper (AR) (T'I'II (T'I'TT'II'I tt t) i e)
 , forall e . Wrapper (AR) (T'TT'I (T'I'II tt i) (T'II'I t i) e)
 , forall e . Wrapper (AR) (T'TT'I (T'II'I t i) (T'I'II tt i) e)
 , forall e . Wrapper (AR) (I e)
 ) => Mapping T'I'II T'I'II (AR) (AR) (T'I'II (AR) Unit) (T'I'II (T'I'TT'II'I tt t) i) where
 mapping = rewrap `identity` \source -> rewrap
  `hc_` wrap @(AR) @(T'I'TT'II'I _ _ _ _)
   `compose` fij @(AR) @(AR) identity
   `compose` source
   `compose` yv Unit

-- instance
--  ( Covariant Yoneda Functor target target I
--  -- , Covariant Endo Monoidal Functor target tt tt t
--  , Covariant Endo Semi Functor target t
--  , Adjoint Functor target target (T'II'I tt e) (T'I'II ttt e)
--  , Component target I (T'I'II target Unit)
--  , Component target (T'I'II target Unit) t
--  , forall ee . Wrapper target (I ee)
--  , forall ee . Wrapper target (T'I'II target Unit ee)
--  , forall ee . Wrapper target (T'TT'I (T'I'II ttt e) (T'II'I tt e) ee)
--  , forall ee . Wrapper target (T'TTT'TT'I (T'I'II ttt e) (T'II'I tt e) t ee)
--  ) => Mapping T'I'II T'I'II target target (T'I'II target Unit) (T'TTT'TT'I (T'I'II ttt e) (T'II'I tt e) t) where
--  mapping = rewrap `identity` \source -> rewrap
--   `hc_` fj @target @target
--    (component @target @(T'I'II target Unit) @t
--     `compose` component @target @I @(T'I'II target Unit)
--     `compose` wrap @target
--    ) `compose` source `compose` yv Unit

instance
 ( Covariant Yoneda Functor (AR) (AR) I
 -- , Covariant Endo Monoidal Functor (AR) tt tt t
 , Covariant Endo Semi Functor (AR) t
 , Adjoint Functor (AR) (AR) (T'II'I tt e) (T'I'II ttt e)
 , Component (AR) I (T'I'II (AR) Unit)
 , Component (AR) (T'I'II (AR) Unit) t
 , forall ee . Wrapper (AR) (I ee)
 , forall ee . Wrapper (AR) (T'I'II (AR) Unit ee)
 , forall ee . Wrapper (AR) (T'TT'I (T'I'II ttt e) (T'II'I tt e) ee)
 , forall ee . Wrapper (AR) (T'TTT'TT'I (T'I'II ttt e) (T'II'I tt e) t ee)
 ) => Mapping T'I'II T'I'II (AR) (AR) (T'I'II (AR) Unit) (T'TTT'TT'I (T'I'II ttt e) (T'II'I tt e) t) where
 mapping = rewrap `identity` \source -> rewrap
  `hc_` fj @(AR) @(AR)
   (component @(AR) @(T'I'II (AR) Unit) @t
    `compose` component @(AR) @I @(T'I'II (AR) Unit)
    `compose` wrap @(AR)
   ) `compose` source `compose` yv Unit

-- TODO: desugar `fj` and move this instance to `Instances` module
instance
 ( Covariant Endo Semi Functor target t
 , Adjoint Functor target target (T'II'I tt e) (T'I'II ttt e)
 , Covariant Transformation Functor source target (T'II'I tt e `T'TT'I` t) (T'II'I tt e `TT'T'I` t)
 , forall ee . Wrapper target (I ee)
 , forall ee . Wrapper target (T'TT'I (T'II'I tt e) (T'I'II ttt e) ee)
 , forall ee . Wrapper target (T'TT'I (T'I'II ttt e) (T'II'I tt e) ee)
 , forall ee . Wrapper target (T'TT'I (T'II'I tt e) t ee)
 , forall ee . Wrapper target (TT'T'I (T'II'I tt e) t ee)
 , forall ee . Wrapper target (T'TTT'TT'I (T'I'II ttt e) (T'II'I tt e) t ee)
 ) => Mapping T'I'II T'I'II source target t (T'TTT'TT'I (T'I'II ttt e) (T'II'I tt e) t) where
 mapping = rewrap `identity` \source -> wrap @target @(T'TTT'TT'I _ _ _ _)
  `compose` fj (wrapped (map @T'I'II @T'I'II @source @target @(T'II'I tt e `T'TT'I` t) @(T'II'I tt e `TT'T'I` t) source))

instance
 ( Covariant Semi Functor source target t
 , Adjoint Functor target target (T'II'I tt e) (T'I'II ttt e)
 , Covariant Transformation Functor source target (T'II'I tt e `T'TT'I` TT'T'I t tttt) (T'II'I tt e `TT'T'I` TT'T'I t tttt)
 , Component target t (TT'T'I t tttt)
 , forall ee . Wrapper target (I ee)
 , forall ee . Wrapper target (T'TT'I (T'II'I tt e) (T'I'II ttt e) ee)
 , forall ee . Wrapper target (T'TT'I (T'I'II ttt e) (T'II'I tt e) ee)
 , forall ee . Wrapper target (TT'T'I (T'II'I tt e) (TT'T'I t tttt) ee)
 , forall ee . Wrapper target (T'TT'I (T'II'I tt e) (TT'T'I t tttt) ee)
 , forall ee . Wrapper target (TT'T'I (T'II'I tt e) tttt ee)
 , forall ee . Wrapper target (TT'T'I t tttt ee)
 , forall ee . Wrapper target (T'TTT'TT'I (T'I'II ttt e) (T'II'I tt e) (TT'T'I t tttt) ee)
 ) => Mapping T'I'II T'I'II source target t (T'TTT'TT'I (T'I'II ttt e) (T'II'I tt e) (TT'T'I t tttt)) where
 mapping = rewrap `identity` \source -> wrap @target @(T'TTT'TT'I _ _ _ _)
  `compose` fj (wrapped (map @T'I'II @T'I'II @source @target @(T'II'I tt e `T'TT'I` TT'T'I t tttt) @(T'II'I tt e `TT'T'I` TT'T'I t tttt) source))
  `compose` component @target @t @(t `TT'T'I` tttt)

instance
 ( Covariant Semi Functor source target t
 , Adjoint Functor target target (tt) (ttt)
 , Covariant Transformation Functor source target (tt `T'TT'I` TT'T'I tttt t) (tt `TT'T'I` TT'T'I tttt t)
 , Component target t (TT'T'I tttt t)
 , forall ee . Wrapper target (I ee)
 , forall ee . Wrapper target (T'TT'I (tt) (ttt) ee)
 , forall ee . Wrapper target (T'TT'I (ttt) (tt) ee)
 , forall ee . Wrapper target (TT'T'I (tt) (TT'T'I tttt t) ee)
 , forall ee . Wrapper target (T'TT'I (tt) (TT'T'I tttt t) ee)
 , forall ee . Wrapper target (TT'T'I (tt) tttt ee)
 , forall ee . Wrapper target (TT'T'I tttt t ee)
 , forall ee . Wrapper target (T'TTT'TT'I (ttt) (tt) (TT'T'I tttt t) ee)
 ) => Mapping T'I'II T'I'II source target t (T'TTT'TT'I ttt tt (tttt `TT'T'I` t)) where
 mapping = rewrap `identity` \source -> wrap @target @(T'TTT'TT'I _ _ _ _)
  `compose` fj (wrapped (map @T'I'II @T'I'II @source @target @(tt `T'TT'I` TT'T'I tttt t) @(tt `TT'T'I` TT'T'I tttt t) source))
  `compose` component @target @t @(tttt `TT'T'I` t)

instance Mapping T'I'II T'I'II (AR) (AR) (S'I'II e `T'TT'I` S'I'II e `L` S'I'II e `T` l) (S'I'II e) where
 mapping = rewrap `identity` \source -> \case
  T'TT'I (T'I'II (That (Label (T'I'II (That x))))) -> T'I'II (That `identity`source x)
  T'TT'I (T'I'II (That (Label (T'I'II (This e))))) -> T'I'II (This e)
  T'TT'I (T'I'II (This e)) -> T'I'II (This e)

instance Covariant Lax Monoidal Functor (AR) (AR) (P) P Void t =>
 Mapping T'I'II T'I'II (AR) (AR) (S'I'II e `T'TT'I` t `L` t `T` ll `L` S'I'II e `T` l) (S'I'II e `TT'T'I` t) where
 mapping = rewrap `identity` \source -> rewrap `identity` \case
  T'I'II (This e) -> (intro `ha` T'I'II) (This e)
  T'I'II (That x) -> super (super x) `yo` source `ho` That  `ho` T'I'II

instance Mapping T'I'II T'I'II (AR) (AR)
 (T'I'II (T'I'TT'II'I (AR) (P)) i `T'TT'I` S'I'II e `L` S'I'II e `T` Recursive)
 (T'I'II (T'I'TT'II'I (AR) (P)) i) where
 mapping = rewrap `identity` \source -> \(T'TT'I x) ->
  x `yok_` Label @_ @_ @Void
    `ha__` constant @(AR) (map @T'I'II @T'I'II source (T'TT'I x))
      `has` intro @(T'I'II (T'I'TT'II'I (AR) (P)) i) @(AR) `ha` source

instance Mapping T'I'II T'I'II (AR) (AR)
 (T'I'II (T'I'TT'II'I (AR) (P)) i `T'TT'I` I `L` I `T` Recursive)
 (T'I'II (T'I'TT'II'I (AR) (P)) i) where
 mapping = rewrap `identity` \source -> \(T'TT'I x) ->
  x `yok` Label @_ @_ @Void `ha` constant @(AR) (map @T'I'II @T'I'II @_ @_ @_ @(T'I'II (T'I'TT'II'I (AR) (P)) i) source (T'TT'I x)) `ha` super @(AR) `ha` super @(AR)

instance
 ( Covariant Yoneda Functor (AR) (AR) t
 , Covariant Transformation Functor (AR) (AR) (t `T'TT'I` t `L` t `T` Void) t
 , Covariant Transformation Functor (AR) (AR) (T'I'II (AR) Unit) t
 ) => Mapping T'I'II T'I'II (AR) (AR)
 (T'TTT'TT'I (T'I'II (AR) i) (T'II'I (P) i) t `T'TT'I` S'I'II e `L` S'I'II e `T` Recursive)
 (T'TTT'TT'I (T'I'II (AR) i) (T'II'I (P) i) t) where
 mapping = rewrap `identity` \source -> \(T'TT'I x) ->
  x `yok_` Label @_ @_ @Void
    `ha__` constant @(AR) (map @T'I'II @T'I'II source (T'TT'I x))
      `has` intro @(T'TTT'TT'I (T'I'II (AR) i) (T'II'I (P) i) t) @(AR) `ha` source

instance
 ( Covariant Yoneda Functor (AR) (AR) t
 , Covariant Transformation Functor (AR) (AR) (t `T'TT'I` t `L` t `T` Void) t
 ) => Mapping T'I'II T'I'II (AR) (AR)
 (T'TTT'TT'I (T'I'II (AR) i) (T'II'I (P) i) t `T'TT'I` I `L` I `T` Recursive)
 (T'TTT'TT'I (T'I'II (AR) i) (T'II'I (P) i) t) where
 mapping = rewrap `identity` \source -> \(T'TT'I x) ->
  x `yok` Label @_ @_ @Void `ha` constant @(AR) (map @T'I'II @T'I'II @_ @_ @_ @(T'TTT'TT'I (T'I'II (AR) i) (T'II'I (P) i) t) source (T'TT'I x)) `ha` super @(AR) `ha` super @(AR)

-- TODO: generahc_ze using adjunctions

instance (e ~ ee) => Mapping T'I'II T'I'II (AR) (AR)
  (Day T'I'II (AR) (P) P (T'I'II (T'I'TT'II'I (AR) (P)) e) (T'I'II (T'I'TT'II'I (AR) (P)) ee `L` T'I'II (T'I'TT'II'I (AR) (P)) ee `T` Void) eee eeee)
  (T'I'II (T'I'TT'II'I (AR) (P)) e) where
 mapping = rewrap `identity` \source -> rewrap `identity` \case
  These (These ee eee) (T'I'II f) -> T'I'TT'II'I `hc_` \old ->
   let These x new = ee `hc` old in
   let These y upd  = eee `hc` new in
   source `ha` f `hc__` x `hjd` y `hjd___` upd

instance (e ~ ee) => Mapping T'I'II T'I'II (AR) (AR)
  (Day T'I'II (AR) (P) P (T'I'II (T'I'TT'II'I (AR) (P)) e) (T'I'II (T'I'TT'II'I (AR) (P)) ee `L` T'I'II (T'I'TT'II'I (AR) (P)) ee `T` (Void `P` Void)) eee eeee)
  (T'I'II (T'I'TT'II'I (AR) (P)) e) where
 mapping = rewrap `identity` \source -> rewrap `identity` \case
  These (These ee eee) (T'I'II f) -> T'I'TT'II'I `hc_` \old ->
   let These x _ = ee `hc` old in
   let These y _  = eee `hc` old in
   source `ha` f `hc__` x `hjd` y `hjd___` old

instance
 ( i ~ ii
 , Covariant Transformation Functor (AR) (AR) (t `T'TT'I` t `L` t `T` Void) t
 , Covariant Yoneda Functor (AR) (AR) t
 ) => Mapping T'I'II T'I'II (AR) (AR)
  (Day T'I'II (AR) (P) P (T'TTT'TT'I (T'I'II (AR) i) (T'II'I (P) i) t)
   (T'TTT'TT'I (T'I'II (AR) ii) (T'II'I (P) ii) t `L` T'TTT'TT'I (T'I'II (AR) ii) (T'II'I (P) ii) t `T` Void) eee eeee)
  (T'TTT'TT'I (T'I'II (AR) i) (T'II'I (P) i) t) where
 mapping = rewrap `identity` \source -> rewrap `identity` \case
  These (These (T'TTT'TT'I (T'I'II x)) (Label (T'TTT'TT'I (T'I'II y)))) (T'I'II f) ->
   T'I'II `identity` \old -> x old `yok` \(T'II'I (These e btw)) ->
    Label @_ @_ @Void (source `compose` f `compose` (e `hjd`) `fo'fo` y btw)

instance
 ( i ~ ii
 , Covariant Transformation Functor (AR) (AR) (t `T'TT'I` t `L` t `T` Void) t
 , forall e ee . Mapping T'I'II T'I'II (AR) (AR) (Covariant Day (AR) (P) (P) t (t `L` t `T` Void) e ee) t
 , Covariant Yoneda Functor (AR) (AR) t
 ) => Mapping T'I'II T'I'II (AR) (AR)
  (Day T'I'II (AR) (P) P (T'TTT'TT'I (T'I'II (AR) i) (T'II'I (P) i) t) (t `L` t `T` Void) eee eeee)
  (T'TTT'TT'I (T'I'II (AR) i) (T'II'I (P) i) t) where
 mapping = rewrap `identity` \source -> rewrap `identity` \case
  These (These (T'TTT'TT'I (T'I'II x)) xx) (T'I'II f) ->
   T'I'II `identity` \old ->
    day @T'I'II @(AR) @Void @t @t @(P) @(P) identity
    (\(These i ii) -> i `yo` (`hjd` ii) `ho` f `ho` source)
    (x old `hjd` xx)

-- instance
 -- ( Component (AR) (t `T'TT'I` t) t
 -- , Covariant Endo Monoidal Functor (AR) (P) P t
 -- ) => Mapping T'I'II T'I'II (AR) (AR)
  -- (Day T'I'II (AR) (P) P (T'TT'I (T'I'II (AR) a) t) (T'I'II (AR) a `T'TT'I` t) ee eee)
  -- (T'TT'I (T'I'II (AR) a) t) where
 -- mapping = rewrap `identity` \source -> rewrap `identity` \case
  -- These (These (T'TT'I (T'I'II f)) (T'TT'I (T'I'II g))) (T'I'II h) -> T'I'II `identity` \x ->
   -- yp (These (f x) (g x)) `yo` h `ho` source

instance Covariant Lax Monoidal Functor (AR)  (AR) (P) P Void t =>
 Mapping T'I'II T'I'II (AR) (AR) (T'I'II (AR) Unit) (S'I'II e `TT'T'I` t) where
 mapping = rewrap `identity` \source (T'I'II f) ->
  TT'T'I `compose` intro `compose` T'I'II `compose` That `compose` source `identity`f Unit

-- TODO: Finish, it's for Halts transformer
instance Covariant Lax Monoidal Functor (AR)  (AR) (P) P Void t =>
 Mapping T'I'II T'I'II (AR) (AR)
  (Day T'I'II (AR) (P) P (S'I'II e `TT'T'I` t) ((S'I'II e `TT'T'I` t) `L` (S'I'II e `TT'T'I` t) `T` Void) ee eee)
  (S'I'II e `TT'T'I` t) where
 mapping = rewrap `identity` \source -> rewrap `identity` \case

-- 1. t (tt (t (tt _)))
-- 2. t (t (tt (tt _)))
-- 3. t (t (tt _))
-- 4. t (tt _)
-- instance
--  ( Covariant Endo Semi Functor target t
--  , Covariant Endo Semi Functor target tt
--  , Covariant Endo Transformation Functor target (t `T'TT'I` t `L` t `T` Void) t
--  , Covariant Endo Transformation Functor target (tt `T'TT'I` t `L` t `T` Void `L` tt `T` Void) (tt `TT'T'I` t)
--  , Covariant Endo Transformation Functor target (tt `T'TT'I` tt) tt
--  , forall e . Wrapper target (((tt `T'TT'I` t) `T'TT'I` (tt `TT'T'I` t)) e)
--  , forall e . Wrapper target (((tt `TT'T'I` t) `T'TT'I` (tt `TT'T'I` t) `L` (tt `TT'T'I` t) `T` Void) e)
--  , forall e . Wrapper target ((tt `T'TT'I` t) ((tt `TT'T'I` t) e))
--  , forall e . Wrapper target (t `T'TT'I` t `L` t `T` Void `T'I_` e)
--  , forall e . Wrapper target (tt `TT'T'I` t `T'I_` e)
--  , forall e . Wrapper target (tt `T'TT'I` t `L` t `T` Void `L` tt `T` Void `T'I_` e)
--  , forall e . Wrapper target (tt `T'TT'I` t `L` t `T` Void `T'I_` e)
--  , forall e . Wrapper target (tt `T'TT'I` tt `T'I_` e)
--  , forall e . Wrapper target (t `L` t `T` Void `L` tt `T` Void `T` e)
--  , forall e . Wrapper target (t `L` t `T` Void `T` e)
--  , forall e . Wrapper target ((tt `TT'T'I` t) `L` (tt `TT'T'I` t) `T` Void `T` e)
--  ) => Mapping T'I'II T'I'II target target ((tt `TT'T'I` t) `T'TT'I` (tt `TT'T'I` t) `L` (tt `TT'T'I` t) `T` Void) (tt `TT'T'I` t) where
--  mapping = rewrap `identity` \source -> rewrap
--   `hc_` component @target @(t `T'TT'I` t `L` t `T` Void) @t
--   `compose` wrap @target
--   `compose` map @T'I'II @T'I'II @target @target @t @t
--   (wrap @_ @(t `L` t `T` Void `T` _)
--    `compose` map @T'I'II @T'I'II @target @target @t @t
--     (map @T'I'II @T'I'II @target @target @(tt `T'TT'I` tt) @tt source `compose` wrap @target)
--     `compose` wrapped (component @target @(tt `T'TT'I` t `L` t `T` Void `L` tt `T` Void) @(tt `TT'T'I` t))
--     `compose` map @T'I'II @T'I'II @target @target @tt @tt
--      (wrap @target @(t `L` t `T` Void `L` tt `T` Void `T` _) `compose` wrap @target @(t `L` t `T` Void `T` _) `compose` super `compose` super)
--    )
--    `compose` super @target @(TT'T'I _ _ _)

-- TODO: generahc_ze with hc_mits
instance Covariant Endo Semi Functor (AR) t =>
 Mapping T'I'II T'I'II (AR) (AR) (P'I'II e `T'TT'I` t `L` t `T` Void `L` P'I'II e `T` Void) (P'I'II e `TT'T'I` t) where
 mapping = rewrap `identity` \source -> rewrap `identity` \case
  T'I'II (These e x) -> super (super x) `yo` source `ho` These e `ho` T'I'II

-- TODO: generahc_ze with hc_mits
instance Covariant Endo Semi Functor (AR) t =>
 Mapping T'I'II T'I'II (AR) (AR) (P'II'I e `T'TT'I` t `L` t `T` Void `L` P'II'I e `T` Void) (P'II'I e `TT'T'I` t) where
 mapping = rewrap `identity` \source -> rewrap `identity` \case
  T'II'I (These x e) -> super (super x) `yo` source `ho` (`hjd` e) `ho` T'II'I

-- instance Covariant Endo Semi Functor (AR) t =>
--  Mapping T'I'II T'I'II (AR) (AR) (t `T'TT'I` T'I'II (AR) e `L` T'I'II (AR) e `T` Void `L` t `T` Void) (t `TT'T'I` T'I'II (AR) e) where
--  mapping = rewrap `identity` \source -> rewrap `identity` \x ->
--   T'I'II `identity` \e -> x `yo` source `compose` (`hc_` e) `compose` super

-- TODO: generahc_ze
-- We need this instance to make `yok'yoklKL` work
-- instance {-# OVERLAPS #-} Component (AR) (T'TT'I t tt) t =>
 -- Mapping T'I'II T'I'II (AR) (AR) (T'TT'I t (Label l tt)) t where
 -- mapping = rewrap `identity` \source ->
  -- map @T'I'II @T'I'II @(AR) @(AR) @(T'TT'I t tt) @t source `compose` rewrap @_ @(AR) (fo @(AR) super)

instance
 ( Covariant Lax Monoidal Functor (AR) (AR) (P) P Void t
 , Mapping T'I'II T'I'II (AR) (AR) (T'I'II (AR) Unit) t
 ) => Mapping T'I'II T'I'II (AR) (AR) (T'I'II (AR) Unit) (t `L` t `T` l) where
 mapping = rewrap `identity` \source -> rewrap `identity` \f -> intro `compose` source `identity`f Unit

instance
 ( forall e ee . Covariant Transformation Functor target target (Covariant Day target u uu t (tt `L` tt `T` ll) e ee) t
 , Covariant Endo Semi Functor target (T'II'I u (tt `L` tt `T` ll `T` ee))
 , Covariant Endo Semi Functor target (T'I'II u (t `L` t `T` l `T` e))
 , forall eee . Mapping T'I'II T'I'II target target (T'II'I (P) eee) (T'II'I (P) eee)
 , forall eee . Wrapper target (t `L` t `T` l `T` eee)
 , forall eee . Wrapper target (Day T'I'II target u uu t t e ee eee)
 , forall eee . Wrapper target (Day T'I'II target u uu (t `L` t `T` l) (tt `L` tt `T` ll) e ee eee)
 , forall eee . Wrapper target (Day T'I'II target u uu t (tt `L` tt `T` ll) e ee eee)
 , forall eee eeee . Wrapper target (T'I'II u eee eeee)
 , forall eee eeee . Wrapper target (T'II'I u eee eeee)
 , forall eee eeee . Wrapper target (T'II'I (P) eee eeee)
 ) => Mapping T'I'II T'I'II target target (Day T'I'II target u uu (t `L` t `T` l) (tt `L` tt `T` ll) e ee) (t `L` t `T` l) where
 mapping = rewrap `identity` \source -> rewrap `hc_`
   map @T'I'II @T'I'II @target @target @(Day T'I'II target u uu t (tt `L` tt `T` ll) _ _) @t source
   `compose` wrap `compose` foi (foi @target @target super)

instance {-# OVERLAPPABLE #-}
 ( Covariant Transformation Functor (AR) (AR) t tt
 , Covariant Transformation Functor (AR) (AR) tt t
 ) => Component (AT) t tt where
 component = T'I'TT'II'T'II'I `identity` \x ->
  map @T'I'II @T'I'II @(AR) @(AR) @t @tt identity x
  `hjd` map @T'I'II @T'I'II @(AR) @(AR) @tt @t identity

instance {-# OVERLAPPABLE #-}
 Mapping T'I'II T'I'II (AR) (AR) t t
 => Mapping T'I'II T'I'II (AT) (AR) t t where
 mapping = rewrap `identity` \(T'I'TT'II'T'II'I source) x ->
  map @T'I'II @T'I'II @(AR) @(AR) @t @t (this `compose` source) x

instance Mapping T'II'I T'I'II (AT) (AR)
 (T'II'I (T'I'TT'II'I (AR) (P)) e)
 (T'II'I (T'I'TT'II'I (AR) (P)) e) where
 mapping = rewrap `identity` \(T'I'TT'II'T'II'I source) ->
  rewrap `compose` rewrap `identity` \state old ->
   let (These new f) = source old in f `fio` state new

-- TODO: I'm not sure about this instance
instance Mapping T'II'I T'I'II (AT) (AT)
 (T'II'I (T'I'TT'II'I (AR) (P)) i)
 (T'II'I (T'I'TT'II'I (AR) (P)) i) where
 mapping = rewrap `compose` rewrap `identity` \source x ->
  These (map @T'II'I @T'I'II (T'I'TT'II'T'II'I source) x)
   (constant @(AR) x)

-- instance
 -- ( Mapping T'I'II T'I'II (AR) (AR) (t `TT'T'I` tt) (t `T'TT'I` tt `L` tt `T` ll `L` t `T` l)
 -- , Mapping T'I'II T'I'II (AR) (AR) (t `T'TT'I` tt `L` tt `T` ll `L` t `T` l) (t `TT'T'I` tt)
 -- ) => Mapping T'I'II T'I'II (AT) (AT) (t `T'TT'I` tt `L` tt `T` ll `L` t `T` l) (t `TT'T'I` tt) where
 -- mapping = rewrap `compose` rewrap `identity` \source x ->
  -- map @T'I'II @T'I'II @(AR) @(AR) @(t `T'TT'I` tt `L` tt `T` ll `L` t `T` l) @(t `TT'T'I` tt) (this `ha` source) x
  -- `hjd` _

-- TODO: try to generahc_se
instance
 ( Covariant Endo Semi Functor (AR) t
 , Covariant Endo Semi Functor (AR) tt
 , Mapping T'I'II T'I'II (AR) (AR) t (t `T'TT'I` t `L` t `T` Void)
 , Mapping T'I'II T'I'II (AR) (AR) tt (tt `T'TT'I` tt `L` tt `T` Void)
 ) => Mapping T'I'II T'I'II (AR) (AR) (t `S'T'I'TT'I` tt) ((t `S'T'I'TT'I` tt) `T'TT'I` (t `S'T'I'TT'I` tt) `L` (t `S'T'I'TT'I` tt) `T` Void) where
 mapping = rewrap `identity` \source -> T'TT'I'TTT'I `ho` T'TT'I
  `ha____` map @T'I'II @T'I'II @AR @AR @t @(t `T'TT'I` t `L` t `T` Void) source
    `ho__` super @AR @(t `T'TT'I` t `L` t `T` Void `T'I_` _)
    `ho__'yo` rewrap @AR @(t `L` t `T` Void `T` _) @((t `S'T'I'TT'I` tt) `L` (t `S'T'I'TT'I` tt) `T` Void `T` _) `hc_` This `ho` T'TT'I'TTT'I
    `ho__` This
    `has__` map @T'I'II @T'I'II @AR @AR @tt @(tt `T'TT'I` tt `L` tt `T` Void) source
    `ho__` super @AR @(tt `T'TT'I` tt `L` tt `T` Void `T'I_` _)
    `ho__'yo` rewrap @AR @(tt `L` tt `T` Void `T` _) @((t `S'T'I'TT'I` tt) `L` (t `S'T'I'TT'I` tt) `T` Void `T` _) `hc_` That `ho` T'TT'I'TTT'I
    `ho__` That

-- TODO: try to generahc_se
instance
 ( Covariant Endo Semi Functor (AR) t
 , Covariant Endo Semi Functor (AR) tt
 , Mapping T'I'II T'I'II (AR) (AR) t (t `T'TT'I` t `L` t `T` Void)
 , Mapping T'I'II T'I'II (AR) (AR) tt (tt `T'TT'I` tt `L` tt `T` Void)
 ) => Mapping T'I'II T'I'II (AR) (AR) (t `P'T'I'TT'I` tt) ((t `P'T'I'TT'I` tt) `T'TT'I` (t `P'T'I'TT'I` tt) `L` (t `P'T'I'TT'I` tt) `T` Void) where
 mapping = rewrap `identity` \source -> T'TT'I'TTT'I `ho` T'TT'I
  `ha____` (is `ho'st` this
    `ho` map @T'I'II @T'I'II @AR @AR @t @(t `T'TT'I` t `L` t `T` Void) source
    `ho` super @AR @(t `T'TT'I` t `L` t `T` Void `T'I_` _)
    `hop` is `ho'st` that `ho'yo` source
   `ho__` (\(These x xx) -> x `yo` rewrap ((`hjd_` xx) `ho` T'TT'I'TTT'I)))
   `hop__` (is `ho'st` that
    `ho` map @T'I'II @T'I'II @AR @AR @tt @(tt `T'TT'I` tt `L` tt `T` Void) source
    `ho` super @AR @(tt `T'TT'I` tt `L` tt `T` Void `T'I_` _)
    `hop` is `ho'st` this `ho'yo` source
   `ho__` (\(These x xx) -> x `yo` rewrap ((xx `hjd_`) `ho` T'TT'I'TTT'I)))

instance Mapping T'I'II T'I'II (AR) (AR) (T'I'I (S)) (T'I'II (AR) Unit) where
 mapping = rewrap `identity` \source -> T'I'II `ha` wrap @AR `ha` source `has` T'I'II `ha` wrap @AR `ha` source

-- TODO: generahc_ze over categories
instance {-# OVERLAPPABLE #-}
 (Setoid (AR) (Supertype e), Wrapper (AR) e)
 => Setoid (AR) e where
 equality (These x xx) = equality (super x `hjd` super xx)
  `yoi` (`yoi` wrap @(AR)) `ho` (`yio` wrap @(AR))
  `yio` wrap @(AR)

instance {-# OVERLAPS #-} Setoid (AR) Unit where
 equality _ = That Unit

instance {-# OVERLAPS #-} (Setoid (AR) e, Setoid (AR) ee) => Setoid (AR) (e `S` ee) where
 equality (These (This x) (This xx)) = equality (x `hjd` xx) `yoi` (`yio` This) `ho` (`yoi` This) `yio` This
 equality (These (That x) (That xx)) = equality (x `hjd` xx) `yoi` (`yio` That) `ho` (`yoi` That) `yio` That
 equality (These x xx) = This (These x xx)

instance {-# OVERLAPS #-} (Setoid (AR) e, Setoid (AR) ee) => Setoid (AR) (e `P` ee) where
 equality (These (These x xx) (These xxx xxxx)) = case equality (x `hjd` xxx) `hjd` equality (xx `hjd` xxxx) of
  These (That x') (That xx') -> That (These x' xx')
  These _ _ -> This ((x `hjd` xx) `hjd` (xxx `hjd` xxxx))

type instance Supertype (e `P` (ee `P` eee)) = e `P` ee `P` eee

instance Elicitable T'II'I (AR) (e `P` (ee `P` eee))
 where elicit = T'II'I (\(These (These x xx) xxx) -> These x (These xx xxx))

instance Elicitable T'I'II (AR) (e `P` (ee `P` eee))
 where elicit = T'I'II (\(These x (These xx xxx)) -> These (These x xx) xxx)

type instance Supertype (e `S` (ee `S` eee)) = e `S` ee `S` eee

instance Elicitable T'II'I (AR) (e `S` (ee `S` eee))
 where elicit = T'II'I (This `has` (That `ha` This) `has_` That `ha` That)

instance Elicitable T'I'II (AR) (e `S` (ee `S` eee))
 where elicit = T'I'II (This `ha` This `has_` This `ha` That `has` That)
