{-# OPTIONS_GHC -fno-warn-orphans #-}
{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE UndecidableInstances #-}
module Ya.Algebra (module Exports) where

import Ya.Algebra.Abstract as Exports
import Ya.Algebra.Definition as Exports
import Ya.Algebra.Instances as Exports ()
import Ya.Algebra.Operators as Exports

-- TODO: reduce a number of transformations here
instance
 ( Covariant Endo Semi Functor AR t
 , Covariant Monoidal Functor AR LM LM tt
 , Component Natural AR AR (t `T'TT'I` tt) (t `TT'T'I` tt)
 , Component Natural AR AR (Labeled l (R_U_I_T_I LM t) `T'TT'I` tt) (Labeled l (R_U_I_T_I LM t) `TT'T'I` tt)
 ) => Mapping Straight Straight AR AR
  (Labeled l (t `T'TT'I` R_U_I_T_I LM t) `T'TT'I` tt)
  (Labeled l (t `T'TT'I` R_U_I_T_I LM t) `TT'T'I` tt) where
 mapping = rewrap / \from -> rewrap / \x -> unwrap (unwrap x)
   `yo` wrapped (map @Straight @Straight @AR @AR
            @(Labeled l (R_U_I_T_I LM t) `T'TT'I` tt)
            @(Labeled l (R_U_I_T_I LM t) `TT'T'I` tt) from)
          `ha` wrap @AR @(Labeled l (R_U_I_T_I LM t) (tt _))
   `yi` wrapped (map @Straight @Straight @AR @AR @(t `T'TT'I` tt) @(t `TT'T'I` tt) unwrap)
   `yo` wrap @AR @(Labeled l _ _)
   `ha` wrap @AR @(T'TT'I t (R_U_I_T_I LM t) _)

-- TODO: reduce a number of transformations here
instance
 ( Covariant Endo Semi Functor AR t
 , Covariant Endo Semi Functor AR tt
 , Covariant Monoidal Functor AR LM LM tt
 , Transformation Straight Functor AR AR (T'TT'I t tt) (TT'T'I t tt)
 ) => Mapping Straight Straight AR AR
  (Labeled (U_I_II AR Unit Unit) (R_U_I_T_I LM t) `T'TT'I` tt)
  (Labeled (U_I_II AR Unit Unit) (R_U_I_T_I LM t) `TT'T'I` tt) where
 mapping = rewrap / \from -> rewrap /
  \(T_'_I (R_U_I_T_I (Recursive (U_I_T_II (These x xs))))) ->
    x `yo` from `lu`
     (wrapped (map @Straight @Straight @AR @_ @(t `T'TT'I` tt) @(t `TT'T'I` tt) (unwrap @AR @(R_U_I_T_I _ _ _) `ha` unwrap @AR @(Labeled _ _ _)))
      (xs `yo` wrap @AR @(R_U_I_T_I _ _ _)
       `ho` wrap @AR @(Labeled (U_I_II AR Unit Unit) _ _)
       `ho` wrapped (map @Straight @Straight @AR @AR
         @(Labeled (U_I_II AR Unit Unit) (R_U_I_T_I LM t) `T'TT'I` tt)
         @(Labeled (U_I_II AR Unit Unit) (R_U_I_T_I LM t) `TT'T'I` tt)
         from)
      )
     ) `yp'yo` wrap @AR @(Labeled _ _ _)
         `ha` wrap @AR @(R_U_I_T_I _ _ _)
         `ha` wrap @AR @(Recursive _)
         `ha` wrap @AR @(U_I_T_II _ _ _ _)

-- TODO: reduce a number of transformations here
instance
 ( Covariant Endo Semi Functor AR t
 , Covariant Endo Semi Functor AR tt
 , Covariant Monoidal Functor AR LM LM tt
 , Transformation Straight Functor AR AR (t `T'TT'I` tt) (t `TT'T'I` tt)
 ) => Mapping Straight Straight AR AR
  (Labeled (U_II_I AR Unit Unit) (R_U_I_T_I LM t) `T'TT'I` tt)
  (Labeled (U_II_I AR Unit Unit) (R_U_I_T_I LM t) `TT'T'I` tt) where
 mapping = rewrap / \from -> rewrap
  / \(T_'_I (R_U_I_T_I (Recursive (U_I_T_II (These x xs))))) ->
   (These
    `ho_'ho` wrap @AR @(U_I_T_II _ _ _ _)
    `ho` wrap @AR @(Recursive _)
    `ho` wrap @AR @(R_U_I_T_I _ _ _)
    `ho` wrap @AR @(Labeled _ _ _))
   `fo` (x `yo` from)
   `fc` wrapped (map @Straight @Straight @AR @_ @(t `T'TT'I` tt) @(t `TT'T'I` tt)
         (unwrap @AR @(R_U_I_T_I _ _ _) `ha` unwrap @AR @(Labeled _ _ _))
        )
    (xs
     `yo` wrap @AR @(R_U_I_T_I _ _ _)
     `ho` wrap @AR @(Labeled _ _ _)
     `ho` wrapped (map @Straight @Straight @AR @AR
        @(Labeled (U_II_I AR Unit Unit) (R_U_I_T_I LM t) `T'TT'I` tt)
        @(Labeled (U_II_I AR Unit Unit) (R_U_I_T_I LM t) `TT'T'I` tt)
        from)
    )

-- TODO: try to simplify
instance
 Mapping Straight Straight AR AR
  (Day Straight AR LM LM t t (Recursive (U_I_T_II t LM e)) (Recursive (U_I_T_II t LM ee))) t =>
 Mapping Straight Straight AR AR
  (Day Straight AR LM LM (R_U_I_T_I LM t) (R_U_I_T_I LM t) e ee) (R_U_I_T_I LM t) where
 mapping = rewrap / \from -> rewrap / \case
  These (These e ee) (Straight f) ->
   let These e_ e__ = he'he'he e in
   let These ee_ ee__ = he'he'he ee in
   Recursive `compose` U_I_T_II / These
    (from `compose` f / These e_ ee_)
    (day @Straight @AR @t @LM @LM identity
     (unwrap
      `compose` day @Straight @AR
       @(R_U_I_T_I LM t) @LM @LM
        identity (from `compose` f)
      `compose` fio R_U_I_T_I
      `compose` foi R_U_I_T_I)
     / These e__ ee__)

instance
 (Initial AR, Monoidal Straight Functor AR LM ML t) =>
 Mapping Straight Straight AR AR (Straight AR Unit) (R_U_I_T_I LM t) where
 mapping = rewrap / \from (Straight f) ->
  R_U_I_T_I `compose` Recursive `compose` U_I_T_II
   / These (from / f Unit) (empty @t `yo` initial @AR)

instance
 ( Mapping Straight Straight AR AR (Day Straight AR LM LM t t (R_U_I_T_I LM t e) (R_U_I_T_I LM t ee)) t
 , Mapping Straight Straight AR AR (Day Straight AR LM LM t t (Recursive (U_I_T_II t LM e)) (Recursive (U_I_T_II t LM ee))) t
 ) => Mapping Straight Straight AR AR (Day Straight AR LM LM (t `T'TT'I` R_U_I_T_I LM t) (t `T'TT'I` R_U_I_T_I LM t) e ee) (t `T'TT'I` R_U_I_T_I LM t) where
 mapping = rewrap / \from -> rewrap / \case
  These (These (T'TT'I e) (T'TT'I ee)) (Straight f) ->
    day @Straight @AR @t @LM @LM identity
     (day @Straight @AR @(R_U_I_T_I LM t) @LM @LM identity (from `compose` f))
      (These e ee)

instance
 ( Monoidal Straight Functor AR LM LM t
 , Monoidal Straight Functor AR LM LM (R_U_I_T_I LM tt)
 ) => Mapping Straight Straight AR AR (Straight AR Unit) (t `T'TT'I` R_U_I_T_I LM tt) where
 mapping = rewrap / \from (Straight f) -> T'TT'I /
  enter @t `yu` (enter @(R_U_I_T_I LM tt) `yo` from `compose` f)

-- TODO: try to avoid mapping twice datastructure here
instance
 ( Covariant Endo Semi Functor AR t
 , Mapping Straight Straight AR AR (Day Straight AR LM MLM t t (R_U_I_T_I LM t e) (R_U_I_T_I LM t ee)) t
 , Mapping Straight Straight AR AR (Day Straight AR LM MLM t t (Recursive (U_I_T_II t LM e)) (Recursive (U_I_T_II t LM ee))) t
 ) => Mapping Straight Straight AR AR (Day Straight AR LM MLM (t `T'TT'I` R_U_I_T_I LM t) (t `T'TT'I` R_U_I_T_I LM t) e ee) (t `T'TT'I` R_U_I_T_I LM t) where
 mapping = rewrap / \from -> rewrap / \case
  These (These (T'TT'I e) (T'TT'I ee)) (Straight f) ->
    (day @Straight @AR @t @LM @MLM identity
     (\case
      U_U_I_II_UU_I_II (This (This x)) -> x `yo` from `compose` f `compose` U_U_I_II_UU_I_II `compose` This `compose` This
      U_U_I_II_UU_I_II (This (That x)) -> x `yo` from `compose` f `compose` U_U_I_II_UU_I_II `compose` This `compose` That
      U_U_I_II_UU_I_II (That x) -> day @Straight @AR @(R_U_I_T_I LM t) @LM @MLM identity (from `compose` f) x
     )
      (These e ee)
    )

-- TODO: try to avoid mapping twice datastructure here
instance
 ( Covariant Endo Semi Functor AR t
 , Mapping Straight Straight AR AR (Day Straight AR LM MLM t t (Recursive (U_I_T_II t LM e)) (Recursive (U_I_T_II t LM ee))) t
 ) => Mapping Straight Straight AR AR (Day Straight AR LM MLM (R_U_I_T_I LM t) (R_U_I_T_I LM t) e ee) (R_U_I_T_I LM t) where
 mapping = rewrap / \from -> rewrap / \case
  These (These e ee) (Straight f) ->
   let These e_ e__ = he'he'he e in
   let These ee_ ee__ = he'he'he ee in
   Recursive `compose` U_I_T_II / These
    (from `compose` f `compose` U_U_I_II_UU_I_II `compose` That / These e_ ee_)
    (day @Straight @AR @t @LM @MLM identity
     (unwrap @AR `compose` \case
      U_U_I_II_UU_I_II (This (This x)) -> R_U_I_T_I x `yo` from `compose` f `compose` U_U_I_II_UU_I_II `compose` This `compose` This
      U_U_I_II_UU_I_II (This (That x)) -> R_U_I_T_I x `yo` from `compose` f `compose` U_U_I_II_UU_I_II `compose` This `compose` That
      U_U_I_II_UU_I_II (That (These x xx)) -> day @Straight @AR @(R_U_I_T_I LM t) @LM @MLM identity (from `compose` f)
       (These (R_U_I_T_I x) (R_U_I_T_I xx))
     )
     / These e__ ee__)

instance (Initial AR, Monoidal Straight Functor AR LM ML t) =>
 Mapping Straight Straight AR AR (Straight AR Void) (t `T'TT'I` R_U_I_T_I LM tt) where
 mapping = rewrap / \_ _ -> T'TT'I (empty @t `yo` initial @AR)

-- TODO: generalize this instance
instance Mapping Opposite Straight (U_I_UU_II_U_II_I AR LM )AR
 (U_II_I (U_I_UU_II_I AR LM) e)
 (U_II_I (U_I_UU_II_I AR LM) e) where
 mapping = rewrap / \(U_I_UU_II_U_II_I from) ->
  rewrap `compose` rewrap `identity` \state old ->
   let (These new f) = from old in f `fio` state new

instance Mapping Straight Straight (U_I_UU_II_U_II_I AR LM) (U_I_UU_II_U_II_I AR LM) (U_I_II LM e) (U_I_II LM e) where
 mapping = rewrap / \(U_I_UU_II_U_II_I from) -> U_I_UU_II_U_II_I / \(U_I_II (These e x)) ->
   let s = from x in U_I_II (These e (this s)) `lu` fo (that s)

instance Mapping Straight Straight (U_I_UU_II_U_II_I AR LM) (U_I_UU_II_U_II_I AR LM) (U_II_I LM e) (U_II_I LM e) where
 mapping = rewrap / \(U_I_UU_II_U_II_I from) -> U_I_UU_II_U_II_I / \(U_II_I (These x e)) ->
   let s = from x in U_II_I (These (this s) e) `lu` fo (that s)

-- TODO: I'm not really sure about this instance... it could easily lead to an error!
instance Mapping Straight Straight (U_I_UU_II_U_II_I AR LM) (U_I_UU_II_U_II_I AR LM) Identity (U_I_I LM) where
 mapping = rewrap / \(U_I_UU_II_U_II_I from) -> U_I_UU_II_U_II_I / \(Identity x) ->
   let s = from x in U_I_I (this s `lu`this s) `lu` (\(U_I_I (These _ _)) -> Identity (that s (this s)))

instance Mapping Straight Straight (U_I_UU_II_U_II_I AR LM) (U_I_UU_II_U_II_I AR LM) (U_I_II LM e) Identity where
 mapping = rewrap / \(U_I_UU_II_U_II_I from) -> U_I_UU_II_U_II_I / \(U_I_II (These e x)) ->
   let s = from x in Identity (this s) `lu` (U_I_II `compose` (e `lu`) `compose` that s `compose` unwrap)

instance Mapping Straight Straight (U_I_UU_II_U_II_I AR LM) (U_I_UU_II_U_II_I AR LM) (U_II_I LM e) Identity where
 mapping = rewrap / \(U_I_UU_II_U_II_I from) -> U_I_UU_II_U_II_I / \(U_II_I (These x e)) ->
   let s = from x in Identity (this s) `lu` (U_II_I `compose` (`lu` e) `compose` that s `compose` unwrap)

-- TODO: I should alse test how attributes behave on sums

instance Mapping Straight Straight AR AR
 (T'TT'I
  (U_I_II (U_I_UU_II_I AR LM) e)
  (U_I_II (U_I_UU_II_I AR LM) e)
 )
 (U_I_II (U_I_UU_II_I AR LM) e) where
 mapping = rewrap / \from ->
  \(T'TT'I (U_I_II (U_I_UU_II_I state))) ->
   U_I_II `compose` U_I_UU_II_I `identity` \old ->
    let These (U_I_II (U_I_UU_II_I f)) s = state old in
     from `foi` f s

instance (Covariant Monoidal Functor AR LM LM t, e ~ ee)
 => Mapping Straight Straight AR AR
  (U_I_II (U_I_UU_II_I AR LM) ee)
  (T'TTT'TT'I (U_I_II AR e) (U_II_I LM e) t) where
 mapping = rewrap / \from (U_I_II (U_I_UU_II_I x)) ->
  wrap @_ @(T'TTT'TT'I _ _ _ _)
  `compose` wrap @_ @(U_I_II _ _ _)
  `identity` (yu enter
   `compose` map @Straight @Straight from
   `compose` wrap @_ @(U_II_I _ _ _)
   `compose` x)

-- x: ee -> Object Straight AR a ee

instance  {-# OVERLAPPABLE #-} Component Natural AR AR (T'TT'I t tt) t => Mapping Straight Straight AR AR
 (T'TT'I (Straight AR e `T'TT'I` t) tt) (Straight AR e `T'TT'I` t) where
 mapping = rewrap / \from -> rewrap `compose` rewrap /
  \(Straight f) e -> map @Straight @Straight @AR @AR @(t `T'TT'I` tt) @t from (T'TT'I (f e))

instance {-# OVERLAPS #-} Covariant Endo Semi Functor AR t => Mapping Straight Straight AR AR
 (T'TT'I (Straight AR e `T'TT'I` t) (Straight AR e)) (Straight AR e `T'TT'I` t) where
 mapping = rewrap / \from -> rewrap `compose` rewrap /
  \(Straight f) e -> f e `yo` unwrap @AR `ho` (`li` e) `ho` from

-- NOTE: this version allow different type of states, but it requires providing types to make it compile
instance
 ( Covariant Endo Semi Functor AR t
 , Transformation Natural Functor AR AR (T'TT'I t t) t
 ) => Mapping Straight Straight AR AR
 (T'TT'I
  ((U_I_II AR old `T'TTT'TT'I` U_II_I LM btw) t)
  ((U_I_II AR btw `T'TTT'TT'I` U_II_I LM new) t)
 )
 (T'TTT'TT'I (U_I_II AR old) (U_II_I LM new) t) where
 mapping = rewrap / \from -> rewrap `compose` rewrap /
  \(U_I_II x) -> component @Straight @AR @AR @(t `T'TT'I` t) @t
  `compose` wrap @AR @(T'TT'I _ _ _)
  `compose` map @Straight @Straight @AR @AR @t @t
   (fd @AR @AR (unwrap `compose` fo from))
  `compose` x

-- TODO: try to use adjunctions here
instance
 ( Covariant Monoidal Functor AR LM LM tt
 , Transformation Natural Functor AR AR (T'TT'I tt tt) tt
 , e ~ ee
 ) => Mapping Straight Straight AR AR
 (T'TT'I
  (T'TTT'TT'I (U_I_II AR e) (U_II_I LM e) tt)
  (U_I_II (U_I_UU_II_I AR LM) ee)
 )
 (T'TTT'TT'I (U_I_II AR e) (U_II_I LM e) tt) where
  mapping = rewrap / \from -> rewrap `compose` rewrap / \(U_I_II x) ->
    \old -> x old `yok` \(U_II_I (These (U_I_II (U_I_UU_II_I f)) btw))
      -> yu (enter @tt) / U_II_I (f btw) `yo` from

instance
 ( Covariant Functor into into t
 , Covariant Endo Semi Functor into (ttt e)
 , Mapping Straight Straight into into (t `T'TT'I` t) t
 , Mapping Straight Straight into into (tt e `T'TT'I` t) (tt e `TT'T'I` t)
 , forall ee . Wrapper into (T'TTT'TT'I (ttt e) (tt e) t ee)
 , forall ee . Wrapper into (T'TT'I (tt e) t ee)
 , forall ee . Wrapper into (TT'T'I (tt e) t ee)
 , forall ee . Wrapper into (T'TT'I t t ee)
 , forall ee . Wrapper into (T'TT'I (T'TTT'TT'I (ttt e) (tt e) t) t ee)
 ) => Mapping Straight Straight into into
  (T'TTT'TT'I (ttt e) (tt e) t `T'TT'I` t)
  (T'TTT'TT'I (ttt e) (tt e) t) where
 mapping = rewrap / \from -> rewrap /
  map @Straight @Straight @into @into @(ttt e)
   (component @Straight @into @into @(t `T'TT'I` t) @t `compose` wrap @into
    `compose` map @Straight @Straight @into @into @t
     (wrapped (map @Straight @Straight @into @into @(tt e `T'TT'I` t) @(tt e `TT'T'I` t) from))
    )
  `compose` unwrap @into

-- 1. ttt (tttt (t (tt (tttt _))))
-- 2. ttt (tttt (t (tttt (tt _))))
-- 3. ttt (tttt (tttt (t (tt _))))
-- 4. ttt (tttt (t (tt _)))
instance
 ( Covariant Functor into into t
 , Covariant Endo Semi Functor into ttt
 , Covariant Endo Semi Functor into tttt
 , Mapping Straight Straight into into (tttt `T'TT'I` tttt) tttt
 , Mapping Straight Straight into into (tt `T'TT'I` tttt) (tt `TT'T'I` tttt)
 , Mapping Straight Straight into into (t `T'TT'I` tttt) (t `TT'T'I` tttt)
 , forall ee . Wrapper into (T'TT'I tt tttt ee)
 , forall ee . Wrapper into (TT'T'I tt tttt ee)
 , forall ee . Wrapper into (T'TT'I t tttt ee)
 , forall ee . Wrapper into (TT'T'I t tttt ee)
 , forall ee . Wrapper into (T'TT'I tttt tttt ee)
 , forall ee . Wrapper into (T'TT'I (T'TTT'TT'I ttt tt (TT'T'I t tttt)) tttt ee)
 , forall ee . Wrapper into (T'TTT'TT'I ttt tt (TT'T'I t tttt) ee)
 ) => Mapping Straight Straight into into
  (T'TTT'TT'I ttt tt (TT'T'I t tttt) `T'TT'I` tttt)
  (T'TTT'TT'I ttt tt (TT'T'I t tttt)) where
 mapping = rewrap / \from -> rewrap /
  map @Straight @Straight @into @into @ttt @ttt
   (wrap @into @(TT'T'I _ _ _)
    `compose` component @Straight @into @into @(tttt `T'TT'I` tttt) @tttt
    `compose` wrap @into @(T'TT'I tttt tttt _)
    `compose` map @Straight @Straight @into @into @tttt
     (wrapped (component @Straight @into @into @(t `T'TT'I` tttt) @(t `TT'T'I` tttt)))
    `compose` unwrap @into @(TT'T'I t tttt _)
    `compose` map @Straight @Straight @into @into @(TT'T'I t tttt) @(TT'T'I t tttt)
     (wrapped (map @Straight @Straight @into @into @(tt `T'TT'I` tttt) @(tt `TT'T'I` tttt) from))
   )
  `compose` unwrap @into

-- 1. ttt (tttt (t (tt (t _))))
-- 2. ttt (tttt (t (t (tt _))))
-- 4. ttt (tttt (t (tt _)))
instance
 ( Covariant Functor into into t
 , Covariant Endo Semi Functor into ttt
 , Covariant Endo Semi Functor into tttt
 , Component Natural into into (t `T'TT'I` t) t
 , Component Natural into into (tt `T'TT'I` t) (tt `TT'T'I` t)
 , Component Natural into into (t `T'TT'I` tttt) (t `TT'T'I` tttt)
 , forall ee . Wrapper into (T'TT'I tt t ee)
 , forall ee . Wrapper into (TT'T'I tt t ee)
 , forall ee . Wrapper into (T'TT'I t tttt ee)
 , forall ee . Wrapper into (TT'T'I t tttt ee)
 , forall ee . Wrapper into (T'TT'I t t ee)
 , forall ee . Wrapper into (T'TT'I (T'TTT'TT'I ttt tt (TT'T'I t tttt)) t ee)
 , forall ee . Wrapper into (T'TTT'TT'I ttt tt (TT'T'I t tttt) ee)
 ) => Mapping Straight Straight into into
  (T'TTT'TT'I ttt tt (TT'T'I t tttt) `T'TT'I` t)
  (T'TTT'TT'I ttt tt (TT'T'I t tttt)) where
 mapping = rewrap / \from -> rewrap /
  map @Straight @Straight @into @into @ttt @ttt
   (wrap @into @(TT'T'I _ _ _)
    `compose` map @Straight @Straight @into @into @tttt
     (component @Straight @into @into @(t `T'TT'I` t) @t `compose` wrap @into @(T'TT'I _ _ _))
    `compose` unwrap @into @(TT'T'I t tttt _)
    `compose` map @Straight @Straight @into @into @(TT'T'I t tttt) @(TT'T'I t tttt)
     (wrapped (map @Straight @Straight @into @into @(tt `T'TT'I` t) @(tt `TT'T'I` t) from))
   )
  `compose` unwrap @into

instance
 ( Monoidal Straight Functor AR LM LM t
 , Covariant Endo Semi Functor AR tt
 ) => Mapping Straight Straight AR AR tt (tt `TT'T'I` t) where
 mapping = rewrap / \from -> wrap @AR @((tt `TT'T'I` t) _)
  `compose` component @Straight @AR @AR @(U_I_II AR Unit) @t
  `compose` component @Straight @AR @AR @Identity @(U_I_II AR Unit)
  `compose` wrap @AR
  `compose` map @Straight @Straight @AR @AR @tt @tt from

instance Mapping Straight Straight AR AR (U_II_I LM e `T'TT'I` tt) (U_II_I LM e `TT'T'I` tt) =>
 Mapping Straight Straight AR AR
  (U_I_II (U_I_UU_II_I AR LM) e `T'TT'I` tt)
  (T'TTT'TT'I (U_I_II AR e) (U_II_I LM e) tt) where
 mapping = rewrap / \from (T'TT'I (U_I_II (U_I_UU_II_I x))) ->
  T'TTT'TT'I `compose` U_I_II / \old -> wrapped @AR
   `li` map @Straight @Straight @AR @AR @(U_II_I LM e `T'TT'I` tt) @(U_II_I LM e `TT'T'I` tt) from
   `li` U_II_I (x old)

instance Monoidal Straight Functor AR LM LM t =>
 Mapping Straight Straight AR AR (U_I_II AR Unit) (U_I_II AR e `T'TT'I` t) where
 mapping = rewrap / \from -> rewrap / \f -> Straight / \_ -> yu enter `compose` from `li` f Unit

instance
 ( Covariant Yoneda into into Identity
 , Covariant Endo Semi Functor into (U_I_II into e)
 , Adjoint Functor into into (U_II_I t e) (U_I_II tt e)
 , forall ee . Wrapper into (U_II_I t e ee)
 , forall ee . Wrapper into (U_I_II into Unit ee)
 , forall ee . Wrapper into (U_I_II tt e (t ee e))
 , forall ee . Wrapper into (U_I_UU_II_I tt t e ee)
 , forall ee . Wrapper into (U_I_II (U_I_UU_II_I tt t) e ee)
 , forall ee . Wrapper into (T'TT'I (U_I_II tt e) (U_II_I t e) ee)
 , forall ee . Wrapper into (T'TT'I (U_II_I t e) (U_I_II tt e) ee)
 , forall ee . Wrapper into (Identity ee)
 ) => Mapping Straight Straight into into (U_I_II into Unit) (U_I_II (U_I_UU_II_I tt t) e) where
 mapping = rewrap `identity` \from -> rewrap
  / wrap @into @(U_I_UU_II_I _ _ _ _)
   `compose` hd @into @into identity
   `compose` from
   `compose` yi Unit

instance
 ( Covariant Yoneda into into Identity
 , Covariant Monoidal Functor into tt tt t
 , Covariant Endo Semi Functor into t
 , Adjoint Functor into into (U_II_I tt e) (U_I_II ttt e)
 , Component Natural into into Identity (U_I_II into Unit)
 , Component Natural into into (U_I_II into Unit) t
 , forall ee . Wrapper into (Identity ee)
 , forall ee . Wrapper into (U_I_II into Unit ee)
 , forall ee . Wrapper into (T'TT'I (U_I_II ttt e) (U_II_I tt e) ee)
 , forall ee . Wrapper into (T'TTT'TT'I (U_I_II ttt e) (U_II_I tt e) t ee)
 ) => Mapping Straight Straight into into (U_I_II into Unit) (T'TTT'TT'I (U_I_II ttt e) (U_II_I tt e) t) where
 mapping = rewrap / \from -> rewrap
  / fj @into @into
   (component @Straight @into @into @(U_I_II into Unit) @t
    `compose` component @Straight @into @into @Identity @(U_I_II into Unit)
    `compose` wrap @into
   ) `compose` from `compose` yi Unit

-- TODO: desugar `fj` and move this instance to `Instances` module
instance
 ( Covariant Endo Semi Functor into t
 , Adjoint Functor into into (U_II_I tt e) (U_I_II ttt e)
 , Component Natural from into (U_II_I tt e `T'TT'I` t) (U_II_I tt e `TT'T'I` t)
 , forall ee . Wrapper into (Identity ee)
 , forall ee . Wrapper into (T'TT'I (U_II_I tt e) (U_I_II ttt e) ee)
 , forall ee . Wrapper into (T'TT'I (U_I_II ttt e) (U_II_I tt e) ee)
 , forall ee . Wrapper into (T'TT'I (U_II_I tt e) t ee)
 , forall ee . Wrapper into (TT'T'I (U_II_I tt e) t ee)
 , forall ee . Wrapper into (T'TTT'TT'I (U_I_II ttt e) (U_II_I tt e) t ee)
 ) => Mapping Straight Straight from into t (T'TTT'TT'I (U_I_II ttt e) (U_II_I tt e) t) where
 mapping = rewrap / \from -> wrap @into @(T'TTT'TT'I _ _ _ _)
  `compose` fj (wrapped (map @Straight @Straight @from @into @(U_II_I tt e `T'TT'I` t) @(U_II_I tt e `TT'T'I` t) from))

instance
 ( Covariant Semi Functor from into t
 , Adjoint Functor into into (U_II_I tt e) (U_I_II ttt e)
 , Component Natural from into (U_II_I tt e `T'TT'I` TT'T'I t tttt) (U_II_I tt e `TT'T'I` TT'T'I t tttt)
 , Component Natural from into (U_II_I tt e `T'TT'I` TT'T'I t tttt) (U_II_I tt e `TT'T'I` TT'T'I t tttt)
 , Component Natural from into t (TT'T'I t tttt)
 , forall ee . Wrapper into (Identity ee)
 , forall ee . Wrapper into (T'TT'I (U_II_I tt e) (U_I_II ttt e) ee)
 , forall ee . Wrapper into (T'TT'I (U_I_II ttt e) (U_II_I tt e) ee)
 , forall ee . Wrapper into (TT'T'I (U_II_I tt e) (TT'T'I t tttt) ee)
 , forall ee . Wrapper into (T'TT'I (U_II_I tt e) (TT'T'I t tttt) ee)
 , forall ee . Wrapper into (TT'T'I (U_II_I tt e) tttt ee)
 , forall ee . Wrapper into (TT'T'I t tttt ee)
 , forall ee . Wrapper into (T'TTT'TT'I (U_I_II ttt e) (U_II_I tt e) (TT'T'I t tttt) ee)
 ) => Mapping Straight Straight from into t (T'TTT'TT'I (U_I_II ttt e) (U_II_I tt e) (TT'T'I t tttt)) where
 mapping = rewrap / \from -> wrap @into @(T'TTT'TT'I _ _ _ _)
  `compose` fj (wrapped (map @Straight @Straight @from @into @(U_II_I tt e `T'TT'I` TT'T'I t tttt) @(U_II_I tt e `TT'T'I` TT'T'I t tttt) from))
  `compose` component @Straight @from @into @t @(t `TT'T'I` tttt)

instance
 ( Covariant Semi Functor from into t
 , Adjoint Functor into into (U_II_I tt e) (U_I_II ttt e)
 , Component Natural from into (U_II_I tt e `T'TT'I` TT'T'I tttt t) (U_II_I tt e `TT'T'I` TT'T'I tttt t)
 , Component Natural from into (U_II_I tt e `T'TT'I` TT'T'I tttt t) (U_II_I tt e `TT'T'I` TT'T'I tttt t)
 , Component Natural from into t (TT'T'I tttt t)
 , forall ee . Wrapper into (Identity ee)
 , forall ee . Wrapper into (T'TT'I (U_II_I tt e) (U_I_II ttt e) ee)
 , forall ee . Wrapper into (T'TT'I (U_I_II ttt e) (U_II_I tt e) ee)
 , forall ee . Wrapper into (TT'T'I (U_II_I tt e) (TT'T'I tttt t) ee)
 , forall ee . Wrapper into (T'TT'I (U_II_I tt e) (TT'T'I tttt t) ee)
 , forall ee . Wrapper into (TT'T'I (U_II_I tt e) tttt ee)
 , forall ee . Wrapper into (TT'T'I tttt t ee)
 , forall ee . Wrapper into (T'TTT'TT'I (U_I_II ttt e) (U_II_I tt e) (TT'T'I tttt t) ee)
 ) => Mapping Straight Straight from into t (T'TTT'TT'I (U_I_II ttt e) (U_II_I tt e) (TT'T'I tttt t)) where
 mapping = rewrap / \from -> wrap @into @(T'TTT'TT'I _ _ _ _)
  `compose` fj (wrapped (map @Straight @Straight @from @into @(U_II_I tt e `T'TT'I` TT'T'I tttt t) @(U_II_I tt e `TT'T'I` TT'T'I tttt t) from))
  `compose` component @Straight @from @into @t @(tttt `TT'T'I` t)

instance
 ( Covariant Semi Functor from AR t
 , forall e . Covariant Semi Functor into AR (U_I_II from e)
 ) => Mapping Straight Straight from AR t (UU_V_U_I_II_T_II Straight into AR t r) where
 mapping = rewrap / \from x -> UU_V_U_I_II_T_II (\(Straight e) -> fo @from (fio @into @AR e from) x)

instance
 ( Covariant Endo Semi Functor AR t
 , forall e . Covariant Endo Semi Functor AR (U_I_II AR e)
 ) => Mapping U_1_I Straight AR AR t (UU_V_U_I_II_T_II U_1_I AR AR t r) where
 mapping = rewrap / \_ x -> UU_V_U_I_II_T_II (\(U_1_I e) -> (\_ -> e Unit) `fo` x)

instance
 ( Contravariant Semi Functor from AR t
 , forall e . Contravariant Semi Functor into AR (Opposite from e)
 ) => Mapping Opposite Straight from AR t (UU_V_U_I_II_T_II Opposite into AR t r) where
 mapping = rewrap / \from x -> UU_V_U_I_II_T_II (\(Opposite e) -> fa @from (fai @into @AR e from) x)

instance Mapping Straight Straight AR AR (U_I_II ML e `T'TT'I` U_I_II ML e) (U_I_II ML e) where
 mapping = rewrap / \from -> \case
  T'TT'I (Straight (That (Straight (That x)))) -> Straight (That / from x)
  T'TT'I (Straight (That (Straight (This e)))) -> Straight (This e)
  T'TT'I (Straight (This e)) -> Straight (This e)

instance Covariant Monoidal Functor AR LM LM t =>
 Mapping Straight Straight AR AR (U_I_II ML e `T'TT'I` t) (U_I_II ML e `TT'T'I` t) where
 mapping = rewrap / \from -> rewrap / \case
  Straight (This e) -> yu enter (Straight `li` This e)
  Straight (That x) -> x `yo` from `ho` That  `ho` Straight

instance
 ( Monoidal Straight Functor AR LM LM t
 , Mapping Straight Straight AR AR (T'TT'I t t) t
 , Mapping Straight Straight AR AR Identity (U_I_II AR e)
 ) => Mapping Straight Straight AR AR (t `T'TT'I` T_'_I (U_I_II ML Unit Unit) (U_I_II ML e)) t where
 mapping = rewrap / \from -> \(T'TT'I x) ->
  x `yok'he'he` constant @AR (map @Straight @Straight from (T'TT'I x)) `la` yu (enter @t) `ha` from

instance
 ( Mapping U_I_II U_I_II AR AR t t
 , Mapping U_I_II U_I_II AR AR (T'TT'I t t) t
 ) => Mapping Straight Straight AR AR (t `T'TT'I` T_'_I (U_I_I LM Unit) Identity) t where
 mapping = rewrap / \from -> \(T'TT'I x) ->
  x `yok'he'he` constant @AR (map @Straight @Straight @_ @_ @_ @t from (T'TT'I x))

-- TODO: generalize using adjunctions
instance Mapping Straight Straight AR AR
  (Day Straight AR LM LM
   (U_I_II (U_I_UU_II_I AR LM) e)
   (U_I_II (U_I_UU_II_I AR LM) e) ee eee)
  (U_I_II (U_I_UU_II_I AR LM) e) where
 mapping = rewrap / \from -> rewrap / \case
  These (These ee eee) (U_I_II f) -> U_I_UU_II_I `li` \old ->
   let These x new = ee `he'he` old in
   let These y upd  = eee `he'he` new in
   These (from `li` f (These x y)) upd

instance
 ( Component Natural AR AR (t `T'TT'I` t) t
 , Covariant Yoneda AR AR t
 ) => Mapping Straight Straight AR AR
  (Day Straight AR LM LM
   (T'TTT'TT'I (U_I_II AR e) (U_II_I LM e) t)
   (T'TTT'TT'I (U_I_II AR e) (U_II_I LM e) t)
   ee eee)
  (T'TTT'TT'I (U_I_II AR e) (U_II_I LM e) t) where
 mapping = rewrap / \from -> rewrap / \case
  These (These (T'TTT'TT'I (U_I_II x)) (T'TTT'TT'I (U_I_II y))) (U_I_II f) ->
   U_I_II / \old -> x old `yok` \(U_II_I (These e btw)) ->
    from `compose` f `compose` (e `lu`) `fo'fo` y btw

instance
 ( Component Natural AR AR (t `T'TT'I` t) t
 , Monoidal Straight Functor AR LM LM t
 ) => Mapping Straight Straight AR AR
  (Day Straight AR LM LM (T'TT'I (U_I_II AR a) t) (U_I_II AR a `T'TT'I` t) ee eee)
  (T'TT'I (U_I_II AR a) t) where
 mapping = rewrap / \from -> rewrap / \case
  These (These (T'TT'I (Straight f)) (T'TT'I (Straight g))) (Straight h) -> Straight / \x ->
   yp (These (f x) (g x)) `yo` h `ho` from

instance Monoidal Straight Functor AR LM LM t =>
 Mapping Straight Straight AR AR (U_I_II AR Unit) (TT'T'I (U_I_II ML e) t) where
 mapping = rewrap / \from (Straight f) -> TT'T'I (yu enter (U_I_II (That (from (f Unit)))))

-- TODO: Finish, it's for Halts transformer
instance Monoidal Straight Functor AR LM LM t =>
 Mapping Straight Straight AR AR
  (Day Straight AR LM LM (TT'T'I (U_I_II ML e) t) (TT'T'I (U_I_II ML e) t) ee eee)
  (TT'T'I (U_I_II ML e) t) where
 mapping = rewrap / \from -> rewrap / \case

-- 1. t (tt (t (tt _)))
-- 2. t (t (tt (tt _)))
-- 3. t (t (tt _))
-- 4. t (tt _)
instance
 ( Covariant Endo Semi Functor into t
 , Covariant Endo Semi Functor into tt
 , Component Natural into into (t `T'TT'I` t) t
 , Component Natural into into (tt `T'TT'I` tt) tt
 , Component Natural into into (tt `T'TT'I` t) (tt `TT'T'I` t)
 , forall e . Wrapper into (((tt `T'TT'I` t) `T'TT'I` (tt `TT'T'I` t)) e)
 , forall e . Wrapper into (((tt `TT'T'I` t) `T'TT'I` (tt `TT'T'I` t)) e)
 , forall e . Wrapper into ((tt `T'TT'I` t) ((tt `TT'T'I` t) e))
 , forall e . Wrapper into ((t `T'TT'I` t) e)
 , forall e . Wrapper into ((tt `TT'T'I` t) e)
 , forall e . Wrapper into ((tt `T'TT'I` t) e)
 , forall e . Wrapper into ((tt `T'TT'I` tt) e)
 ) => Mapping Straight Straight into into (TT'T'I tt t `T'TT'I` TT'T'I tt t) (TT'T'I tt t) where
 mapping = rewrap / \from -> rewrap
  / component @Straight @into @into @(t `T'TT'I` t) @t `compose` wrap @into
  `compose` map @Straight @Straight @into @into @t @t
  (map @Straight @Straight @into @into @t @t
    (map @Straight @Straight @into @into @(tt `T'TT'I` tt) @tt from `compose` wrap @into)
    `compose` wrapped (component @Straight @into @into @(tt `T'TT'I` t) @(tt `TT'T'I` t))
    `compose` map @Straight @Straight @into @into @tt @tt unwrap
   ) `compose` unwrap @into @(TT'T'I _ _ _)

-- TODO: generalize with limits
instance Covariant Monoidal Functor AR LM LM t =>
 Mapping Straight Straight AR AR (U_I_II LM e `T'TT'I` t) (U_I_II LM e `TT'T'I` t) where
 mapping = rewrap / \from -> rewrap / \case
  U_I_II (These e x) -> x `yo` from `ho` These e `ho` U_I_II

-- TODO: generalize with limits
instance Covariant Monoidal Functor AR LM LM t =>
 Mapping Straight Straight AR AR (U_II_I LM e `T'TT'I` t) (U_II_I LM e `TT'T'I` t) where
 mapping = rewrap / \from -> rewrap / \case
  U_II_I (These x e) -> x `yo` from `ho` (`lu` e) `ho` U_II_I

instance Covariant Endo Semi Functor AR t =>
 Mapping Straight Straight AR AR (t `T'TT'I` U_I_II AR e) (t `TT'T'I` U_I_II AR e) where
 mapping = rewrap / \from -> rewrap / \x ->
  Straight / \e -> x `yo` (from `compose` (`li` e) `compose` unwrap)

-- TODO: generalize
-- We need this instance to make `yok'yoklKL` work
instance {-# OVERLAPS #-} Component Natural AR AR (T'TT'I t tt) t =>
 Mapping Straight Straight AR AR (T'TT'I t (T_'_I l tt)) t where
 mapping = rewrap / \from ->
  map @Straight @Straight @AR @AR @(T'TT'I t tt) @t from `compose` rewrap @_ @AR (fo @AR unwrap)

instance Setoid AR Unit where
 equality _ = That Unit

instance (Setoid AR e, Setoid AR ee) => Setoid AR (e `ML` ee) where
 equality (These (This x) (This xx)) = equality (x `lu` xx) `yoi` (`yio` This) `ho` (`yoi` This) `yio` This
 equality (These (That x) (That xx)) = equality (x `lu` xx) `yoi` (`yio` That) `ho` (`yoi` That) `yio` That
 equality (These x xx) = This (These x xx)

instance (Setoid AR e, Setoid AR ee) => Setoid AR (e `LM` ee) where
 equality (These (These x xx) (These xxx xxxx)) = case equality (x `lu` xxx) `lu`equality (xx `lu` xxxx) of
  These (That x') (That xx') -> That (These x' xx')
  These _ _ -> This ((x `lu` xx) `lu` (xxx `lu` xxxx))
