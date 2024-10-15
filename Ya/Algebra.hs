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
 , Component Natural AR AR (t `T_TT_I` tt) (t `TT_T_I` tt)
 , Component Natural AR AR (Labeled l (R_U_I_T_I LM t) `T_TT_I` tt) (Labeled l (R_U_I_T_I LM t) `TT_T_I` tt)
 ) => Mapping Straight Straight AR AR
  (Labeled l (t `T_TT_I` R_U_I_T_I LM t) `T_TT_I` tt)
  (Labeled l (t `T_TT_I` R_U_I_T_I LM t) `TT_T_I` tt) where
 mapping = rwr / \from -> rwr / \x -> unwrap (unwrap x)
   `yo` wrapped (map @Straight @Straight @AR @AR
            @(Labeled l (R_U_I_T_I LM t) `T_TT_I` tt)
            @(Labeled l (R_U_I_T_I LM t) `TT_T_I` tt) from)
          `ha` wrap @AR @(Labeled l (R_U_I_T_I LM t) (tt _))
   `yi` wrapped (map @Straight @Straight @AR @AR @(t `T_TT_I` tt) @(t `TT_T_I` tt) unwrap)
   `yo` wrap @AR @(Labeled l _ _)
   `ha` wrap @AR @(T_TT_I t (R_U_I_T_I LM t) _)

-- TODO: reduce a number of transformations here
instance
 ( Covariant Endo Semi Functor AR t
 , Covariant Endo Semi Functor AR tt
 , Covariant Monoidal Functor AR LM LM tt
 , Transformation Straight Functor AR AR (T_TT_I t tt) (TT_T_I t tt)
 ) => Mapping Straight Straight AR AR
  (Labeled (U_I_II AR () ()) (R_U_I_T_I LM t) `T_TT_I` tt)
  (Labeled (U_I_II AR () ()) (R_U_I_T_I LM t) `TT_T_I` tt) where
 mapping = rwr / \from -> rwr /
  \(T_'_I (R_U_I_T_I (Recursive (U_I_T_II (These x xs))))) ->
    x `yo` from `lu`
     (wrapped (map @Straight @Straight @AR @_ @(t `T_TT_I` tt) @(t `TT_T_I` tt) (unwrap @AR @(R_U_I_T_I _ _ _) `ha` unwrap @AR @(Labeled _ _ _)))
      (xs `yo` wrap @AR @(R_U_I_T_I _ _ _)
       `ho` wrap @AR @(Labeled (U_I_II AR () ()) _ _)
       `ho` wrapped (map @Straight @Straight @AR @AR
         @(Labeled (U_I_II AR () ()) (R_U_I_T_I LM t) `T_TT_I` tt)
         @(Labeled (U_I_II AR () ()) (R_U_I_T_I LM t) `TT_T_I` tt)
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
 , Transformation Straight Functor AR AR (t `T_TT_I` tt) (t `TT_T_I` tt)
 ) => Mapping Straight Straight AR AR
  (Labeled (U_II_I AR () ()) (R_U_I_T_I LM t) `T_TT_I` tt)
  (Labeled (U_II_I AR () ()) (R_U_I_T_I LM t) `TT_T_I` tt) where
 mapping = rwr / \from -> rwr
  / \(T_'_I (R_U_I_T_I (Recursive (U_I_T_II (These x xs))))) ->
   (These
    `hoo'ho` wrap @AR @(U_I_T_II _ _ _ _)
    `ho` wrap @AR @(Recursive _)
    `ho` wrap @AR @(R_U_I_T_I _ _ _)
    `ho` wrap @AR @(Labeled _ _ _))
   `fo` (x `yo` from)
   `fc` wrapped (map @Straight @Straight @AR @_ @(t `T_TT_I` tt) @(t `TT_T_I` tt)
         (unwrap @AR @(R_U_I_T_I _ _ _) `ha` unwrap @AR @(Labeled _ _ _))
        )
    (xs
     `yo` wrap @AR @(R_U_I_T_I _ _ _)
     `ho` wrap @AR @(Labeled _ _ _)
     `ho` wrapped (map @Straight @Straight @AR @AR
        @(Labeled (U_II_I AR () ()) (R_U_I_T_I LM t) `T_TT_I` tt)
        @(Labeled (U_II_I AR () ()) (R_U_I_T_I LM t) `TT_T_I` tt)
        from)
    )

-- TODO: try to simplify
instance
 Mapping Straight Straight AR AR
  (Day Straight AR LM LM t t (Recursive (U_I_T_II t LM e)) (Recursive (U_I_T_II t LM ee))) t =>
 Mapping Straight Straight AR AR
  (Day Straight AR LM LM (R_U_I_T_I LM t) (R_U_I_T_I LM t) e ee) (R_U_I_T_I LM t) where
 mapping = rwr / \from -> rwr / \case
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
 Mapping Straight Straight AR AR (Straight AR ()) (R_U_I_T_I LM t) where
 mapping = rwr / \from (Straight f) ->
  R_U_I_T_I `compose` Recursive `compose` U_I_T_II
   / These (from / f ()) (empty @t `yo` initial @AR)

instance
 ( Mapping Straight Straight AR AR (Day Straight AR LM LM t t (R_U_I_T_I LM t e) (R_U_I_T_I LM t ee)) t
 , Mapping Straight Straight AR AR (Day Straight AR LM LM t t (Recursive (U_I_T_II t LM e)) (Recursive (U_I_T_II t LM ee))) t
 ) => Mapping Straight Straight AR AR (Day Straight AR LM LM (t `T_TT_I` R_U_I_T_I LM t) (t `T_TT_I` R_U_I_T_I LM t) e ee) (t `T_TT_I` R_U_I_T_I LM t) where
 mapping = rwr / \from -> rwr / \case
  These (These (T_TT_I e) (T_TT_I ee)) (Straight f) ->
    day @Straight @AR @t @LM @LM identity
     (day @Straight @AR @(R_U_I_T_I LM t) @LM @LM identity (from `compose` f))
      (These e ee)

instance
 ( Monoidal Straight Functor AR LM LM t
 , Monoidal Straight Functor AR LM LM (R_U_I_T_I LM tt)
 ) => Mapping Straight Straight AR AR (Straight AR ()) (t `T_TT_I` R_U_I_T_I LM tt) where
 mapping = rwr / \from (Straight f) -> T_TT_I /
  enter @t `yu` (enter @(R_U_I_T_I LM tt) `yo` from `compose` f)

-- TODO: try to avoid mapping twice datastructure here
instance
 ( Covariant Endo Semi Functor AR t
 , Mapping Straight Straight AR AR (Day Straight AR LM MLM t t (R_U_I_T_I LM t e) (R_U_I_T_I LM t ee)) t
 , Mapping Straight Straight AR AR (Day Straight AR LM MLM t t (Recursive (U_I_T_II t LM e)) (Recursive (U_I_T_II t LM ee))) t
 ) => Mapping Straight Straight AR AR (Day Straight AR LM MLM (t `T_TT_I` R_U_I_T_I LM t) (t `T_TT_I` R_U_I_T_I LM t) e ee) (t `T_TT_I` R_U_I_T_I LM t) where
 mapping = rwr / \from -> rwr / \case
  These (These (T_TT_I e) (T_TT_I ee)) (Straight f) ->
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
 mapping = rwr / \from -> rwr / \case
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
 Mapping Straight Straight AR AR (Straight AR Void) (t `T_TT_I` R_U_I_T_I LM tt) where
 mapping = rwr / \_ _ -> T_TT_I (empty @t `yo` initial @AR)

-- TODO: generalize this instance
instance Mapping Opposite Straight (U_I_UU_II_U_II_I AR LM )AR
 (U_II_I (U_I_UU_II_I AR LM) e)
 (U_II_I (U_I_UU_II_I AR LM) e) where
 mapping = rwr / \(U_I_UU_II_U_II_I from) ->
  rwr `compose` rwr `identity` \state old ->
   let (These new f) = from old in f `fio` state new

instance Mapping Straight Straight (U_I_UU_II_U_II_I AR LM) (U_I_UU_II_U_II_I AR LM) (U_I_II LM e) (U_I_II LM e) where
 mapping = rwr / \(U_I_UU_II_U_II_I from) -> U_I_UU_II_U_II_I / \(U_I_II (These e x)) ->
   let s = from x in U_I_II (These e (this s)) `lu` fo (that s)

instance Mapping Straight Straight (U_I_UU_II_U_II_I AR LM) (U_I_UU_II_U_II_I AR LM) (U_II_I LM e) (U_II_I LM e) where
 mapping = rwr / \(U_I_UU_II_U_II_I from) -> U_I_UU_II_U_II_I / \(U_II_I (These x e)) ->
   let s = from x in U_II_I (These (this s) e) `lu` fo (that s)

-- TODO: I'm not really sure about this instance... it could easily lead to an error!
instance Mapping Straight Straight (U_I_UU_II_U_II_I AR LM) (U_I_UU_II_U_II_I AR LM) Identity (U_I_I LM) where
 mapping = rwr / \(U_I_UU_II_U_II_I from) -> U_I_UU_II_U_II_I / \(Identity x) ->
   let s = from x in U_I_I (this s `lu`this s) `lu` (\(U_I_I (These _ _)) -> Identity (that s (this s)))

instance Mapping Straight Straight (U_I_UU_II_U_II_I AR LM) (U_I_UU_II_U_II_I AR LM) (U_I_II LM e) Identity where
 mapping = rwr / \(U_I_UU_II_U_II_I from) -> U_I_UU_II_U_II_I / \(U_I_II (These e x)) ->
   let s = from x in Identity (this s) `lu` (U_I_II `compose` (e `lu`) `compose` that s `compose` unwrap)

instance Mapping Straight Straight (U_I_UU_II_U_II_I AR LM) (U_I_UU_II_U_II_I AR LM) (U_II_I LM e) Identity where
 mapping = rwr / \(U_I_UU_II_U_II_I from) -> U_I_UU_II_U_II_I / \(U_II_I (These x e)) ->
   let s = from x in Identity (this s) `lu` (U_II_I `compose` (`lu` e) `compose` that s `compose` unwrap)

-- TODO: I should alse test how attributes behave on sums

instance Mapping Straight Straight AR AR
 (T_TT_I
  (U_I_II (U_I_UU_II_I AR LM) e)
  (U_I_II (U_I_UU_II_I AR LM) e)
 )
 (U_I_II (U_I_UU_II_I AR LM) e) where
 mapping = rwr / \from ->
  \(T_TT_I (U_I_II (U_I_UU_II_I state))) ->
   U_I_II `compose` U_I_UU_II_I `identity` \old ->
    let These (U_I_II (U_I_UU_II_I f)) s = state old in
     from `foi` f s

instance Covariant Endo Semi Functor AR t
 => Mapping Straight Straight AR AR t (T_TTT_TT_I (U_I_II AR e) (U_II_I LM e) t) where
 mapping = rwr / \from x -> T_TTT_TT_I `compose` Straight `li` \state ->
  x `yo` from `ho` (`lu` state) `ho` U_II_I

instance (Covariant Monoidal Functor AR LM LM t, e ~ ee)
 => Mapping Straight Straight AR AR
  (U_I_II (U_I_UU_II_I AR LM) ee)
  (T_TTT_TT_I (U_I_II ARR e) (U_II_I LM e) t) where
 mapping = rwr / \from (U_I_II (U_I_UU_II_I x)) ->
  wrap @_ @(T_TTT_TT_I _ _ _ _)
  `compose` wrap @_ @(U_I_II _ _ _)
  `identity` (yu enter
   `compose` map @Straight @Straight from
   `compose` wrap @_ @(U_II_I _ _ _)
   `compose` x)

-- x: ee -> Object Straight AR a ee

instance  {-# OVERLAPPABLE #-} Component Natural ARR AR (T_TT_I t tt) t => Mapping Straight Straight AR AR
 (T_TT_I (Straight AR e `T_TT_I` t) tt) (Straight AR e `T_TT_I` t) where
 mapping = rwr / \from -> rwr `compose` rwr /
  \(Straight f) e -> map @Straight @Straight @AR @AR @(t `T_TT_I` tt) @t from (T_TT_I (f e))

instance {-# OVERLAPS #-} Covariant Endo Semi Functor AR t => Mapping Straight Straight AR AR
 (T_TT_I (Straight AR e `T_TT_I` t) (Straight AR e)) (Straight AR e `T_TT_I` t) where
 mapping = rwr / \from -> rwr `compose` rwr /
  \(Straight f) e -> f e `yo` unwrap @AR `ho` (`li` e) `ho` from

-- NOTE: this version allow different type of states, but it requires providing types to make it compile
instance
 ( Covariant Endo Semi Functor AR t
 , Transformation Natural Functor AR AR (T_TT_I t t) t
 ) => Mapping Straight Straight AR AR
 (T_TT_I
  (T_TTT_TT_I (U_I_II AR old) (U_II_I LM btw) t)
  (T_TTT_TT_I (U_I_II AR btw) (U_II_I LM new) t)
 )
 (T_TTT_TT_I (U_I_II AR old) (U_II_I LM new) t) where
 mapping = rwr / \from (T_TT_I (T_TTT_TT_I (U_I_II x))) -> 
  wrap @_ @(T_TTT_TT_I _ _ _ _) `compose` wrap @_ @(U_I_II _ _ _)
  `li` \old -> x old `yok` \(U_II_I (These (T_TTT_TT_I (U_I_II f)) btw))
   -> f btw `yo'yo` from

-- TODO: try to use adjunctions here
instance
 ( Covariant Monoidal Functor AR LM LM tt
 , Transformation Natural Functor AR AR (T_TT_I tt tt) tt
 , e ~ ee
 ) => Mapping Straight Straight AR AR
 (T_TT_I
  (T_TTT_TT_I (U_I_II AR e) (U_II_I LM e) tt)
  (U_I_II (U_I_UU_II_I AR LM) ee)
 )
 (T_TTT_TT_I (U_I_II AR e) (U_II_I LM e) tt) where
  mapping = rwr / \from (T_TT_I (T_TTT_TT_I (U_I_II x))) ->
   wrap @_ @(T_TTT_TT_I _ _ _ _) `compose` wrap @_ @(U_I_II _ _ _)
    `li` \old -> x old `yok` \(U_II_I (These (U_I_II (U_I_UU_II_I f)) btw))
      -> yu (enter @tt) / U_II_I (f btw) `yo` from

instance
 ( Covariant Endo Semi Functor AR t
 , Mapping Straight Straight AR AR (t `T_TT_I` t) t
 ) => Mapping Straight Straight AR AR
  (T_TT_I (T_TTT_TT_I (U_I_II AR e) (U_II_I LM e) t) t)
  (T_TTT_TT_I (U_I_II AR e) (U_II_I LM e) t) where
 mapping = rwr / \from (T_TT_I (T_TTT_TT_I (Straight f))) -> T_TTT_TT_I `compose` U_I_II / \old ->
  component @Straight @AR @AR @(t `T_TT_I` t) @t
   (T_TT_I (f old `yo` (\(U_II_I (These y x)) -> y `yo` U_II_I `ha` (`lu` x) `ha` from)))

instance Mapping Straight Straight AR AR (U_II_I LM e `T_TT_I` tt) (U_II_I LM e `TT_T_I` tt) =>
 Mapping Straight Straight AR AR
  (U_I_II (U_I_UU_II_I AR LM) e `T_TT_I` tt)
  (T_TTT_TT_I (U_I_II AR e) (U_II_I LM e) tt) where
 mapping = rwr / \from (T_TT_I (U_I_II (U_I_UU_II_I x))) ->
  T_TTT_TT_I `compose` U_I_II / \old -> wrapped @AR
   `li` map @Straight @Straight @AR @AR @(U_II_I LM e `T_TT_I` tt) @(U_II_I LM e `TT_T_I` tt) from
   `li` U_II_I (x old)

instance Monoidal Straight Functor AR LM LM t =>
 Mapping Straight Straight AR AR (U_I_II AR ()) (U_I_II AR e `T_TT_I` t) where
 mapping = rwr / \from -> rwr / \f -> Straight / \_ -> yu enter `compose` from `li` f ()

instance Mapping Straight Straight AR AR (U_I_II AR ()) (U_I_II (U_I_UU_II_I AR LM) e) where
 mapping = rwr / \from -> rwr / \f -> U_I_UU_II_I `li` \e -> from `li` f () `lu` e

instance Monoidal Straight Functor AR LM LM t =>
 Mapping Straight Straight AR AR (U_I_II AR ()) (T_TTT_TT_I (U_I_II AR e) (U_II_I LM e) t) where
 mapping = rwr / \from (U_I_II f) -> T_TTT_TT_I `compose` U_I_II
  / \old -> yu enter `compose` U_II_I `compose` (`lu` old) `compose` from `li` f ()

instance
 ( Covariant Semi Functor from AR t
 , forall e . Covariant Semi Functor into AR (U_I_II from e)
 ) => Mapping Straight Straight from AR t (UU_V_U_I_II_T_II Straight into AR t r) where
 mapping = rwr / \from x -> UU_V_U_I_II_T_II (\(Straight e) -> fo @from (fio @into @AR e from) x)

instance
 ( Covariant Endo Semi Functor AR t
 , forall e . Covariant Endo Semi Functor AR (U_I_II AR e)
 ) => Mapping U_1_I Straight AR AR t (UU_V_U_I_II_T_II U_1_I AR AR t r) where
 mapping = rwr / \_ x -> UU_V_U_I_II_T_II (\(U_1_I e) -> (\_ -> e ()) `fo` x)

instance
 ( Contravariant Semi Functor from AR t
 , forall e . Contravariant Semi Functor into AR (Opposite from e)
 ) => Mapping Opposite Straight from AR t (UU_V_U_I_II_T_II Opposite into AR t r) where
 mapping = rwr / \from x -> UU_V_U_I_II_T_II (\(Opposite e) -> fa @from (fai @into @AR e from) x)

instance Mapping Straight Straight AR AR (U_I_II ML e `T_TT_I` U_I_II ML e) (U_I_II ML e) where
 mapping = rwr / \from -> \case
  T_TT_I (Straight (That (Straight (That x)))) -> Straight (That / from x)
  T_TT_I (Straight (That (Straight (This e)))) -> Straight (This e)
  T_TT_I (Straight (This e)) -> Straight (This e)

instance Covariant Monoidal Functor AR LM LM t =>
 Mapping Straight Straight AR AR (U_I_II ML e `T_TT_I` t) (U_I_II ML e `TT_T_I` t) where
 mapping = rwr / \from -> rwr / \case
  Straight (This e) -> yu enter (Straight `li` This e)
  Straight (That x) -> x `yo` from `ho` That  `ho` Straight

instance
 ( Monoidal Straight Functor AR LM LM t
 , Mapping Straight Straight AR AR (T_TT_I t t) t
 , Mapping Straight Straight AR AR Identity (U_I_II AR e)
 ) => Mapping Straight Straight AR AR (t `T_TT_I` T_'_I (U_I_II ML () ()) (U_I_II ML e)) t where
 mapping = rwr / \from -> \(T_TT_I x) ->
  x `yok'he'he` constant @AR (map @Straight @Straight from (T_TT_I x)) `la` yu (enter @t) `ha` from

instance
 ( Mapping U_I_II U_I_II AR AR t t
 , Mapping U_I_II U_I_II AR AR (T_TT_I t t) t
 ) => Mapping Straight Straight AR AR (t `T_TT_I` T_'_I (U_I_I LM ()) Identity) t where
 mapping = rwr / \from -> \(T_TT_I x) ->
  x `yok'he'he` constant @AR (map @Straight @Straight @_ @_ @_ @t from (T_TT_I x))

instance Mapping Straight Straight AR AR
  (Day Straight AR LM LM
   (U_I_II (U_I_UU_II_I AR LM) e)
   (U_I_II (U_I_UU_II_I AR LM) e) ee eee)
  (U_I_II (U_I_UU_II_I AR LM) e) where
 mapping = rwr / \from -> rwr / \case
  These (These ee eee) (Straight f) -> U_I_UU_II_I `li` \old ->
   let These x new = ee `he'he` old in
   let These y upd  = eee `he'he` new in
   These (from `li` f (These x y)) upd

instance
 ( Component Natural AR AR (t `T_TT_I` t) t
 , Covariant Yoneda AR AR t
 ) => Mapping Straight Straight AR AR
  (Day Straight AR LM LM
   (T_TTT_TT_I (U_I_II AR e) (U_II_I LM e) t)
   (T_TTT_TT_I (U_I_II AR e) (U_II_I LM e) t)
   ee eee)
  (T_TTT_TT_I (U_I_II AR e) (U_II_I LM e) t) where
 mapping = rwr / \from -> rwr / \case
  These (These (T_TTT_TT_I (U_I_II x)) (T_TTT_TT_I (U_I_II y))) (U_I_II f) ->
   U_I_II / \old -> x old `yok` \(U_II_I (These e btw)) ->
    from `compose` f `compose` (e `lu`) `fo'fo` y btw

instance
 ( Component Natural AR AR (t `T_TT_I` t) t
 , Monoidal Straight Functor AR LM LM t
 ) => Mapping Straight Straight AR AR
  (Day Straight AR LM LM (T_TT_I (U_I_II AR a) t) (U_I_II AR a `T_TT_I` t) ee eee)
  (T_TT_I (U_I_II AR a) t) where
 mapping = rwr / \from -> rwr / \case
  These (These (T_TT_I (Straight f)) (T_TT_I (Straight g))) (Straight h) -> Straight / \x ->
   yp (These (f x) (g x)) `yo` h `ho` from

instance Monoidal Straight Functor AR LM LM t =>
 Mapping Straight Straight AR AR (U_I_II AR Unit) (TT_T_I (U_I_II ML e) t) where
 mapping = rwr / \from (Straight f) -> TT_T_I (yu enter (U_I_II (That (from (f Unit)))))

-- TODO: Finish, it's for Halts transformer
instance Monoidal Straight Functor AR LM LM t =>
 Mapping Straight Straight AR AR
  (Day Straight AR LM LM (TT_T_I (U_I_II ML e) t) (TT_T_I (U_I_II ML e) t) ee eee)
  (TT_T_I (U_I_II ML e) t) where
 mapping = rwr / \from -> rwr / \case

-- TODO: Finish, it's for Halts transformer
instance
 Mapping Straight Straight AR AR
  (TT_T_I (U_I_II ML e) t `T_TT_I` TT_T_I (U_I_II ML e) t)
  (TT_T_I (U_I_II ML e) t) where
 mapping = rwr / \from -> rwr / \case

-- TODO: generalize with limits
instance Covariant Monoidal Functor AR LM LM t =>
 Mapping Straight Straight AR AR (U_I_II LM e `T_TT_I` t) (U_I_II LM e `TT_T_I` t) where
 mapping = rwr / \from -> rwr / \case
  Straight (These e x) -> x `yo` from `ho` These e `ho` Straight

instance Covariant Endo Semi Functor AR t =>
 Mapping Straight Straight AR AR (t `T_TT_I` U_I_II AR e) (t `TT_T_I` U_I_II AR e) where
 mapping = rwr / \from -> rwr / \x ->
  Straight / \e -> x `yo` (from `compose` (`li` e) `compose` unwrap)

-- TODO: generalize
-- We need this instance to make `yok'yoklKL` work
instance {-# OVERLAPS #-} Component Natural AR AR (T_TT_I t tt) t =>
 Mapping Straight Straight AR AR (T_TT_I t (T_'_I l tt)) t where
 mapping = rwr / \from ->
  map @Straight @Straight @AR @AR @(T_TT_I t tt) @t from `compose` rwr @_ @AR (fo @AR unwrap)

instance Setoid AR () where
 equality _ = That ()

instance (Setoid AR e, Setoid AR ee) => Setoid AR (e `ML` ee) where
 equality (These (This x) (This xx)) = equality (x `lu` xx) `yoi` (`yio` This) `ho` (`yoi` This) `yio` This
 equality (These (That x) (That xx)) = equality (x `lu` xx) `yoi` (`yio` That) `ho` (`yoi` That) `yio` That
 equality (These x xx) = This (These x xx)

instance (Setoid AR e, Setoid AR ee) => Setoid AR (e `LM` ee) where
 equality (These (These x xx) (These xxx xxxx)) = case equality (x `lu` xxx) `lu`equality (xx `lu` xxxx) of
  These (That x') (That xx') -> That (These x' xx')
  These _ _ -> This ((x `lu` xx) `lu` (xxx `lu` xxxx))
