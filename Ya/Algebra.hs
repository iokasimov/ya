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
 ( Covariant Endo Semi Functor (->) t
 , Covariant Monoidal Functor (->) LM LM tt
 , Component Natural (->) (->) (t `T_TT_I` tt) (t `TT_T_I` tt)
 , Component Natural (->) (->) (Labeled l (R_U_I_T_I LM t) `T_TT_I` tt) (Labeled l (R_U_I_T_I LM t) `TT_T_I` tt)
 ) => Mapping Straight Straight (->) (->)
  (Labeled l (t `T_TT_I` R_U_I_T_I LM t) `T_TT_I` tt)
  (Labeled l (t `T_TT_I` R_U_I_T_I LM t) `TT_T_I` tt) where
 mapping = rwr / \from -> rwr / \x -> unwrap (unwrap x)
   `yo` wrapped (map @Straight @Straight @(->) @(->)
            @(Labeled l (R_U_I_T_I LM t) `T_TT_I` tt)
            @(Labeled l (R_U_I_T_I LM t) `TT_T_I` tt) from)
          `ha` wrap @Arrow @(Labeled l (R_U_I_T_I LM t) (tt _))
   `yi` wrapped (map @Straight @Straight @(->) @(->) @(t `T_TT_I` tt) @(t `TT_T_I` tt) unwrap)
   `yo` wrap @Arrow @(Labeled l _ _)
   `ha` wrap @Arrow @(T_TT_I t (R_U_I_T_I LM t) _)

-- TODO: reduce a number of transformations here
instance
 ( Covariant Endo Semi Functor (->) t
 , Covariant Endo Semi Functor (->) tt
 , Covariant Monoidal Functor (->) LM LM tt
 , Transformation Straight Functor (->) (->) (T_TT_I t tt) (TT_T_I t tt)
 ) => Mapping Straight Straight (->) (->)
  (Labeled (U_I_II (->) () ()) (R_U_I_T_I LM t) `T_TT_I` tt)
  (Labeled (U_I_II (->) () ()) (R_U_I_T_I LM t) `TT_T_I` tt) where
 mapping = rwr / \from -> rwr /
  \(T_'_I (R_U_I_T_I (Recursive (U_I_T_II (These x xs))))) ->
    x `yo` from `lu`
     (wrapped (map @Straight @Straight @(->) @_ @(t `T_TT_I` tt) @(t `TT_T_I` tt) (unwrap @(->) @(R_U_I_T_I _ _ _) `ha` unwrap @(->) @(Labeled _ _ _)))
      (xs `yo` wrap @(->) @(R_U_I_T_I _ _ _)
       `ho` wrap @(->) @(Labeled (U_I_II (->) () ()) _ _)
       `ho` wrapped (map @Straight @Straight @(->) @(->)
         @(Labeled (U_I_II (->) () ()) (R_U_I_T_I LM t) `T_TT_I` tt)
         @(Labeled (U_I_II (->) () ()) (R_U_I_T_I LM t) `TT_T_I` tt)
         from)
      )
     ) `yp'yo` wrap @(->) @(Labeled _ _ _)
         `ha` wrap @(->) @(R_U_I_T_I _ _ _)
         `ha` wrap @(->) @(Recursive _)
         `ha` wrap @(->) @(U_I_T_II _ _ _ _)

-- TODO: reduce a number of transformations here
instance
 ( Covariant Endo Semi Functor (->) t
 , Covariant Endo Semi Functor (->) tt
 , Covariant Monoidal Functor (->) LM LM tt
 , Transformation Straight Functor (->) (->) (t `T_TT_I` tt) (t `TT_T_I` tt)
 ) => Mapping Straight Straight (->) (->)
  (Labeled (U_II_I (->) () ()) (R_U_I_T_I LM t) `T_TT_I` tt)
  (Labeled (U_II_I (->) () ()) (R_U_I_T_I LM t) `TT_T_I` tt) where
 mapping = rwr / \from -> rwr
  / \(T_'_I (R_U_I_T_I (Recursive (U_I_T_II (These x xs))))) ->
   (These
    `hoo'ho` wrap @(->) @(U_I_T_II _ _ _ _)
    `ho` wrap @(->) @(Recursive _)
    `ho` wrap @(->) @(R_U_I_T_I _ _ _)
    `ho` wrap @(->) @(Labeled _ _ _))
   `fo` (x `yo` from)
   `fc` wrapped (map @Straight @Straight @(->) @_ @(t `T_TT_I` tt) @(t `TT_T_I` tt)
         (unwrap @(->) @(R_U_I_T_I _ _ _) `ha` unwrap @(->) @(Labeled _ _ _))
        )
    (xs
     `yo` wrap @(->) @(R_U_I_T_I _ _ _)
     `ho` wrap @(->) @(Labeled _ _ _)
     `ho` wrapped (map @Straight @Straight @(->) @(->)
        @(Labeled (U_II_I (->) () ()) (R_U_I_T_I LM t) `T_TT_I` tt)
        @(Labeled (U_II_I (->) () ()) (R_U_I_T_I LM t) `TT_T_I` tt)
        from)
    )

-- TODO: try to simplify
instance
 Mapping Straight Straight (->) (->)
  (Day Straight (->) LM LM t t (Recursive (U_I_T_II t LM e)) (Recursive (U_I_T_II t LM ee))) t =>
 Mapping Straight Straight (->) (->)
  (Day Straight (->) LM LM (R_U_I_T_I LM t) (R_U_I_T_I LM t) e ee) (R_U_I_T_I LM t) where
 mapping = rwr / \from -> rwr / \case
  These (These e ee) (Straight f) ->
   let These e_ e__ = he'he'he e in
   let These ee_ ee__ = he'he'he ee in
   Recursive `compose` U_I_T_II / These
    (from `compose` f / These e_ ee_)
    (day @Straight @Arrow @t @LM @LM identity
     (unwrap
      `compose` day @Straight @(->)
       @(R_U_I_T_I LM t) @LM @LM
        identity (from `compose` f)
      `compose` fio R_U_I_T_I
      `compose` foi R_U_I_T_I)
     / These e__ ee__)

instance
 (Initial (->), Monoidal Straight Functor (->) LM ML t) =>
 Mapping Straight Straight (->) (->) (Straight (->) ()) (R_U_I_T_I LM t) where
 mapping = rwr / \from (Straight f) ->
  R_U_I_T_I `compose` Recursive `compose` U_I_T_II
   / These (from / f ()) (empty @t `yo` initial @(->))

instance
 ( Mapping Straight Straight (->) (->) (Day Straight (->) LM LM t t (R_U_I_T_I LM t e) (R_U_I_T_I LM t ee)) t
 , Mapping Straight Straight (->) (->) (Day Straight (->) LM LM t t (Recursive (U_I_T_II t LM e)) (Recursive (U_I_T_II t LM ee))) t
 ) => Mapping Straight Straight (->) (->) (Day Straight (->) LM LM (t `T_TT_I` R_U_I_T_I LM t) (t `T_TT_I` R_U_I_T_I LM t) e ee) (t `T_TT_I` R_U_I_T_I LM t) where
 mapping = rwr / \from -> rwr / \case
  These (These (T_TT_I e) (T_TT_I ee)) (Straight f) ->
    day @Straight @Arrow @t @LM @LM identity
     (day @Straight @Arrow @(R_U_I_T_I LM t) @LM @LM identity (from `compose` f))
      (These e ee)

instance
 ( Monoidal Straight Functor (->) LM LM t
 , Monoidal Straight Functor (->) LM LM (R_U_I_T_I LM tt)
 ) => Mapping Straight Straight (->) (->) (Straight (->) ()) (t `T_TT_I` R_U_I_T_I LM tt) where
 mapping = rwr / \from (Straight f) -> T_TT_I /
  enter @t `yu` (enter @(R_U_I_T_I LM tt) `yo` from `compose` f)

-- TODO: try to avoid mapping twice datastructure here
instance
 ( Covariant Endo Semi Functor (->) t
 , Mapping Straight Straight (->) (->) (Day Straight (->) LM MLM t t (R_U_I_T_I LM t e) (R_U_I_T_I LM t ee)) t
 , Mapping Straight Straight (->) (->) (Day Straight (->) LM MLM t t (Recursive (U_I_T_II t LM e)) (Recursive (U_I_T_II t LM ee))) t
 ) => Mapping Straight Straight (->) (->) (Day Straight (->) LM MLM (t `T_TT_I` R_U_I_T_I LM t) (t `T_TT_I` R_U_I_T_I LM t) e ee) (t `T_TT_I` R_U_I_T_I LM t) where
 mapping = rwr / \from -> rwr / \case
  These (These (T_TT_I e) (T_TT_I ee)) (Straight f) ->
    (day @Straight @Arrow @t @LM @MLM identity
     (\case
      U_U_I_II_UU_I_II (This (This x)) -> x `yo` from `compose` f `compose` U_U_I_II_UU_I_II `compose` This `compose` This
      U_U_I_II_UU_I_II (This (That x)) -> x `yo` from `compose` f `compose` U_U_I_II_UU_I_II `compose` This `compose` That
      U_U_I_II_UU_I_II (That x) -> day @Straight @Arrow @(R_U_I_T_I LM t) @LM @MLM identity (from `compose` f) x
     )
      (These e ee)
    )

-- TODO: try to avoid mapping twice datastructure here
instance
 ( Covariant Endo Semi Functor (->) t
 , Mapping Straight Straight (->) (->) (Day Straight (->) LM MLM t t (Recursive (U_I_T_II t LM e)) (Recursive (U_I_T_II t LM ee))) t
 ) => Mapping Straight Straight (->) (->) (Day Straight (->) LM MLM (R_U_I_T_I LM t) (R_U_I_T_I LM t) e ee) (R_U_I_T_I LM t) where
 mapping = rwr / \from -> rwr / \case
  These (These e ee) (Straight f) ->
   let These e_ e__ = he'he'he e in
   let These ee_ ee__ = he'he'he ee in
   Recursive `compose` U_I_T_II / These
    (from `compose` f `compose` U_U_I_II_UU_I_II `compose` That / These e_ ee_)
    (day @Straight @Arrow @t @LM @MLM identity
     (unwrap @Arrow `compose` \case
      U_U_I_II_UU_I_II (This (This x)) -> R_U_I_T_I x `yo` from `compose` f `compose` U_U_I_II_UU_I_II `compose` This `compose` This
      U_U_I_II_UU_I_II (This (That x)) -> R_U_I_T_I x `yo` from `compose` f `compose` U_U_I_II_UU_I_II `compose` This `compose` That
      U_U_I_II_UU_I_II (That (These x xx)) -> day @Straight @Arrow @(R_U_I_T_I LM t) @LM @MLM identity (from `compose` f)
       (These (R_U_I_T_I x) (R_U_I_T_I xx))
     )
     / These e__ ee__)

instance (Initial (->), Monoidal Straight Functor (->) LM ML t) =>
 Mapping Straight Straight (->) (->) (Straight (->) Void) (t `T_TT_I` R_U_I_T_I LM tt) where
 mapping = rwr / \_ _ -> T_TT_I (empty @t `yo` initial @(->))

-- TODO: generalize this instance
instance Mapping Opposite Straight (U_I_UU_II_U_II_I (->) LM )(->)
 (U_II_I (U_I_UU_II_I (->) LM) e)
 (U_II_I (U_I_UU_II_I (->) LM) e) where
 mapping = rwr / \(U_I_UU_II_U_II_I from) ->
  rwr `compose` rwr `identity` \state old ->
   let (These new f) = from old in f `fio` state new

instance Mapping Straight Straight (U_I_UU_II_U_II_I (->) LM) (U_I_UU_II_U_II_I (->) LM) (U_I_II LM e) (U_I_II LM e) where
 mapping = rwr / \(U_I_UU_II_U_II_I from) -> U_I_UU_II_U_II_I / \(U_I_II (These e x)) ->
   let s = from x in U_I_II (These e (this s)) `lu` fo (that s)

instance Mapping Straight Straight (U_I_UU_II_U_II_I (->) LM) (U_I_UU_II_U_II_I (->) LM) (U_II_I LM e) (U_II_I LM e) where
 mapping = rwr / \(U_I_UU_II_U_II_I from) -> U_I_UU_II_U_II_I / \(U_II_I (These x e)) ->
   let s = from x in U_II_I (These (this s) e) `lu` fo (that s)

-- TODO: I'm not really sure about this instance... it could easily lead to an error!
instance Mapping Straight Straight (U_I_UU_II_U_II_I (->) LM) (U_I_UU_II_U_II_I (->) LM) Identity (U_I_I LM) where
 mapping = rwr / \(U_I_UU_II_U_II_I from) -> U_I_UU_II_U_II_I / \(Identity x) ->
   let s = from x in U_I_I (this s `lu`this s) `lu` (\(U_I_I (These _ _)) -> Identity (that s (this s)))

instance Mapping Straight Straight (U_I_UU_II_U_II_I (->) LM) (U_I_UU_II_U_II_I (->) LM) (U_I_II LM e) Identity where
 mapping = rwr / \(U_I_UU_II_U_II_I from) -> U_I_UU_II_U_II_I / \(U_I_II (These e x)) ->
   let s = from x in Identity (this s) `lu` (U_I_II `compose` (e `lu`) `compose` that s `compose` unwrap)

instance Mapping Straight Straight (U_I_UU_II_U_II_I (->) LM) (U_I_UU_II_U_II_I (->) LM) (U_II_I LM e) Identity where
 mapping = rwr / \(U_I_UU_II_U_II_I from) -> U_I_UU_II_U_II_I / \(U_II_I (These x e)) ->
   let s = from x in Identity (this s) `lu` (U_II_I `compose` (`lu` e) `compose` that s `compose` unwrap)

-- TODO: I should alse test how attributes behave on sums

instance Mapping Straight Straight (->) (->)
 (T_TT_I
  (U_I_II (U_I_UU_II_I (->) LM) e)
  (U_I_II (U_I_UU_II_I (->) LM) e)
 )
 (U_I_II (U_I_UU_II_I (->) LM) e) where
 mapping = rwr / \from ->
  \(T_TT_I (U_I_II (U_I_UU_II_I state))) ->
   U_I_II `compose` U_I_UU_II_I `identity` \old ->
    let These (U_I_II (U_I_UU_II_I f)) s = state old in
     from `foi` f s

instance Covariant Endo Semi Functor (->) t
 => Mapping Straight Straight (->) (->) t (T_TTT_TT_I (Straight (->) e) (Straight LM e) t) where
 mapping = rwr / \from x -> T_TTT_TT_I `compose` Straight `li` \state ->
  x `yo` from `ho` These state `ho` Straight

instance (Covariant Monoidal Functor (->) LM LM t, e ~ ee)
 => Mapping Straight Straight (->) (->)
  (U_I_II (U_I_UU_II_I (->) LM) ee)
  (T_TTT_TT_I (U_I_II ARR e) (U_I_II LM e) t) where
 mapping = rwr / \from (U_I_II (U_I_UU_II_I x)) -> 
  wrap @_ @(T_TTT_TT_I _ _ _ _)
  `compose` wrap @_ @(U_I_II _ _ _)
  `identity` (yu enter
   `compose` map @Straight @Straight from
   `compose` wrap @_ @(U_I_II _ _ _)
   `compose` swap
   `compose` x)

-- x: ee -> Object Straight Arrow a ee

instance  {-# OVERLAPPABLE #-} Component Natural ARR (->) (T_TT_I t tt) t => Mapping Straight Straight (->) (->)
 (T_TT_I (Straight (->) e `T_TT_I` t) tt) (Straight (->) e `T_TT_I` t) where
 mapping = rwr / \from -> rwr `compose` rwr /
  \(Straight f) e -> map @Straight @Straight @(->) @(->) @(t `T_TT_I` tt) @t from (T_TT_I (f e))

instance {-# OVERLAPS #-} Covariant Endo Semi Functor (->) t => Mapping Straight Straight (->) (->)
 (T_TT_I (Straight (->) e `T_TT_I` t) (Straight (->) e)) (Straight (->) e `T_TT_I` t) where
 mapping = rwr / \from -> rwr `compose` rwr /
  \(Straight f) e -> f e `yo` unwrap @Arrow `ho` (`li` e) `ho` from

-- NOTE: this version allow different type of states, but it requires providing types to make it compile
instance
 ( Covariant Endo Semi Functor (->) t
 , Transformation Natural Functor (->) (->) (T_TT_I t t) t
 ) => Mapping Straight Straight (->) (->)
 (T_TT_I
  (T_TTT_TT_I (Straight (->) old) (Straight LM btw) t)
  (T_TTT_TT_I (Straight (->) btw) (Straight LM new) t)
 )
 (T_TTT_TT_I (Straight (->) old) (Straight LM new) t) where
 mapping = rwr / \from (T_TT_I (T_TTT_TT_I (Straight x))) -> 
  wrap @_ @(T_TTT_TT_I _ _ _ _) `compose` wrap @_ @(Straight _ _ _)
  `li` \old -> x old `yok` \(Straight (These btw (T_TTT_TT_I (Straight f))))
   -> f btw `yo'yo` from

-- TODO: try to use adjunctions here
instance
 ( Covariant Monoidal Functor (->) LM LM tt
 , Transformation Natural Functor (->) (->) (T_TT_I tt tt) tt
 , e ~ ee
 ) => Mapping Straight Straight (->) (->)
 (T_TT_I
  (T_TTT_TT_I (Straight (->) e) (Straight LM e) tt)
  (U_I_II (U_I_UU_II_I (->) LM) ee)
 )
 (T_TTT_TT_I (U_I_II (->) e) (U_I_II LM e) tt) where
  mapping = rwr / \from (T_TT_I (T_TTT_TT_I (U_I_II x))) ->
   wrap @_ @(T_TTT_TT_I _ _ _ _) `compose` wrap @_ @(U_I_II _ _ _)
    `li` \old -> x old `yok` \(U_I_II (These btw (U_I_II (U_I_UU_II_I f))))
      -> yu (enter @tt) / U_I_II (swap (f btw)) `yo` from

instance
 ( Covariant Endo Semi Functor (->) t
 , Mapping Straight Straight (->) (->) (t `T_TT_I` t) t
 ) => Mapping Straight Straight (->) (->)
  (T_TT_I (T_TTT_TT_I (Straight (->) e) (Straight LM e) t) t)
  (T_TTT_TT_I (Straight (->) e) (Straight LM e) t) where
 mapping = rwr / \from (T_TT_I (T_TTT_TT_I (Straight f))) -> T_TTT_TT_I `compose` Straight / \old ->
  component @Straight @(->) @(->) @(t `T_TT_I` t) @t
   (T_TT_I (f old `yo` (\(Straight (These x y)) -> y `yo` Straight `ha` These x `ha` from)))

instance Mapping Straight Straight (->) (->) (U_I_II LM e `T_TT_I` tt) (U_I_II LM e `TT_T_I` tt) =>
 Mapping Straight Straight (->) (->)
  (U_I_II (U_I_UU_II_I (->) LM) e `T_TT_I` tt)
  (T_TTT_TT_I (U_I_II (->) e) (U_I_II LM e) tt) where
 mapping = rwr / \from (T_TT_I (U_I_II (U_I_UU_II_I x))) -> 
  T_TTT_TT_I `compose` U_I_II / \old -> wrapped @(->)
   `li` map @Straight @Straight @(->) @(->) @(U_I_II LM e `T_TT_I` tt) @(U_I_II LM e `TT_T_I` tt) from
   `li` Straight (let These e r = x old in These r e)

instance Monoidal Straight Functor (->) LM LM t =>
 Mapping Straight Straight (->) (->) (U_I_II (->) ()) (U_I_II (->) e `T_TT_I` t) where
 mapping = rwr / \from -> rwr / \f -> Straight / \_ -> yu enter `compose` from `li` f ()

instance Mapping Straight Straight (->) (->) (U_I_II (->) ()) (U_I_II (U_I_UU_II_I (->) LM) e) where
 mapping = rwr / \from -> rwr / \f -> U_I_UU_II_I `li` \e -> from `li` f () `lu` e

instance Monoidal Straight Functor (->) LM LM t =>
 Mapping Straight Straight (->) (->) (U_I_II (->) ()) (T_TTT_TT_I (U_I_II (->) e) (U_I_II LM e) t) where
 mapping = rwr / \from (Straight f) -> T_TTT_TT_I `compose` Straight
  / \old -> yu enter `compose` Straight `compose` These old `compose` from `li` f ()

instance
 ( Covariant Semi Functor from (->) t
 , forall e . Covariant Semi Functor into (->) (U_I_II from e)
 ) => Mapping Straight Straight from (->) t (UU_V_U_I_II_T_II Straight into (->) t r) where
 mapping = rwr / \from x -> UU_V_U_I_II_T_II (\(Straight e) -> fo @from (fio @into @(->) e from) x)

instance
 ( Covariant Endo Semi Functor (->) t
 , forall e . Covariant Endo Semi Functor (->) (U_I_II (->) e)
 ) => Mapping U_1_I Straight (->) (->) t (UU_V_U_I_II_T_II U_1_I (->) (->) t r) where
 mapping = rwr / \_ x -> UU_V_U_I_II_T_II (\(U_1_I e) -> (\_ -> e ()) `fo` x)

instance
 ( Contravariant Semi Functor from (->) t
 , forall e . Contravariant Semi Functor into (->) (Opposite from e)
 ) => Mapping Opposite Straight from (->) t (UU_V_U_I_II_T_II Opposite into (->) t r) where
 mapping = rwr / \from x -> UU_V_U_I_II_T_II (\(Opposite e) -> fa @from (fai @into @(->) e from) x)

instance Mapping Straight Straight (->) (->) (U_I_II ML e `T_TT_I` U_I_II ML e) (U_I_II ML e) where
 mapping = rwr / \from -> \case
  T_TT_I (Straight (That (Straight (That x)))) -> Straight (That / from x)
  T_TT_I (Straight (That (Straight (This e)))) -> Straight (This e)
  T_TT_I (Straight (This e)) -> Straight (This e)

instance Covariant Monoidal Functor (->) LM LM t =>
 Mapping Straight Straight (->) (->) (U_I_II ML e `T_TT_I` t) (U_I_II ML e `TT_T_I` t) where
 mapping = rwr / \from -> rwr / \case
  Straight (This e) -> yu enter (Straight `li` This e)
  Straight (That x) -> x `yo` from `ho` That  `ho` Straight

instance
 ( Monoidal Straight Functor (->) LM LM t
 , Mapping Straight Straight (->) (->) (T_TT_I t t) t
 , Mapping Straight Straight (->) (->) Identity (U_I_II (->) e)
 ) => Mapping Straight Straight (->) (->) (t `T_TT_I` T_'_I (U_I_II ML () ()) (U_I_II ML e)) t where
 mapping = rwr / \from -> \(T_TT_I x) ->
  x `yok'he'he` constant @Arrow (map @Straight @Straight from (T_TT_I x)) `la` yu (enter @t) `ha` from

instance
 ( Mapping U_I_II U_I_II (->) (->) t t
 , Mapping U_I_II U_I_II (->) (->) (T_TT_I t t) t
 ) => Mapping Straight Straight (->) (->) (t `T_TT_I` T_'_I (U_I_I LM ()) Identity) t where
 mapping = rwr / \from -> \(T_TT_I x) ->
  x `yok'he'he` constant @Arrow (map @Straight @Straight @_ @_ @_ @t from (T_TT_I x))

instance Mapping Straight Straight (->) (->)
  (Day Straight (->) LM LM
   (U_I_II (U_I_UU_II_I (->) LM) e)
   (U_I_II (U_I_UU_II_I (->) LM) e) ee eee)
  (U_I_II (U_I_UU_II_I (->) LM) e) where
 mapping = rwr / \from -> rwr / \case
  These (These ee eee) (Straight f) -> U_I_UU_II_I `li` \old ->
   let These x new = ee `he'he` old in
   let These y upd  = eee `he'he` new in
   These (from `li` f (These x y)) upd

instance
 ( Component Natural (->) (->) (t `T_TT_I` t) t
 , Covariant Yoneda (->) (->) t
 ) => Mapping Straight Straight (->) (->)
  (Day Straight (->) LM LM (T_TTT_TT_I (U_I_II (->) e) (U_I_II LM e) t) (T_TTT_TT_I (U_I_II (->) e) (U_I_II LM e) t) ee eee)
  (T_TTT_TT_I (U_I_II (->) e) (U_I_II LM e) t) where
 mapping = rwr / \from -> rwr / \case
  These (These (T_TTT_TT_I (Straight x)) (T_TTT_TT_I (Straight y))) (Straight f) ->
   Straight / \old -> x old `yok` \(Straight (These btw e)) -> from `compose` f `compose` These e `fo'fo` y btw

instance
 ( Component Natural (->) (->) (t `T_TT_I` t) t
 , Monoidal Straight Functor (->) LM LM t
 ) => Mapping Straight Straight (->) (->)
  (Day Straight (->) LM LM (T_TT_I (U_I_II (->) a) t) (U_I_II (->) a `T_TT_I` t) ee eee)
  (T_TT_I (U_I_II (->) a) t) where
 mapping = rwr / \from -> rwr / \case
  These (These (T_TT_I (Straight f)) (T_TT_I (Straight g))) (Straight h) -> Straight / \x ->
   yp (These (f x) (g x)) `yo` h `ho` from

-- TODO: generalize with limits
instance Covariant Monoidal Functor (->) LM LM t =>
 Mapping Straight Straight (->) (->) (U_I_II LM e `T_TT_I` t) (U_I_II LM e `TT_T_I` t) where
 mapping = rwr / \from -> rwr / \case
  Straight (These e x) -> x `yo` from `ho` These e `ho` Straight

instance Covariant Endo Semi Functor (->) t =>
 Mapping Straight Straight (->) (->) (t `T_TT_I` U_I_II (->) e) (t `TT_T_I` U_I_II (->) e) where
 mapping = rwr / \from -> rwr / \x ->
  Straight / \e -> x `yo` (from `compose` (`li` e) `compose` unwrap)

-- TODO: generalize
-- We need this instance to make `yok'yoklKL` work
instance {-# OVERLAPS #-} Component Natural (->) (->) (T_TT_I t tt) t =>
 Mapping Straight Straight (->) (->) (T_TT_I t (T_'_I l tt)) t where
 mapping = rwr / \from ->
  map @Straight @Straight @(->) @(->) @(T_TT_I t tt) @t from `compose` rwr @_ @(->) (fo @Arrow unwrap)

instance Setoid Arrow () where
 q _ = That ()

instance (Setoid Arrow e, Setoid Arrow ee) => Setoid Arrow (e `ML` ee) where
 q (These (This x) (This xx)) = q (x `lu` xx) `yoi` (`yio` This) `ho` (`yoi` This) `yio` This
 q (These (That x) (That xx)) = q (x `lu` xx) `yoi` (`yio` That) `ho` (`yoi` That) `yio` That
 q (These x xx) = This (These x xx)

instance (Setoid Arrow e, Setoid Arrow ee) => Setoid Arrow (e `LM` ee) where
 q (These (These x xx) (These xxx xxxx)) = case q (x `lu` xxx) `lu`q (xx `lu` xxxx) of
  These (That x') (That xx') -> That (These x' xx')
  These _ _ -> This ((x `lu` xx) `lu` (xxx `lu` xxxx))
