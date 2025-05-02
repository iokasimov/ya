{-# OPTIONS_GHC -fno-warn-orphans #-}
{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE UndecidableInstances #-}
module Ya.Program.Interface (module Exports, focus, shaft) where

import Ya.Algebra
import Ya.Operators
import Ya.Program.Patterns
import Ya.Program.Primitive
import Ya.Program.Labels

import Ya.Program.Interface.Field as Exports
import Ya.Program.Interface.Match as Exports
import Ya.Program.Interface.Stackable as Exports
import Ya.Program.Interface.Shiftable as Exports

instance Mapping U_I_II U_I_II AR AR (Shafted List) List where
 mapping = rewrap / \from (U_T_I_TT_I (These (Labeled bs) (Labeled fs))) -> that
  (bs `yokl` Prior `ha` New `ha` State `ha` Event `ha` push @List `he'he'hv____` fs) `yo` from

instance Mapping U_I_II U_I_II AR AR (U_I_II AR Void) (Shafted List) where
 mapping = rewrap / \_ _ -> U_T_I_TT_I (wrap empty `lu` wrap empty)

instance Mapping U_I_II U_I_II AR AR (Day U_I_II AR P S (Shafted List) (Unit `L` Shafted List) i ii) (Shafted List) where
 mapping = rewrap / \from -> rewrap / \(These (These i ii) (U_I_II f)) ->
  let These i' i'' = unwrap i in
  let These ii' ii'' = (unwrap `compose` unwrap) ii in
  (wrap (day @U_I_II @AR @Unit @List @List @P @S identity (from `compose` f) (unwrap i' `lu` wrap (unwrap ii')))) `lu`
  (wrap (day @U_I_II @AR @Unit @List @List @P @S identity (from `compose` f) (unwrap i' `lu` wrap (unwrap ii'))))

instance Mapping U_I_II U_I_II AR AR (Only `P'T'I'TT'I` Shafted List) ((Only `P'T'I'TT'I` Shafted List) `T'TT'I` Unit `L` (Only `P'T'I'TT'I` Shafted List)) where
 mapping = rewrap / \from x@(U_T_I_TT_I (These (Identity _) (U_T_I_TT_I (These rl fl)))) ->
  Identity `hv` Labeled x
   `lu__` (positions (x `lu` unwrap rl) `yi` that `ho` that `ho` Reverse)
    `lu_` (positions (x `lu` unwrap fl) `yi` that `ho` that `ho` Forward)
    `yi_` U_T_I_TT_I
   `yi__` U_T_I_TT_I `ho` T'TT'I
   `yo__` from where

  positions :: forall item label .
   Scrolling List item `P` List item `AR__`
   List (Unit `L` Scrolling List `T'I` item) `P` (Scrolling List item `P` List (Unit `L` Scrolling List `T'I` item))
  positions (These x xs) = xs `yukl__` Forth `ha` New
   `hv____` State `hv__` Event `hv_` (shift (by Fore) `ho` that `ho` auto) `ha_` Scope `hv` at @(Scrolling List item)
   `yok_` New `ha` State `ha__` Event `ha` push @List `ha` Labeled `ho_'ha` Scope `hv` at @(List `T'I_` Unit `L` Scrolling List `T'I` item)
   `he'he'hv______` x `lu` by `hv` Empty @List

instance Mapping U_I_II U_I_II Arrow Arrow (Construction List)
 ((Only `P'T'I'TT'I` Shafted List) `T'TT'I` Construction List `P'T'I'TT'I` (Reverse List `T'TT'I` (Only `P'T'I'TT'I` Shafted List `T'TT'I` Construction List))) where
  mapping = rewrap / \from x -> U_T_I_TT_I
   (T'TT'I (U_T_I_TT_I ((Only `hv__` x `yo` from) `lu` U_T_I_TT_I (Reverse `hv` Empty @List Unit `lu`Forward `hv` Empty @List Unit))) `lu` T'TT'I (Reverse `hv` Empty @List Unit))

-- instance Mapping U_I_II U_I_II Arrow Arrow
 -- ((Only `P'T'I'TT'I` (Reverse List `P'T'I'TT'I` Forward List)) `T'TT'I` Construction List `P'T'I'TT'I` (Reverse List `T'TT'I` (Only `P'T'I'TT'I` (Reverse List `P'T'I'TT'I` Forward List) `T'TT'I` Construction List)))
 -- ((Only `P'T'I'TT'I` (Reverse List `P'T'I'TT'I` Forward List)) `T'TT'I` Construction List) where
 -- mapping = rewrap / \from (U_T_I_TT_I (These sl xs)) ->
  -- T'TT'I `he` that ((unwrap xs `yokl` State `ha` Transition `ha_` restoring `ho'ho` (Unit `lu`)) `he_'he` unwrap sl) `yo` from where

   -- restoring (U_T_I_TT_I (These focus shafted)) scrolling_list_tree = U_T_I_TT_I
    -- `he__` Only (Tree `he` unwrap focus `he__` to @(Nonempty List) `he` scrolling_list_tree `yo` unwrap @AR `yi` unwrap @AR)
     -- `lu` unwrap shafted

instance Mapping U_I_II U_I_II AR AR (Construction Optional) List where
 mapping = rewrap / \from -> rewrap / wrap `ho'yo` from `ho` Some

instance Mapping U_I_II U_I_II AR AR (Construction Optional) (List `P'T'I'TT'I` Shafted List) where
 mapping = rewrap / \from x -> U_T_I_TT_I (Empty @List Unit `lu` U_T_I_TT_I (Reverse `hv` Empty @List Unit `lu` Forward `ha` List `hv` unwrap x)) `yo` from

instance Mapping U_I_II U_I_II AR AR List (List `P'T'I'TT'I` Shafted List) where
 mapping = rewrap / \from x -> U_T_I_TT_I (Empty @List Unit `lu` U_T_I_TT_I (Reverse `hv` Empty @List Unit `lu` Forward `hv` x)) `yo` from

instance Mapping U_I_II U_I_II AR AR (List `P'T'I'TT'I` Shafted List) List where
 mapping = rewrap / \from (U_T_I_TT_I (These w (U_T_I_TT_I (These (Labeled r) (Labeled f))))) ->
  that `ho'yo` from
  `hv_____` enter @(State `T'I` List _)
    `yuk__` New (f `yokl` Prior `ha` New `ha` State `ha` Event `ha` push @List)
    `yuk__` New (w `yokl` Prior `ha` New `ha` State `ha` Event `ha` push @List)
    `yuk__` New (r `yokl` Forth `ha` New `ha` State `ha` Event `ha` push @List)
  `he'he'hv____` Empty @List Unit

instance Mapping U_I_II U_I_II AR AR (Only `P'T'I'TT'I` Shafted List) (List `P'T'I'TT'I` Shafted List) where
 mapping = rewrap / \from -> rewrap / \x -> x
  `yoi` is `he'ho` (\i -> List `ha` Item (from i) `ha` Last `hv` Unit)
  `yio'yo` from

instance Mapping U_I_II U_I_II AR AR (Only `P'T'I'TT'I` Shafted List)
 ((Only `P'T'I'TT'I` Shafted List) `T'TT'I` Tree `P'T'I'TT'I` Reverse List `T'TT'I` (Only `P'T'I'TT'I` Shafted List `T'TT'I` Tree)) where
 mapping = rewrap / \from x -> x `yo` from `ho` intro @Tree `yi` wrap @AR `lu` by (wrap @AR `ha` Reverse `ha` Empty @List) `yi` wrap @AR

-- TODO: check this instance, I'm not sure it works correctly
instance
 ( Covariant Endo Semi Functor AR t
 , Covariant Endo Semi Functor AR tt
 , Covariant Endo Semi Functor AR ttt
 , Covariant Endo Monoidal Functor AR P P Unit tttt
 , Covariant Endo Transformation Functor AR (t `T'TT'I` Unit `L` ll `L` tttt) (t `TT'T'I` tttt)
 , Covariant Endo Transformation Functor AR (tt `T'TT'I` Unit `L` ll `L` tttt) (tt `TT'T'I` tttt)
 , Covariant Endo Transformation Functor AR (ttt `T'TT'I` Unit `L` ll `L` tttt) (ttt `TT'T'I` tttt)
 ) => Mapping U_I_II U_I_II AR AR
 ((t `P'T'I'TT'I` (Reverse tt `P'T'I'TT'I` Forward ttt)) `T'TT'I` Unit `L` ll `L` tttt)
 ((t `P'T'I'TT'I` (Reverse tt `P'T'I'TT'I` Forward ttt)) `TT'T'I` tttt)
 where
  mapping = rewrap / \from -> rewrap / \(U_T_I_TT_I (These w (U_T_I_TT_I (These (Labeled r) (Labeled f))))) ->
   (r `yokl` is) `lu'yp` Run (w `yokl` is) `lu'yp` Run (f `yokl` is) -- `yo'yo` from
    `yo` (\(These (These sx x) xs) -> U_T_I_TT_I (These (x `yo` from) (U_T_I_TT_I (These (Labeled (sx `yo` from)) (Labeled (xs `yo` from))))))

instance
 ( Covariant Endo Semi Functor AR tt
 , Covariant Endo Semi Functor AR ttt
 , Covariant Endo Monoidal Functor AR P P Unit tttt
 , Covariant Endo Transformation Functor AR (tt `T'TT'I` Unit `L` ll `L` tttt) (tt `TT'T'I` tttt)
 , Covariant Endo Transformation Functor AR (ttt `T'TT'I` Unit `L` ll `L` tttt) (ttt `TT'T'I` tttt)
 ) => Mapping U_I_II U_I_II AR AR
 ((Reverse tt `P'T'I'TT'I` Forward ttt) `T'TT'I` Unit `L` ll `L` tttt)
 ((Reverse tt `P'T'I'TT'I` Forward ttt) `TT'T'I` tttt)
 where
  mapping = rewrap / \from -> rewrap / \(U_T_I_TT_I (These (Labeled r) (Labeled f))) ->
   (r `yokl` is) `lu'yp` Run (f `yokl` is)
    `yo` (\(These sx xs) -> U_T_I_TT_I (These (Labeled (sx `yo` from)) (Labeled (xs `yo` from))))

instance
 ( Covariant Endo Semi Functor AR t
 -- , Covariant Endo Semi Functor AR tt
 -- , Covariant Endo Semi Functor AR ttt
 -- , Covariant Endo Monoidal Functor AR P P tttt
 -- , Covariant Endo Transformation Functor AR (t `T'TT'I` Unit `L` ll `L` tttt) (t `TT'T'I` tttt)
 -- , Covariant Endo Transformation Functor AR (tt `T'TT'I` Unit `L` ll `L` tttt) (tt `TT'T'I` tttt)
 -- , Covariant Endo Transformation Functor AR (ttt `T'TT'I` Unit `L` ll `L` tttt) (ttt `TT'T'I` tttt)
 ) => Mapping U_I_II U_I_II AR AR
 (((t `P'T'I'TT'I` Shafted List) `T'TT'I` Tree `P'T'I'TT'I` Reverse List `T'TT'I` (t `P'T'I'TT'I` Shafted List `T'TT'I` Tree)) `T'TT'I` Unit `L` ll `L` tttt)
 (((t `P'T'I'TT'I` Shafted List) `T'TT'I` Tree `P'T'I'TT'I` Stacked Only Tree List) `TT'T'I` tttt)  where
  -- mapping = rewrap / \from -> rewrap /
  --  \(U_T_I_TT_I (These (U_T_I_TT_I (These w (U_T_I_TT_I (These (Labeled r) (Labeled f))))) (Labeled passed))) ->
  --  ()

-- TODO: we are going to apply the same function to all items in a list but it's actually fine
instance Mapping U_I_II U_I_II AR AR (List `P'T'I'TT'I` Shafted List) ((List `P'T'I'TT'I` Shafted List) `T'TT'I` Unit `L` (List `P'T'I'TT'I` Shafted List)) where
 mapping = rewrap / \from x@(U_T_I_TT_I (These _ (U_T_I_TT_I (These rl fl)))) ->
  List `ha` Item (Labeled x) `ha` Last `hv` Unit
    `lu__` (unwrap rl `yokl` Prior `ha` New `ha` State `ha` Event `ha` push @List `ha` Labeled `ha` that `ha` shift (by Back) `ha_` is `hu` x)
      `he'he'hv` Empty @List () `yi` that `ho` Reverse
     `lu_` (unwrap fl `yokl` Forth `ha` New `ha` State `ha` Event `ha` push @List `ha` Labeled `ha` that `ha` shift (by Fore) `ha_` is `hu` x)
      `he'he'hv` Empty @List () `yi` that `ho` Forward
     `yi_` U_T_I_TT_I
    `yi__` U_T_I_TT_I `ho` T'TT'I
    `yo__` from

-- TODO: instance Scrollable (Construction (U_I_I P `T'TT'I` Optional)) item where

-- TODO: think about alternative implementations
-- TODO: refactor, it's really hard to read
-- TODO: this instance works incorrectly!
-- instance Mapping U_I_II U_I_II AR AR (List `T'TT'I` Cascading List) List where
--  mapping = rewrap / \from -> \case
--   T'TT'I (T'TT'I (U_I_II (This ())))
--    -> T'TT'I (U_I_II (This ()))
--   T'TT'I (T'TT'I (U_I_II (That (R_U_I_T_I (Recursive (U_I_T_II (These (Cascading (T'TT'I (U_I_II (This ())))) _)))))))
--    -> T'TT'I (U_I_II (This ()))
--   T'TT'I (T'TT'I (U_I_II (That (R_U_I_T_I (Recursive (U_I_T_II (These (Cascading (T'TT'I (U_I_II (That
--    (R_U_I_T_I (Recursive (U_I_T_II (These x xx)))))))) xxx)))))))
--    -> T'TT'I (U_I_II (That (R_U_I_T_I (Recursive (U_I_T_II (These (from x)
--      (fo @Arrow unwrap `compose` unwrap @Arrow / map @U_I_II @U_I_II @AR @AR @(List `T'TT'I` Cascading List) @List from
--       (T'TT'I (T'TT'I (U_I_II (That (R_U_I_T_I (Recursive (U_I_T_II (These (Cascading `ha` T'TT'I / xx `yo` R_U_I_T_I) xxx))))))))
--      )
--     ))))))

instance Mapping U_I_II U_I_II AR AR (Day U_I_II AR P P List ((Void `P` Void) `L` List) e ee) List where
 mapping = rewrap / \from -> rewrap / \case
  These (These e (Labeled ee)) (U_I_II f) ->
   (e `yokl` (\x -> Prior `ha` New `hv` (ee `yokl` (\xx -> Prior `ha` New `ha` State `ha` Event `hv` push @List (from (f (x `lu` xx)))))))
   `he'he'hv____` Empty @List Unit
   `yi______` that `ho` unwrap @AR

instance Mapping U_I_II U_I_II AR AR (Day U_I_II AR P P (Construction Optional) ((Void `P` Void) `L` (Construction Optional)) e ee) (Construction Optional) where
 mapping = rewrap / \from -> rewrap / \case
  These (These e (Labeled ee)) (U_I_II f) ->
   (e `yokl` (\x -> Prior `ha` New `hv` (ee `yokl` (\xx -> Prior `ha` New `ha` State `ha` Event `hv` push @List (from (f (x `lu` xx)))))))
   `he'he'hv____` Empty @List Unit
   `yi______` that `ho` (\r -> let (T'TT'I (U_I_II (That rr))) = r in rr) `ho` unwrap @AR

instance Mapping U_I_II U_I_II AR AR (List `T'TT'I` Void `L` List) List where
 mapping = rewrap / \from x -> unwrap x
  `yokl` Prior `ha` New `ha__'yokl` Prior `ha` New `ha` State `ha` Event `ha` push @List `ha` from `ha__` unwrap @AR `he'he'hv___` Empty @List Unit
  `yi__` that

instance Mapping U_I_II U_I_II AR AR (Construction Optional `T'TT'I` Void `L` Construction Optional) (Construction Optional) where
 mapping = rewrap / \from x -> let start = (unwrap (unwrap (unwrap (unwrap x)))) in
  that `hv` start
  `yokl` Run `ha` New
  `ha__'yokl` Prior `ha` New
   `ha_'yokl` Prior `ha` New `ha` State `ha` Event `ha` push @(Nonempty List) `ha` from
   `ha_` unwrap @AR @((Void `L` Nonempty List) _)
  `ha__` wrap @AR @(Nonempty List (Void `L` Nonempty List `T'I` _))
  `he'he'hv___` unwrap @AR @((Void `L` Nonempty List) _) `ha` this `hv` start `yo` from
  `yi__` that

instance Mapping U_I_II U_I_II AR AR (Construction Optional)
 (Construction Optional `T'TT'I` Unit `L` Construction Optional) where
 mapping = rewrap / \from x -> x
  `yukl` Forth `ha` New `ha` State `ha` Event `hv_` get `ha` that `ha` pop `he'he'hv___` x
  `yi__` this @(Nonempty List _) `ho'yo` (Labeled `ho'yo` from) `ho` wrap @AR

instance Mapping U_I_II U_I_II AR AR (Both P) (Construction Optional) where
 mapping = rewrap / \from -> rewrap / \(These x y) -> Item (from x) `ha` Next `ha` Item (from y) `ha` Last `hv` Unit

instance Mapping U_I_II U_I_II AR AR (Both P) List where
 mapping = rewrap / \from -> rewrap / \(These x y) -> Some `ha` Nonempty @List `ha` Item (from x) `ha` Next `ha` Item (from y) `ha` Last `hv` Unit

-- TODO: Add a label
-- instance Mapping U_I_II U_I_II AR AR (Construction Optional) (Construction Optional `T'TT'I` Construction Optional) where
 -- mapping = rewrap / \from -> \case
  -- R_U_I_T_I (Recursive (U_I_T_II (These e (U_I_II (This ()))))) ->
   -- T'TT'I `ha` R_U_I_T_I
    -- `li` Last (R_U_I_T_I (Recursive (U_I_T_II (These (from e) (U_I_II (This ()))))))
  -- R_U_I_T_I (Recursive (U_I_T_II (These e (U_I_II (That es))))) ->
   -- T'TT'I `ha` R_U_I_T_I
    -- `ha` Next (R_U_I_T_I (Recursive (U_I_T_II (These (from e) (U_I_II (That / unwrap (R_U_I_T_I es `yo` from)))))))
    -- `li` Last (map @U_I_II @U_I_II @AR @AR from (R_U_I_T_I es))

-- Define `Rewindable` typeclass, there should be instances for `Scrolling List`/`Sliding List`

type family Vector x xs where
 Vector x (y `P` xs) = (x ~ y, Vector x xs)
 Vector x y = x ~ y

-- This transformation is not natural!
instance (forall i . Setoid AR i) => Mapping U_II_I U_I_II AR AR I Predicate where
 mapping = rewrap / \from -> rewrap / \x x' -> is `hu` by False `la` Same `hu` by True `li` x `hd'q` from x'


