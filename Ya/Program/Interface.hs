{-# OPTIONS_GHC -fno-warn-orphans #-}
{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE UndecidableInstances #-}
module Ya.Program.Interface (module Exports, focus, shaft, pattern Aloft, pattern Stump, pattern Merge) where

import Ya.Algebra
import Ya.Operators
import Ya.Program.Patterns
import Ya.Program.Primitive
import Ya.Program.Labels

import Ya.Program.Interface.Fieldable as Exports
import Ya.Program.Interface.Matchable as Exports
import Ya.Program.Interface.Stackable as Exports
import Ya.Program.Interface.Shiftable as Exports
import Ya.Program.Interface.Keyable as Exports

instance
 ( Stackable tt
 , Covariant Endo Semi Functor (->) tt
 , Covariant Yoneda Functor (->) (->) t
 , forall e . Mapping T'I'II T'I'II (->) (->) (t `T'TT'I` State (tt e) `L` State (tt e) `T` Void `L` t `T` (Void `P` Void)) (t `TT'T'I` State (tt e))
 ) => Mapping T'I'II T'I'II (AR) (AR) ((T'TT'I'TTT'I (P) t tt) `L` tt `T` Void) tt where
 mapping = rewrap `identity` \from (Labeled (T'TT'I'TTT'I (These x xx))) ->
  x `yokl` Prior `ha` Apply `ha` State `ha` Event `ha` push
    `he'he'hv___` xx `yi__` that `ho'yo` from

pattern Merge :: forall t tt i .
 ( Stackable tt
 , Covariant Endo Semi Functor (->) tt
 , Covariant Endo Yoneda Functor (->) t
 , forall e . Mapping T'I'II T'I'II (->) (->) (t `T'TT'I` State (tt e) `L` State (tt e) `T` Void `L` t `T` (Void `P` Void)) (t `TT'T'I` State (tt e))
 ) =>
 t i `P` tt i `AR____` (T'TT'I'TTT'I (P) t tt) `L` tt `T` Void `T` i
pattern Merge x = Labeled (T'TT'I'TTT'I x)

instance Mapping T'I'II T'I'II (AR) (AR) (Shafted List) List where
 mapping = rewrap `identity` \from (T'TT'I'TTT'I (These (Labeled bs) (Labeled fs))) -> that
  (bs `yokl` Prior `ha` New `ha` State `ha` Event `ha` push @List `he'he'hv____` fs) `yo` from

instance Mapping T'I'II T'I'II (AR) (AR) List (Shafted List) where
 mapping = rewrap `identity` \from x -> T'TT'I'TTT'I (These (Labeled `hv` empty @List) (Labeled `hv__` x `yo` from))

instance Mapping T'I'II T'I'II (AR) (AR) (T'I'II (AR) Void) (Shafted List) where
 mapping = rewrap `identity` \_ _ -> T'TT'I'TTT'I (wrap empty `lu` wrap empty)

instance Mapping T'I'II T'I'II (AR) (AR) (Covariant Day (AR) (P) (S) (Shafted List) (Shafted List `L` Shafted List `T` Void) i ii) (Shafted List) where
 mapping = rewrap `identity` \from -> rewrap `identity` \(These (These i ii) (T'I'II f)) ->
  let These i' i'' = unwrap i in
  let These ii' ii'' = (unwrap `compose` unwrap) ii in
  (wrap (day @T'I'II @(AR) @Void @List @List @(P) @(S) identity (from `compose` f) (unwrap i' `lu` wrap (unwrap ii')))) `lu`
  (wrap (day @T'I'II @(AR) @Void @List @List @(P) @(S) identity (from `compose` f) (unwrap i' `lu` wrap (unwrap ii'))))

instance Mapping T'I'II T'I'II (AR) (AR) (Only `P'T'I'TT'I` Shafted List) ((Only `P'T'I'TT'I` Shafted List) `T'TT'I` (Only `P'T'I'TT'I` Shafted List) `L` (Only `P'T'I'TT'I` Shafted List) `T` Void) where
 mapping = rewrap `identity` \from x@(T'TT'I'TTT'I (These (Identity _) (T'TT'I'TTT'I (These rl fl)))) ->
  Identity `hv` Labeled x
   `lu__` (positions (x `lu` unwrap rl) `yi` that `ho` that `ho` Prior)
    `lu_` (positions (x `lu` unwrap fl) `yi` that `ho` that `ho` Forth)
    `yi_` T'TT'I'TTT'I
   `yi__` T'TT'I'TTT'I `ho` T'TT'I
   `yo__` from where

  positions :: forall item label .
   Scrolling List item `P` List item `AR__`
   List (Scrolling List `L` Scrolling List `T` Void `T` item) `P` (Scrolling List item `P` List (Scrolling List `L` Scrolling List `T` Void `T` item))
  positions (These x xs) = xs `yukl__` Forth `ha` New
   `hv____` State `hv__` Event `hv_` (shift (by Fore) `ho` that `ho` auto) `ha_` Scope `hv` at @(Scrolling List item)
   `yok_` New `ha` State `ha__` Event `ha` push @List `ha` Labeled `ho_'ha` Scope `hv` at @(List `T'I` Scrolling List `L` Scrolling List `T` Void `T` item)
   `he'he'hv______` x `lu` by `hv` Empty @List

instance Mapping T'I'II T'I'II Arrow Arrow (Construction List)
 ((Only `P'T'I'TT'I` Shafted List) `T'TT'I` Construction List `P'T'I'TT'I` (Reverse List `T'TT'I` (Only `P'T'I'TT'I` Shafted List `T'TT'I` Construction List))) where
  mapping = rewrap `identity` \from x -> T'TT'I'TTT'I
   (T'TT'I (T'TT'I'TTT'I ((Only `hv__` x `yo` from) `lu` T'TT'I'TTT'I (Prior `hv` Empty @List Unit `lu` Forth `hv` Empty @List Unit))) `lu` T'TT'I (Prior `hv` Empty @List Unit))

-- instance Mapping T'I'II T'I'II Arrow Arrow
 -- ((Only `P'T'I'TT'I` (Reverse List `P'T'I'TT'I` Forward List)) `T'TT'I` Construction List `P'T'I'TT'I` (Reverse List `T'TT'I` (Only `P'T'I'TT'I` (Reverse List `P'T'I'TT'I` Forward List) `T'TT'I` Construction List)))
 -- ((Only `P'T'I'TT'I` (Reverse List `P'T'I'TT'I` Forward List)) `T'TT'I` Construction List) where
 -- mapping = rewrap `identity` \from (T'TT'I'TTT'I (These sl xs)) ->
  -- T'TT'I `he` that ((unwrap xs `yokl` State `ha` Transition `ha_` restoring `ho'ho` (Unit `lu`)) `he_'he` unwrap sl) `yo` from where

   -- restoring (T'TT'I'TTT'I (These focus shafted)) scrolling_list_tree = T'TT'I'TTT'I
    -- `he__` Only (Tree `he` unwrap focus `he__` to @(Nonempty List) `he` scrolling_list_tree `yo` unwrap @(AR) `yi` unwrap @(AR))
     -- `lu` unwrap shafted

instance Mapping T'I'II T'I'II (AR) (AR) (Construction Optional) List where
 mapping = rewrap `identity` \from -> rewrap `li_` wrap `ho'yo` from `ho` Some

instance Mapping T'I'II T'I'II (AR) (AR) (Construction Optional) (List `P'T'I'TT'I` Shafted List) where
 mapping = rewrap `identity` \from x -> T'TT'I'TTT'I (Empty @List Unit `lu` T'TT'I'TTT'I (Prior `hv` Empty @List Unit `lu` Forth `ha` List `hv` unwrap x)) `yo` from

instance Mapping T'I'II T'I'II (AR) (AR) List (List `P'T'I'TT'I` Shafted List) where
 mapping = rewrap `identity` \from x -> T'TT'I'TTT'I (Empty @List Unit `lu` T'TT'I'TTT'I (Prior `hv` Empty @List Unit `lu` Forth `hv` x)) `yo` from

instance Mapping T'I'II T'I'II (AR) (AR) (List `P'T'I'TT'I` Shafted List) List where
 mapping = rewrap `identity` \from (T'TT'I'TTT'I (These w (T'TT'I'TTT'I (These (Labeled r) (Labeled f))))) ->
  that `ho'yo` from
  `hv_____` intro @(State `T'I` List _) Unit
    `yuk__` New (f `yokl` Prior `ha` New `ha` State `ha` Event `ha` push @List)
    `yuk__` New (w `yokl` Prior `ha` New `ha` State `ha` Event `ha` push @List)
    `yuk__` New (r `yokl` Forth `ha` New `ha` State `ha` Event `ha` push @List)
  `he'he'hv____` Empty @List Unit

instance Mapping T'I'II T'I'II (AR) (AR) (Only `P'T'I'TT'I` Shafted List) (List `P'T'I'TT'I` Shafted List) where
 mapping = rewrap `identity` \from -> rewrap `identity` \x -> x
  `yoi` is `he'ho` (\i -> List `ha` Item (from i) `ha` Last `hv` Unit)
  `yio'yo` from

instance Mapping T'I'II T'I'II (AR) (AR) (Only `P'T'I'TT'I` Shafted List)
 ((Only `P'T'I'TT'I` Shafted List) `T'TT'I` Tree `P'T'I'TT'I` Reverse List `T'TT'I` (Only `P'T'I'TT'I` Shafted List `T'TT'I` Tree)) where
 mapping = rewrap `identity` \from x -> x `yo` from `ho` intro @Tree @(AR) `yi` wrap @(AR) `lu` by (wrap @(AR) `ha` Prior `ha` Empty @List) `yi` wrap @(AR)

-- TODO: check this instance, I'm not sure it works correctly
instance
 ( Covariant Endo Semi Functor (AR) t
 , Covariant Endo Semi Functor (AR) tt
 , Covariant Lax Monoidal Functor (AR) (AR) (P) P Void tttt
 , Covariant Endo Transformation Functor (AR) (t `T'TT'I` tttt `L` tttt `T` ll `L` t `T` Void) (t `TT'T'I` tttt)
 , Covariant Endo Transformation Functor (AR) (tt `T'TT'I` tttt `L` tttt `T` ll `L` tt `T` Void) (tt `TT'T'I` tttt)
 , Covariant Endo Transformation Functor (AR) (tt `T'TT'I` tttt `L` tttt `T` ll `L` tt `T` (Void `P` Void)) (tt `TT'T'I` tttt)
 ) => Mapping T'I'II T'I'II (AR) (AR) ((t `P'T'I'TT'I` Shafted tt) `T'TT'I` tttt `L` tttt `T` ll `L` (t `P'T'I'TT'I` Shafted tt) `T` Void) ((t `P'T'I'TT'I` Shafted tt) `TT'T'I` tttt) where
  mapping = rewrap `identity` \from -> rewrap `identity` \(T'TT'I'TTT'I (These w (T'TT'I'TTT'I (These (Labeled r) (Labeled f))))) ->
            (r `yokl` rewrap @(tttt `L` tttt `T` ll `L` tt `T` (Void `P` Void) `T` _) is)
   `lu'yp` Run (w `yokl` rewrap @(tttt `L` tttt `T` ll `L` t `T` Void `T` _) is)
   `lu'yp` Run (f `yokl` rewrap @(tttt `L` tttt `T` ll `L` tt `T` Void `T` _) is)
     `yo` (\(These (These sx x) xs) -> T'TT'I'TTT'I ((x `yo` from) `lu` (T'TT'I'TTT'I (
      (Labeled (sx `yo` from)) `lu_` (Labeled (xs `yo` from))))))

instance
 ( Covariant Endo Semi Functor (AR) t
 , Covariant Endo Semi Functor (AR) tt
 , Covariant Lax Monoidal Functor (AR) (AR) (P) P Void tttt
 , Covariant Endo Transformation Functor (AR) (t `T'TT'I` tttt `L` tttt `T` ll `L` t `T` (Void `P` Void)) (t `TT'T'I` tttt)
 , Covariant Endo Transformation Functor (AR) (tt `T'TT'I` tttt `L` tttt `T` ll `L` tt `T` Void) (tt `TT'T'I` tttt)
 , Covariant Endo Transformation Functor (AR) (tt `T'TT'I` tttt `L` tttt `T` ll `L` tt `T` (Void `P` Void)) (tt `TT'T'I` tttt)
 ) => Mapping T'I'II T'I'II (AR) (AR) ((t `P'T'I'TT'I` Shafted tt) `T'TT'I` tttt `L` tttt `T` ll `L` (t `P'T'I'TT'I` Shafted tt) `T` (Void `P` Void)) ((t `P'T'I'TT'I` Shafted tt) `TT'T'I` tttt) where
  mapping = rewrap `identity` \from -> rewrap `identity` \(T'TT'I'TTT'I (These w (T'TT'I'TTT'I (These (Labeled r) (Labeled f))))) ->
            (f `yokl` rewrap @(tttt `L` tttt `T` ll `L` tt `T` (Void `P` Void) `T` _) is)
   `lu'yp` Run (w `yokl` rewrap @(tttt `L` tttt `T` ll `L` t `T` (Void `P` Void) `T` _) is)
   `lu'yp` Run (r `yokl` rewrap @(tttt `L` tttt `T` ll `L` tt `T` Void `T` _) is)
     `yo` (\(These (These sx x) xs) -> T'TT'I'TTT'I ((x `yo` from) `lu` (T'TT'I'TTT'I (
      (Labeled (sx `yo` from)) `lu_` (Labeled (xs `yo` from))))))

instance
 ( Covariant Endo Semi Functor (AR) tt
 , Covariant Lax Monoidal Functor (AR) (AR) (P) P Void ttt
 , Covariant Endo Transformation Functor (AR) (tt `T'TT'I` ttt `L` ttt `T` ll `L` tt `T` Void) (tt `TT'T'I` ttt)
 , Covariant Endo Transformation Functor (AR) (tt `T'TT'I` ttt `L` ttt `T` ll `L` tt `T` (Void `P` Void)) (tt `TT'T'I` ttt)
 ) => Mapping T'I'II T'I'II (AR) (AR) (Shafted tt `T'TT'I` ttt `L` ttt `T` ll `L` Shafted tt `T` Void) (Shafted tt `TT'T'I` ttt) where
  mapping = rewrap `identity` \from -> rewrap `identity` \(T'TT'I'TTT'I (These (Labeled r) (Labeled f))) ->
            (r `yokl` rewrap @(ttt `L` ttt `T` ll `L` tt `T` (Void `P` Void) `T` _) is)
   `lu'yp` Run (f `yokl` rewrap @(ttt `L` ttt `T` ll `L` tt `T` Void `T` _) is)
     `yo` (\(These sx xs) -> T'TT'I'TTT'I (These (Labeled @_ @_ @(Void `P` Void) (sx `yo` from)) (Labeled @_ @_ @Void (xs `yo` from))))

instance
 ( Covariant Endo Semi Functor (AR) tt
 , Covariant Lax Monoidal Functor (AR) (AR) (P) P Void ttt
 , Covariant Endo Transformation Functor (AR) (tt `T'TT'I` ttt `L` ttt `T` ll `L` tt `T` Void) (tt `TT'T'I` ttt)
 , Covariant Endo Transformation Functor (AR) (tt `T'TT'I` ttt `L` ttt `T` ll `L` tt `T` (Void `P` Void)) (tt `TT'T'I` ttt)
 ) => Mapping T'I'II T'I'II (AR) (AR) (Shafted tt `T'TT'I` ttt `L` ttt `T` ll `L` Shafted tt `T` (Void `P` Void)) (Shafted tt `TT'T'I` ttt) where
  mapping = rewrap `identity` \from -> rewrap `identity` \(T'TT'I'TTT'I (These (Labeled r) (Labeled f))) ->
            (f `yokl` rewrap @(ttt `L` ttt `T` ll `L` tt `T` (Void `P` Void) `T` _) is)
   `lu'yp` Run (r `yokl` rewrap @(ttt `L` ttt `T` ll `L` tt `T` Void `T` _) is)
     `yo` (\(These sx xs) -> T'TT'I'TTT'I (These (Labeled @_ @_ @(Void `P` Void) (sx `yo` from)) (Labeled @_ @_ @Void (xs `yo` from))))

-- instance
--  ( Covariant Endo Semi Functor (AR) t
--  -- , Covariant Endo Semi Functor (AR) tt
--  -- , Covariant Endo Semi Functor (AR) ttt
--  -- , Covariant Endo Monoidal Functor (AR) (P) P tttt
--  -- , Covariant Endo Transformation Functor (AR) (t `T'TT'I` t `L` t `T` Void `L` lltt) (t `TT'T'I` tttt)
--  -- , Covariant Endo Transformation Functor (AR) (tt `T'TT'I` t `L` t `T` Void `L` lltt) (tt `TT'T'I` tttt)
--  -- , Covariant Endo Transformation Functor (AR) (ttt `T'TT'I` t `L` t `T` Void `L` lltt) (ttt `TT'T'I` tttt)
--  ) => Mapping T'I'II T'I'II (AR) (AR)
--  (((t `P'T'I'TT'I` Shafted List) `T'TT'I` Tree `P'T'I'TT'I` Reverse List `T'TT'I` (t `P'T'I'TT'I` Shafted List `T'TT'I` Tree)) `T'TT'I` ttt `L` ll `L` Void)
--  (((t `P'T'I'TT'I` Shafted List) `T'TT'I` Tree `P'T'I'TT'I` Stacked Only Tree List) `TT'T'I` tttt)  where
  -- mapping = rewrap `identity` \from -> rewrap `identity`
  --  \(T'TT'I'TTT'I (These (T'TT'I'TTT'I (These w (T'TT'I'TTT'I (These (Labeled r) (Labeled f))))) (Labeled passed))) ->
  --  ()

-- TODO: we are going to apply the same function to all items in a list but it's actually fine
instance Mapping T'I'II T'I'II (AR) (AR) (List `P'T'I'TT'I` Shafted List) ((List `P'T'I'TT'I` Shafted List) `T'TT'I` (List `P'T'I'TT'I` Shafted List) `L` (List `P'T'I'TT'I` Shafted List) `T` Void) where
 mapping = rewrap `identity` \from x@(T'TT'I'TTT'I (These _ (T'TT'I'TTT'I (These rl fl)))) ->
  List `ha` Item (Labeled x) `ha` Last `hv` Unit
    `lu__` (unwrap rl `yokl` Prior `ha` New `ha` State `ha` Event `ha` push @List `ha` Labeled `ha` that `ha` shift (by Back) `ha_` is `hu` x)
      `he'he'hv` Empty @List () `yi` that `ho` Prior
     `lu_` (unwrap fl `yokl` Forth `ha` New `ha` State `ha` Event `ha` push @List `ha` Labeled `ha` that `ha` shift (by Fore) `ha_` is `hu` x)
      `he'he'hv` Empty @List () `yi` that `ho` Forth
     `yi_` T'TT'I'TTT'I
    `yi__` T'TT'I'TTT'I `ho` T'TT'I
    `yo__` from

-- TODO: instance Scrollable (Construction (T'I'I (P) `T'TT'I` Optional)) item where

-- TODO: think about alternative implementations
-- TODO: refactor, it's really hard to read
-- TODO: this instance works incorrectly!
-- instance Mapping T'I'II T'I'II (AR) (AR) (List `T'TT'I` Cascading List) List where
--  mapping = rewrap `identity` \from -> \case
--   T'TT'I (T'TT'I (T'I'II (This ())))
--    -> T'TT'I (T'I'II (This ()))
--   T'TT'I (T'TT'I (T'I'II (That (R_U_I_T_I (Recursive (T'I'TT'II (These (Cascading (T'TT'I (T'I'II (This ())))) _)))))))
--    -> T'TT'I (T'I'II (This ()))
--   T'TT'I (T'TT'I (T'I'II (That (R_U_I_T_I (Recursive (T'I'TT'II (These (Cascading (T'TT'I (T'I'II (That
--    (R_U_I_T_I (Recursive (T'I'TT'II (These x xx)))))))) xxx)))))))
--    -> T'TT'I (T'I'II (That (R_U_I_T_I (Recursive (T'I'TT'II (These (from x)
--      (fo @Arrow unwrap `compose` unwrap @Arrow `identity` map @T'I'II @T'I'II @(AR) @(AR) @(List `T'TT'I` Cascading List) @List from
--       (T'TT'I (T'TT'I (T'I'II (That (R_U_I_T_I (Recursive (T'I'TT'II (These (Cascading `ha` T'TT'I `identity` xx `yo` R_U_I_T_I) xxx))))))))
--      )
--     ))))))

instance Mapping T'I'II T'I'II (AR) (AR)
 (Covariant Day (AR) (P) P List (List `L` List `T` (Void `P` Void)) e ee) List where
 mapping = rewrap `identity` \from -> rewrap `identity` \case
  These (These e ee) (T'I'II f) ->
   e `yokl` (\x -> Prior `ha` New `hv` (unwrap ee `yokl` (\xx -> Prior `ha` New `ha` State `ha` Event `hv` push @List (from (f (x `lu` xx))))))
   `he'he'hv____` Empty @List Unit
   `yi______` that `ho` unwrap @(AR)

instance Mapping T'I'II T'I'II (AR) (AR) (Covariant Day (AR) (P) P (Construction Optional) (Construction Optional `L` Construction Optional `T` (Void `P` Void)) e ee) (Construction Optional) where
 mapping = rewrap `identity` \from -> rewrap `identity` \case
  These (These e (Labeled ee)) (T'I'II f) ->
   (e `yokl` (\x -> Prior `ha` New `hv` (ee `yokl` (\xx -> Prior `ha` New `ha` State `ha` Event `hv` push @List (from (f (x `lu` xx)))))))
   `he'he'hv____` Empty @List Unit
   `yi______` that `ho` (\r -> let (T'TT'I (T'I'II (That rr))) = r in rr) `ho` unwrap @(AR)

instance Mapping T'I'II T'I'II (AR) (AR) (List `T'TT'I` List `L` List `T` Void) List where
 mapping = rewrap `identity` \from x -> unwrap x
  `yokl` Prior `ha` New `ha__'yokl` Prior `ha` New `ha` State `ha` Event `ha` push @List `ha` from `ha__` unwrap @(AR) `he'he'hv___` Empty @List Unit
  `yi__` that

instance Mapping T'I'II T'I'II (AR) (AR) (List `T'TT'I` List `L` List `T` (Void `P` Void)) List where
 mapping = rewrap `identity` \from x -> unwrap x
  `yokl` Prior `ha` Run
  `ha__` intro @(Halts `JNT` State `T'I` List _) @(AR)
   `ho_'yok` Try `ha'he'he` is @(Maybe (Nonempty List _))
   `ho_'yok` New `ha` (\xx -> xx `yokl` Prior `ha` New `ha` State `ha` Event `ha` push @List `ha` from)
  `he'he'hv___` empty @List
  `yi__` Empty @List `la` is `ho'he` that @(List _)

instance Mapping T'I'II T'I'II (AR) (AR) (List `T'TT'I` S'I'II i `L` S'I'II i `T` Void) List where
 mapping = rewrap `identity` \from x -> unwrap x
  `yokl` Prior `ha` Apply `ha` State `ha` Event
  `ha__` Error `hu` auto `la` push @List `ho'ho` (auto `ha` that) `ha` from
  `he'he'hv___` Empty @List Unit
  `yi__` that

instance Mapping T'I'II T'I'II (AR) (AR) (Construction Optional `T'TT'I` Construction Optional `L` Construction Optional `T` Void) (Construction Optional) where
 mapping = rewrap `identity` \from x -> let start = (unwrap (unwrap (unwrap (unwrap x)))) in
  that `hv` start
  `yokl` Run `ha` New
  `ha__'yokl` Prior `ha` New
   `ha_'yokl` Prior `ha` New `ha` State `ha` Event `ha` push @(Nonempty List) `ha` from
   `ha_` unwrap @(AR) @(Nonempty List `L` Nonempty List `T` Void `T` _)
  `ha__` wrap @(AR) @(Nonempty List (Nonempty List `L` Nonempty List `T` Void `T` _))
  `he'he'hv___` unwrap @(AR) @(Nonempty List `L` Nonempty List `T` Void `T` _) `ha` this `hv` start `yo` from
  `yi__` that

instance Mapping T'I'II T'I'II (AR) (AR) (Construction Optional)
 (Construction Optional `T'TT'I` Construction Optional `L` Construction Optional `T` Void) where
 mapping = rewrap `identity` \from x -> x
  `yukl` Forth `ha` New `ha` State `ha` Event `hv_` (\old -> pop old `yui` old) `he'he'hv___` x
  -- `yukl` Forth `ha` New `ha` State `ha` Event `hv_` (get `ha` that `ha` pop) `he'he'hv___` x
  `yi__` this @(Nonempty List _) `ho'yo` (Labeled `ho'yo` from) `ho` wrap @(AR) where

instance Mapping T'I'II T'I'II (AR) (AR) (Construction Optional)
 (Construction Optional `T'TT'I` (Only `P'T'I'TT'I` Shafted List) `L` (Only `P'T'I'TT'I` Shafted List) `T` Void) where
 mapping = rewrap `identity` \from x -> x
  `yi_` to @(Scrolling List)
  `kyo` Range `ha` wrap @(AR) @(Scrolling List `L` Scrolling List `T` Void `T` _) `ha'yo` from
  `yi_` to @(Nonempty List) `ho` wrap @(AR)

instance Mapping T'I'II T'I'II (AR) (AR) List
 (List `T'TT'I` (Only `P'T'I'TT'I` Shafted List) `L` (Only `P'T'I'TT'I` Shafted List) `T` Void) where
 mapping = rewrap `identity` \from -> wrap @(AR) @(List `T'TT'I` Scrolling List `L` Scrolling List `T` Void `T'I_` _)
  `ha__` Empty @List `hu` Empty @List Unit
    `la` map @T'I'II @T'I'II @(AR) @(AR) @(Nonempty List) @(Nonempty List `T'TT'I` Scrolling List `L` Scrolling List `T` Void) from `ho'he` to @List

instance Mapping T'I'II T'I'II (AR) (AR) (Both (P)) (Construction Optional) where
 mapping = rewrap `identity` \from -> rewrap `identity` \(These x y) -> Item (from x) `ha` Next `ha` Item (from y) `ha` Last `hv` Unit

instance Mapping T'I'II T'I'II (AR) (AR) (Both (P)) List where
 mapping = rewrap `identity` \from -> rewrap `identity` \(These x y) -> Some `ha` Nonempty @List `ha` Item (from x) `ha` Next `ha` Item (from y) `ha` Last `hv` Unit

-- TODO: Add a label
-- instance Mapping T'I'II T'I'II (AR) (AR) (Construction Optional) (Construction Optional `T'TT'I` Construction Optional) where
 -- mapping = rewrap `identity` \from -> \case
  -- R_U_I_T_I (Recursive (T'I'TT'II (These e (T'I'II (This ()))))) ->
   -- T'TT'I `ha` R_U_I_T_I
    -- `li` Last (R_U_I_T_I (Recursive (T'I'TT'II (These (from e) (T'I'II (This ()))))))
  -- R_U_I_T_I (Recursive (T'I'TT'II (These e (T'I'II (That es))))) ->
   -- T'TT'I `ha` R_U_I_T_I
    -- `ha` Next (R_U_I_T_I (Recursive (T'I'TT'II (These (from e) (T'I'II (That `identity` unwrap (R_U_I_T_I es `yo` from)))))))
    -- `li` Last (map @T'I'II @T'I'II @(AR) @(AR) from (R_U_I_T_I es))

-- Define `Rewindable` typeclass, there should be instances for `Scrolling List``identity``Sliding List`

type family Vector x xs where
 Vector x (y `P` xs) = (x ~ y, Vector x xs)
 Vector x y = x ~ y

-- This transformation is not natural!
instance (forall i . Setoid (AR) i) => Mapping T'II'I T'I'II (AR) (AR) I Predicate where
 mapping = rewrap `identity` \from -> rewrap `identity` \x x' -> is `hu` by False `la` Same `hu` by True `li_` x `lu'q` from x'

pattern Aloft :: forall t e .
 Component (AR) (((Only `P'T'I'TT'I` Shafted List) `P'T'I'TT'I` Tree) `L` ((Only `P'T'I'TT'I` Shafted List) `P'T'I'TT'I` Tree) `T` Void) Tree =>
 (t `P'T'I'TT'I` Tree) e `AR___` (t `P'T'I'TT'I` Tree) `L` (t `P'T'I'TT'I` Tree) `T` Void `T` e
pattern Aloft x = Labeled x

instance Mapping T'I'II T'I'II Arrow Arrow (((Only `P'T'I'TT'I` Shafted List) `P'T'I'TT'I` Tree) `L` ((Only `P'T'I'TT'I` Shafted List) `P'T'I'TT'I` Tree) `T` Void) Tree where
  mapping = rewrap `identity` \from (Labeled (T'TT'I'TTT'I (These scrolling_list tree))) ->
   rewrap (\x -> Only tree `lu` that @(Shafted List _) `ho'yo` intro @Tree @(AR) `hv` x) scrolling_list
    `yi` is @(Scrolling List _) `ho` to @(Nonempty List) `ho` to @List `ho'yo` unwrap @(AR)
    `yi` this @(Only _) `ho'he` Root `hv` unwrap scrolling_list
    `yo` from

pattern Stump :: forall i e .
 Component (AR) (S'I'II i) (S'I'II Unit) =>
 S'I'II i e `AR__` S'I'II i `L` S'I'II i `T` Void `T` e
pattern Stump x = Labeled x

instance Mapping T'I'II T'I'II (AR) (AR) (S'I'II e `L` S'I'II e `T` Void) (S'I'II Unit) where
 mapping = rewrap `identity` \from ->
  rewrap `identity` ((This `compose` constant Unit `la` That `compose` from) `compose` unwrap)

instance Semigroup (AR) Boolean where
 s (These x y) = x `lu'ys'la` Try y

instance Quasigroup (AR) Boolean where
 p (These x y) = x `lu'yp` Try `hv` y `yu` Unit

instance Semigroup (AR) (List item) where
 s (These x y) = x `yokl` Prior `ha` New `ha` State `ha` Event `ha` push `he'he'hv___` y `yi__` that

instance Semigroup (AR) (Construction Maybe item) where
 s (These x y) = x `yokl` Prior `ha` New `ha` State `ha` Event `ha` push `he'he'hv___` y `yi__` that
