{-# OPTIONS_GHC -fno-warn-orphans #-}
{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE UndecidableInstances #-}
module Ya.Program.Interface (module Exports, focus, shaft) where

import Ya.Algebra
import Ya.Program.Patterns
import Ya.Program.Primitive
import Ya.Program.Labels

import Ya.Program.Interface.Field as Exports
import Ya.Program.Interface.Match as Exports
import Ya.Program.Interface.Stackable as Exports
import Ya.Program.Interface.Shiftable as Exports

instance Mappings U_I_II U_I_II AR AR (Shafted List) List where
 mapping = rewrap / \from (U_T_I_TT_I (These (Labeled bs) (Labeled fs))) -> that
  (bs `yokl` Prior `ha` New `ha` State `ha` Event `ha` push @List `he'he'hv____` fs) `yo` from

instance Mappings U_I_II U_I_II AR AR (U_I_II AR Void) (Shafted List) where
 mapping = rewrap / \_ _ -> U_T_I_TT_I (wrap empty `lu` wrap empty)

instance Mappings U_I_II U_I_II AR AR (Day U_I_II AR P S (Shafted List) (Shafted List) i ii) (Shafted List) where
 mapping = rewrap / \from -> rewrap / \(These (These i ii) (U_I_II f)) ->
  let These i' i'' = unwrap i in
  let These ii' ii'' = unwrap ii in
  (wrap (day @U_I_II @AR @List @P @S identity (from `compose` f) (unwrap i' `lu` unwrap ii'))) `lu`
  (wrap (day @U_I_II @AR @List @P @S identity (from `compose` f) (unwrap i' `lu` unwrap ii')))

instance Mappings U_I_II U_I_II AR AR (Only `P'T'I'TT'I` Shafted List) ((Only `P'T'I'TT'I` Shafted List) `T'TT'I` Unit `L` (Only `P'T'I'TT'I` Shafted List)) where
 mapping = rewrap / \from x@(U_T_I_TT_I (These (Identity _) (U_T_I_TT_I (These rl fl)))) ->
  Identity `hv` Labeled x
   `lu__` (positions (x `lu` unwrap rl) `yi` that `ho` that `ho` Reverse)
    `lu_` (positions (x `lu` unwrap fl) `yi` that `ho` that `ho` Forward)
    `yi_` U_T_I_TT_I
   `yi__` U_T_I_TT_I `ho` T'TT'I
   `yo__` from where

  positions :: forall item label .
   Scrolling List item `P` List item `AR__`
   List (Unit `L` Scrolling List `WR` item) `P` (Scrolling List item `P` List ((Unit `L` Scrolling List) item))
  positions (These x xs) = xs `yukl__` Forth `ha` New
   `hv____` State `hv__` Event `hv_` (shift (by Fore) `ho` that `ho` auto) `ha_` Scope `hv` at @(Scrolling List item)
   `yok_` New `ha` State `ha__` Event `ha` push @List `ha` Labeled `ho_'ha` Scope `hv` at @(List `WR` (Unit `L` Scrolling List) item)
   `he'he'hv______` x `lu` by `hv` Empty @List

instance Mappings U_I_II U_I_II Arrow Arrow (Construction List)
 ((Only `P'T'I'TT'I` Shafted List) `T'TT'I` Construction List `P'T'I'TT'I` (Reverse List `T'TT'I` (Only `P'T'I'TT'I` Shafted List `T'TT'I` Construction List))) where
  mapping = rewrap / \from x -> U_T_I_TT_I
   (T'TT'I (U_T_I_TT_I ((Only `hv__` x `yo` from) `lu` U_T_I_TT_I (Reverse `hv` Empty @List Unit `lu`Forward `hv` Empty @List Unit))) `lu` T'TT'I (Reverse `hv` Empty @List Unit))

-- instance Mappings U_I_II U_I_II Arrow Arrow
 -- ((Only `P'T'I'TT'I` (Reverse List `P'T'I'TT'I` Forward List)) `T'TT'I` Construction List `P'T'I'TT'I` (Reverse List `T'TT'I` (Only `P'T'I'TT'I` (Reverse List `P'T'I'TT'I` Forward List) `T'TT'I` Construction List)))
 -- ((Only `P'T'I'TT'I` (Reverse List `P'T'I'TT'I` Forward List)) `T'TT'I` Construction List) where
 -- mapping = rewrap / \from (U_T_I_TT_I (These sl xs)) ->
  -- T'TT'I `he` that ((unwrap xs `yokl` State `ha` Transition `ha_` restoring `ho'ho` (Unit `lu`)) `he_'he` unwrap sl) `yo` from where

   -- restoring (U_T_I_TT_I (These focus shafted)) scrolling_list_tree = U_T_I_TT_I
    -- `he__` Only (Tree `he` unwrap focus `he__` to @(Nonempty List) `he` scrolling_list_tree `yo` unwrap @AR `yi` unwrap @AR)
     -- `lu` unwrap shafted

instance Mappings U_I_II U_I_II AR AR (Construction Optional) List where
 mapping = rewrap / \from -> rewrap / wrap `ho'yo` from `ho` Some

instance Mappings U_I_II U_I_II AR AR (Construction Optional) (List `P'T'I'TT'I` Shafted List) where
 mapping = rewrap / \from x -> U_T_I_TT_I (Empty @List Unit `lu` U_T_I_TT_I (Reverse `hv` Empty @List Unit `lu` Forward `ha` List `hv` unwrap x)) `yo` from

instance Mappings U_I_II U_I_II AR AR List (List `P'T'I'TT'I` Shafted List) where
 mapping = rewrap / \from x -> U_T_I_TT_I (Empty @List Unit `lu` U_T_I_TT_I (Reverse `hv` Empty @List Unit `lu` Forward `hv` x)) `yo` from

instance Mappings U_I_II U_I_II AR AR (List `P'T'I'TT'I` Shafted List) List where
 mapping = rewrap / \from (U_T_I_TT_I (These w (U_T_I_TT_I (These (Labeled r) (Labeled f))))) ->
  that `ho'yo` from
  `hv_____` enter @(State `WR` List _)
    `yuk__` New (f `yokl` Prior `ha` New `ha` State `ha` Event `ha` push @List)
    `yuk__` New (w `yokl` Prior `ha` New `ha` State `ha` Event `ha` push @List)
    `yuk__` New (r `yokl` Forth `ha` New `ha` State `ha` Event `ha` push @List)
  `he'he'hv____` Empty @List Unit

instance Mappings U_I_II U_I_II AR AR (Only `P'T'I'TT'I` Shafted List) (List `P'T'I'TT'I` Shafted List) where
 mapping = rewrap / \from -> rewrap / \x -> x
  `yoi` is `he'ho` (\i -> List `ha` Item (from i) `ha` Last `hv` Unit)
  `yio'yo` from

instance Mappings U_I_II U_I_II AR AR (Only `P'T'I'TT'I` Shafted List)
 ((Only `P'T'I'TT'I` Shafted List) `T'TT'I` Tree `P'T'I'TT'I` Reverse List `T'TT'I` (Only `P'T'I'TT'I` Shafted List `T'TT'I` Tree)) where
 mapping = rewrap / \from x -> x `yo` from `ho` intro @Tree `yi` wrap @AR `lu` by (wrap @AR `ha` Reverse `ha` Empty @List) `yi` wrap @AR

-- TODO
instance Mappings U_I_II U_I_II AR AR
 ((t `P'T'I'TT'I` (Reverse tt `P'T'I'TT'I` Forward ttt)) `T'TT'I` l `L` ll `L` tttt)
 ((t `P'T'I'TT'I` (Reverse tt `P'T'I'TT'I` Forward ttt)) `TT'T'I` tttt)
 where
  -- mapping = rewrap / \from -> rewrap / \(U_T_I_TT_I (These w (U_T_I_TT_I (These (Labeled r) (Labeled f))))) ->
   -- (wrapped (map @U_I_II @U_I_II @AR @AR @(t `T'TT'I` L l (L ll tttt)) @(t `TT'T'I` tttt) from) w :: _)

-- TODO: we are going to apply the same function to all items in a list but it's actually fine
instance Mappings U_I_II U_I_II AR AR (List `P'T'I'TT'I` Shafted List) ((List `P'T'I'TT'I` Shafted List) `T'TT'I` Unit `L` (List `P'T'I'TT'I` Shafted List)) where
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
instance Mappings U_I_II U_I_II AR AR (List `T'TT'I` Cascading List) List where
 mapping = rewrap / \from -> \case
  T'TT'I (T'TT'I (U_I_II (This ())))
   -> T'TT'I (U_I_II (This ()))
  T'TT'I (T'TT'I (U_I_II (That (R_U_I_T_I (Recursive (U_I_T_II (These (Cascading (T'TT'I (U_I_II (This ())))) _)))))))
   -> T'TT'I (U_I_II (This ()))
  T'TT'I (T'TT'I (U_I_II (That (R_U_I_T_I (Recursive (U_I_T_II (These (Cascading (T'TT'I (U_I_II (That
   (R_U_I_T_I (Recursive (U_I_T_II (These x xx)))))))) xxx)))))))
   -> T'TT'I (U_I_II (That (R_U_I_T_I (Recursive (U_I_T_II (These (from x)
     (fo @Arrow unwrap `compose` unwrap @Arrow / map @U_I_II @U_I_II @AR @AR @(List `T'TT'I` Cascading List) @List from
      (T'TT'I (T'TT'I (U_I_II (That (R_U_I_T_I (Recursive (U_I_T_II (These (Cascading `ha` T'TT'I / xx `yo` R_U_I_T_I) xxx))))))))
     )
    ))))))

-- TODO: Add a label
-- instance Mappings U_I_II U_I_II AR AR (Construction Optional) (Construction Optional `T'TT'I` Construction Optional) where
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
instance (forall i . Setoid AR i) => Mappings U_II_I U_I_II AR AR I Predicate where
 mapping = rewrap / \from -> rewrap / \x x' -> is `hu` by False `la` Same `hu` by True `li` x `hd'q` from x'


