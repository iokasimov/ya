{-# OPTIONS_GHC -fno-warn-orphans #-}
{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE UndecidableInstances #-}
module Ya.Program.Interface (module Exports, pattern Aloft, pattern Spare) where

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
import Ya.Program.Interface.Instances as Exports

instance Mapping T'I'II T'I'II (AR) (AR) (T'I'II (AR) Void) (Twice `T'TT'I` List) where
 mapping = rewrap `hc` \_ _ -> empty `hjd` empty

instance Mapping T'I'II T'I'II (AR) (AR)
 (Covariant Day (AR) (P) (S) (Twice `T'TT'I` List) ((Twice `T'TT'I` List) `L` (Twice `T'TT'I` List) `T` Void) i ii) (Twice `T'TT'I` List) where
 mapping = rewrap `hc` \source -> rewrap `hc` \(These (These i ii) (T'I'II f)) ->
  let These i' i'' = super `compose` super `identity` i in
  let These ii' ii'' = super `compose` super `compose` super `identity` ii in
  (day @T'I'II @(AR) @Void @List @List @(P) @(S) identity (source `compose` f) (i' `hjd` wrap ii')) `hjd`
  (day @T'I'II @(AR) @Void @List @List @(P) @(S) identity (source `compose` f) (i'' `hjd` wrap ii''))

instance {-# OVERLAPS #-} Mapping T'I'II T'I'II (AR) (AR) (I `P'T'I'TT'I` Twice `T'TT'I` List) ((I `P'T'I'TT'I` Twice `T'TT'I` List) `T'TT'I` (I `P'T'I'TT'I` Twice `T'TT'I` List) `L` (I `P'T'I'TT'I` Twice `T'TT'I` List) `T` Void) where
 mapping = rewrap `hc` \source x@(T'TT'I'TTT'I (These (Identity _) (T'TT'I (T'I'I (These rl fl))))) ->
  Identity `hc` Label x
   `hjd__` positions (x `hjd` rl) `yv` that `ho` that
    `hjd_` positions (x `hjd` fl) `yv` that `ho` that
    `yv_` T'TT'I `ha` T'I'I
   `yv__` T'TT'I'TTT'I `ho` T'TT'I
   `yo__` source where

  positions :: forall item label .
   Scrolling List item `P` List item `AR__`
   List (Scrolling List `L` Scrolling List `T` Void `T` item) `P` (Scrolling List item `P` List (Scrolling List `L` Scrolling List `T` Void `T` item))
  positions (These x xs) = xs
   `yukl__` Forth `ha` Apply
   `hc____` State `hc__` Event `hc_` (shift `hc'st` Fore `ho` that `ho` fetch) `ha_` Scope `hc` at @(Scrolling List item)
   `yok_` Apply `ha` State `ha__` Event `ha` push @List `ha` Label `ho_'ha` Scope `hc` at @(List `T'I` Scrolling List `L` Scrolling List `T` Void `T` item)
   `hc______` x `hjd` empty @List

instance Mapping T'I'II T'I'II (AR) (AR) (Construction List)
 ((Alone `P'T'I'TT'I` Twice `T'TT'I` List) `T'TT'I` Construction List `P'T'I'TT'I` (Reverse List `T'TT'I` (Alone `P'T'I'TT'I` Twice `T'TT'I` List `T'TT'I` Construction List))) where
  mapping = rewrap `hc` \source x -> T'TT'I'TTT'I
   (T'TT'I (T'TT'I'TTT'I ((x `yo` source `yv` Alone) `hjd` T'TT'I (T'I'I (empty @List `hjd` empty @List)))) `hjd` T'TT'I (Label `hc` empty @List))

-- instance Mapping T'I'II T'I'II Arrow Arrow
 -- ((Alone `P'T'I'TT'I` (Reverse List `P'T'I'TT'I` Forward List)) `T'TT'I` Construction List `P'T'I'TT'I` (Reverse List `T'TT'I` (Alone `P'T'I'TT'I` (Reverse List `P'T'I'TT'I` Forward List) `T'TT'I` Construction List)))
 -- ((Alone `P'T'I'TT'I` (Reverse List `P'T'I'TT'I` Forward List)) `T'TT'I` Construction List) where
 -- mapping = rewrap `hc` \source (T'TT'I'TTT'I (These sl xs)) ->
  -- T'TT'I `st` that ((super xs `yokl` State `ha` Transition `ha_` restoring `ho'ho` (Unit `hjd`)) `he_'st` super sl) `yo` source where

   -- restoring (T'TT'I'TTT'I (These focus shafted)) scrolling_list_tree = T'TT'I'TTT'I
    -- `he__` Alone (Tree `st` super focus `he__` to @(Nonempty List) `st` scrolling_list_tree `yo` super @((AR)) `yv` super @(AR))
     -- `hjd` super shafted

instance Mapping T'I'II T'I'II (AR) (AR) (Construction Optional) (List `P'T'I'TT'I` Twice `T'TT'I` List) where
 mapping = rewrap `hc` \source x -> (empty @List `hjd` T'TT'I (T'I'I (empty @List `hjd` List `ha` Exist `ha` Build `hc` super x))) `yo` source

instance Mapping T'I'II T'I'II (AR) (AR) (Alone `P'T'I'TT'I` Twice `T'TT'I` List) (List `P'T'I'TT'I` Twice `T'TT'I` List) where
 mapping = rewrap `hc` \source -> rewrap `hc` \x -> x
  `yoi` is `st'ho` (\i -> List `ha` Exist `ha` Build `ha` Item (source i) `ha` Last `hc` Unit)
  `yio'yo` source

instance Mapping T'I'II T'I'II (AR) (AR) (Alone `P'T'I'TT'I` Twice `T'TT'I` List)
 ((Alone `P'T'I'TT'I` Twice `T'TT'I` List) `T'TT'I` Tree `P'T'I'TT'I` Reverse List `T'TT'I` (Alone `P'T'I'TT'I` Twice `T'TT'I` List `T'TT'I` Tree)) where
 mapping = rewrap `hc` \source x -> x `yo` source `ho` intro @Tree @(AR) `yv` wrap @(AR) `hjd` (wrap @(AR) `ha` Label `ha` wrap @AR `ha` Empty) Unit `yv` wrap @(AR)

-- TODO: check this instance, I'm not sure it works correctly
instance {-# OVERLAPS #-}
 ( Covariant Endo Semi Functor (AR) t
 , Covariant Endo Semi Functor (AR) tt
 , Covariant Lax Monoidal Functor (AR) (AR) (P) P Void tttt
 , Covariant Endo Transformation Functor (AR) (t `T'TT'I` tttt `L` tttt `T` ll `L` t `T` Void) (t `TT'T'I` tttt)
 , Covariant Endo Transformation Functor (AR) (tt `T'TT'I` tttt `L` tttt `T` ll `L` tt `T` Void) (tt `TT'T'I` tttt)
 , Covariant Endo Transformation Functor (AR) (tt `T'TT'I` tttt `L` tttt `T` ll `L` tt `T` (Void `P` Void)) (tt `TT'T'I` tttt)
 ) => Mapping T'I'II T'I'II (AR) (AR) ((t `P'T'I'TT'I` Twice `T'TT'I` tt) `T'TT'I` tttt `L` tttt `T` ll `L` (t `P'T'I'TT'I` Twice `T'TT'I` tt) `T` Void) ((t `P'T'I'TT'I` Twice `T'TT'I` tt) `TT'T'I` tttt) where
  mapping = rewrap `hc` \source -> rewrap `hc` \(T'TT'I'TTT'I (These w (T'TT'I (T'I'I (These r f))))) ->
            (r `yokl` rewrap @(AR) @_ @(tttt `L` tttt `T` ll `L` tt `T` (Void `P` Void) `T` _) is)
   `hjd'yp` Apply (w `yokl` rewrap @(AR) @_ @(tttt `L` tttt `T` ll `L` t `T` Void `T` _) is)
   `hjd'yp` Apply (f `yokl` rewrap @(AR) @_ @(tttt `L` tttt `T` ll `L` tt `T` Void `T` _) is)
     `yo` (\(These (These sx x) xs) -> T'TT'I'TTT'I ((x `yo` source) `hjd` (T'TT'I (T'I'I (
      (sx `yo` source `hjd_` xs `yo` source))))))

instance {-# OVERLAPS #-}
 ( Covariant Endo Semi Functor (AR) t
 , Covariant Endo Semi Functor (AR) tt
 , Covariant Lax Monoidal Functor (AR) (AR) (P) P Void tttt
 , Covariant Endo Transformation Functor (AR) (t `T'TT'I` tttt `L` tttt `T` ll `L` t `T` (Void `P` Void)) (t `TT'T'I` tttt)
 , Covariant Endo Transformation Functor (AR) (tt `T'TT'I` tttt `L` tttt `T` ll `L` tt `T` Void) (tt `TT'T'I` tttt)
 , Covariant Endo Transformation Functor (AR) (tt `T'TT'I` tttt `L` tttt `T` ll `L` tt `T` (Void `P` Void)) (tt `TT'T'I` tttt)
 ) => Mapping T'I'II T'I'II (AR) (AR) ((t `P'T'I'TT'I` Twice `T'TT'I` tt) `T'TT'I` tttt `L` tttt `T` ll `L` (t `P'T'I'TT'I` Twice `T'TT'I` tt) `T` (Void `P` Void)) ((t `P'T'I'TT'I` Twice `T'TT'I` tt) `TT'T'I` tttt) where
  mapping = rewrap `hc` \source -> rewrap `hc` \(T'TT'I'TTT'I (These w (T'TT'I (T'I'I (These r f))))) ->
            (f `yokl` rewrap @(AR) @_ @(tttt `L` tttt `T` ll `L` tt `T` (Void `P` Void) `T` _) is)
   `hjd'yp` Apply (w `yokl` rewrap @(AR) @_ @(tttt `L` tttt `T` ll `L` t `T` (Void `P` Void) `T` _) is)
   `hjd'yp` Apply (r `yokl` rewrap @(AR) @_ @(tttt `L` tttt `T` ll `L` tt `T` Void `T` _) is)
     `yo` (\(These (These sx x) xs) -> T'TT'I'TTT'I ((x `yo` source) `hjd` (T'TT'I (T'I'I (
      (sx `yo` source) `hjd_` (xs `yo` source))))))

instance {-# OVERLAPS #-}
 ( Covariant Endo Semi Functor (AR) tt
 , Covariant Lax Monoidal Functor (AR) (AR) (P) P Void ttt
 , Covariant Endo Transformation Functor (AR) (tt `T'TT'I` ttt `L` ttt `T` ll `L` tt `T` Void) (tt `TT'T'I` ttt)
 , Covariant Endo Transformation Functor (AR) (tt `T'TT'I` ttt `L` ttt `T` ll `L` tt `T` (Void `P` Void)) (tt `TT'T'I` ttt)
 ) => Mapping T'I'II T'I'II (AR) (AR) ((Twice `T'TT'I` tt) `T'TT'I` ttt `L` ttt `T` ll `L` (Twice `T'TT'I` tt) `T` Void) ((Twice `T'TT'I` tt) `TT'T'I` ttt) where
  mapping = rewrap `hc` \source -> rewrap `hc` \(T'TT'I (T'I'I (These r f))) ->
            (r `yokl` rewrap @(AR) @_ @(ttt `L` ttt `T` ll `L` tt `T` (Void `P` Void) `T` _) is)
   `hjd'yp` Apply (f `yokl` rewrap @(AR) @_ @(ttt `L` ttt `T` ll `L` tt `T` Void `T` _) is)
     `yo` (\(These sx xs) -> T'TT'I (T'I'I (These (sx `yo` source) (xs `yo` source))))

instance {-# OVERLAPS #-}
 ( Covariant Endo Semi Functor (AR) tt
 , Covariant Lax Monoidal Functor (AR) (AR) (P) P Void ttt
 , Covariant Endo Transformation Functor (AR) (tt `T'TT'I` ttt `L` ttt `T` ll `L` tt `T` Void) (tt `TT'T'I` ttt)
 , Covariant Endo Transformation Functor (AR) (tt `T'TT'I` ttt `L` ttt `T` ll `L` tt `T` (Void `P` Void)) (tt `TT'T'I` ttt)
 ) => Mapping T'I'II T'I'II (AR) (AR) ((Twice `T'TT'I` tt) `T'TT'I` ttt `L` ttt `T` ll `L` (Twice `T'TT'I` tt) `T` (Void `P` Void)) ((Twice `T'TT'I` tt) `TT'T'I` ttt) where
  mapping = rewrap `hc` \source -> rewrap `hc` \(T'TT'I (T'I'I (These r f))) ->
            (f `yokl` rewrap @(AR) @_ @(ttt `L` ttt `T` ll `L` tt `T` (Void `P` Void) `T` _) is)
   `hjd'yp` Apply (r `yokl` rewrap @(AR) @_ @(ttt `L` ttt `T` ll `L` tt `T` Void `T` _) is)
     `yo` (\(These sx xs) -> T'TT'I (T'I'I (These (sx `yo` source) (xs `yo` source))))

-- instance
--  ( Covariant Endo Semi Functor (AR) t
--  -- , Covariant Endo Semi Functor (AR) tt
--  -- , Covariant Endo Semi Functor (AR) ttt
--  -- , Covariant Endo Monoidal Functor (AR) (P) P tttt
--  -- , Covariant Endo Transformation Functor (AR) (t `T'TT'I` t `L` t `T` Void `L` lltt) (t `TT'T'I` tttt)
--  -- , Covariant Endo Transformation Functor (AR) (tt `T'TT'I` t `L` t `T` Void `L` lltt) (tt `TT'T'I` tttt)
--  -- , Covariant Endo Transformation Functor (AR) (ttt `T'TT'I` t `L` t `T` Void `L` lltt) (ttt `TT'T'I` tttt)
--  ) => Mapping T'I'II T'I'II (AR) (AR)
--  (((t `P'T'I'TT'I` Twice `T'TT'I` List) `T'TT'I` Tree `P'T'I'TT'I` Reverse List `T'TT'I` (t `P'T'I'TT'I` Twice `T'TT'I` List `T'TT'I` Tree)) `T'TT'I` ttt `L` ll `L` Void)
--  (((t `P'T'I'TT'I` Twice `T'TT'I` List) `T'TT'I` Tree `P'T'I'TT'I` Stacked Alone Tree List) `TT'T'I` tttt)  where
  -- mapping = rewrap `hc` \source -> rewrap `identity`
  --  \(T'TT'I'TTT'I (These (T'TT'I'TTT'I (These w (T'TT'I'TTT'I (These (Label r) (Label f))))) (Label passed))) ->
  --  ()

-- TODO: we are going to apply the same function to all items in a list but it's actually fine
instance Mapping T'I'II T'I'II (AR) (AR) (List `P'T'I'TT'I` Twice `T'TT'I` List) ((List `P'T'I'TT'I` Twice `T'TT'I` List) `T'TT'I` (List `P'T'I'TT'I` Twice `T'TT'I` List) `L` (List `P'T'I'TT'I` Twice `T'TT'I` List) `T` Void) where
 mapping = rewrap `hc` \source x@(T'TT'I'TTT'I (These _ (T'TT'I (T'I'I (These rl fl))))) ->
  List `ha` Exist `ha` Build `ha` Item (Label x) `hc` super Last
    `hjd__` (rl `yokl` Label @_ @_ @(Void `P` Void) `ha` Apply `ha` State `ha` Event `ha` push @List `ha` Label `ha` that `ha` shift (Back Unit) `ha_` is `hu` x) `hc` empty @List `yv` that
     `hjd_` (fl `yokl` Label @_ @_ @Void `ha` Apply `ha` State `ha` Event `ha` push @List `ha` Label `ha` that `ha` shift (Fore Unit) `ha_` is `hu` x)
      `hc` empty @List `yv` that
     `yv_` T'TT'I `ha` T'I'I
    `yv__` T'TT'I'TTT'I `ho` T'TT'I
    `yo__` source

-- TODO: instance Scrollable (Construction (T'I'I (P) `T'TT'I` Optional)) item where

-- TODO: think about alternative implementations
-- TODO: refactor, it's really hard to read
-- TODO: this instance works incorrectly!
-- instance Mapping T'I'II T'I'II (AR) (AR) (List `T'TT'I` Cascading List) List where
--  mapping = rewrap `hc` \source -> \case
--   T'TT'I (T'TT'I (T'I'II (This ())))
--    -> T'TT'I (T'I'II (This ()))
--   T'TT'I (T'TT'I (T'I'II (That (F'T'I'TT'I (Recursive (T'I'TT'II (These (Cascading (T'TT'I (T'I'II (This ())))) _)))))))
--    -> T'TT'I (T'I'II (This ()))
--   T'TT'I (T'TT'I (T'I'II (That (F'T'I'TT'I (Recursive (T'I'TT'II (These (Cascading (T'TT'I (T'I'II (That
--    (F'T'I'TT'I (Recursive (T'I'TT'II (These x xx)))))))) xxx)))))))
--    -> T'TT'I (T'I'II (That (F'T'I'TT'I (Recursive (T'I'TT'II (These (source x)
--      (fo @Arrow super `compose` super @Arrow `hc`map @T'I'II @T'I'II @(AR) @(AR) @(List `T'TT'I` Cascading List) @List source
--       (T'TT'I (T'TT'I (T'I'II (That (F'T'I'TT'I (Recursive (T'I'TT'II (These (Cascading `ha` T'TT'I `hc`xx `yo` F'T'I'TT'I) xxx))))))))
--      )
--     ))))))

instance Mapping T'I'II T'I'II (AR) (AR) (Covariant Day (AR) (P) P List (List `L` List `T` (Void `P` Void)) e ee) List where
 mapping = rewrap `hc` \source -> rewrap `hc` \case
  These (These e ee) (T'I'II f) ->
   e `yokl` (\x -> Prior `ha` Apply `hc` (super ee `yokl` (\xx -> Prior `ha` Apply `ha` State `ha` Event `hc` push @List (source (f (x `hjd` xx))))))
   `hc____` empty @List
   `yv______` that `ho` super @(AR)

instance Mapping T'I'II T'I'II (AR) (AR) (Covariant Day (AR) (P) P (Construction Optional) (Construction Optional `L` Construction Optional `T` (Void `P` Void)) e ee) (Construction Optional) where
 mapping = rewrap `hc` \source -> rewrap `hc` \case
  These (These e (Label ee)) (T'I'II f) ->
   (e `yokl` (\x -> Prior `ha` Apply `hc` (ee `yokl` (\xx -> Prior `ha` Apply `ha` State `ha` Event `hc` push @List (source `ha` f `hc____` x `hjd` xx)))))
   `hc____` empty @List
   `yv______` that `ho` (\r -> let (T'TT'I (T'I'II (That rr))) = r in rr) `ho` super @(AR)

instance Mapping T'I'II T'I'II (AR) (AR) (List `T'TT'I` List `L` List `T` Void) List where
 mapping = rewrap `hc` \source x -> super x
  `yokl` Prior `ha` Apply `ha__'yokl` Prior `ha` Apply `ha` State `ha` Event `ha` push @List `ha` source `ha__` super @(AR) `hc___` empty @List
  `yv__` that

instance Mapping T'I'II T'I'II (AR) (AR) (List `T'TT'I` List `L` List `T` (Void `P` Void)) List where
 mapping = rewrap `hc` \source x -> super x
  `yokl` Prior `ha` Apply
  `ha__` intro @(Halts `JNT` State `T'I` List _) @(AR)
   `ho_'yok` Try `ha'st'st` is @(Maybe (Nonempty List _))
   `ho_'yok` Apply `ha` (\xx -> xx `yokl` Prior `ha` Apply `ha` State `ha` Event `ha` push @List `ha` source)
  `hc___` empty @List
  `yv__` wrap `ha` Empty `has` is `ho'st` that @(List _)

instance Mapping T'I'II T'I'II (AR) (AR) (List `T'TT'I` S'I'II i `L` S'I'II i `T` Void) List where
 mapping = rewrap `hc` \source x -> super x
  `yokl` Prior `ha` Apply `ha` State `ha` Event
  `ha__` Error `hu` fetch `has` push @List `ho'ho` (fetch `ha` that) `ha` source
  `hc___` empty @List
  `yv__` that

instance Mapping T'I'II T'I'II (AR) (AR) (Construction Optional `T'TT'I` Construction Optional `L` Construction Optional `T` Void) (Construction Optional) where
 mapping = rewrap `hc` \source x -> let start = (super (super (super (super (super x))))) in
  this `hc` start
  `yokl` Apply `ha` Apply
  `ha__'yokl` Prior `ha` Apply
   `ha_'yokl` Prior `ha` Apply `ha` State `ha` Event `ha` push @(Nonempty List) `ha` source
   `ha_` super @(AR) @(Nonempty List `L` Nonempty List `T` Void `T` _)
  `ha__` wrap @(AR) @(Nonempty List (Nonempty List `L` Nonempty List `T` Void `T` _))
  `hc___` super @(AR) @(Nonempty List `L` Nonempty List `T` Void `T` _) `ha` that `hc` start `yo` source
  `yv__` that

instance Mapping T'I'II T'I'II (AR) (AR) (Construction Optional)
 (Construction Optional `T'TT'I` (Alone `P'T'I'TT'I` Twice `T'TT'I` List) `L` (Alone `P'T'I'TT'I` Twice `T'TT'I` List) `T` Void) where
 mapping = rewrap `hc` \source x -> x
  `yv_` Adapt `ho` to @(Scrolling List)
  `kyo` Range `ha` wrap @(AR) @(Scrolling List `L` Scrolling List `T` Void `T` _) `ha'yo` source
  `yv_` Adapt `ho` to @(Nonempty List) `ho` wrap @(AR)

instance Mapping T'I'II T'I'II (AR) (AR) List
 (List `T'TT'I` (Alone `P'T'I'TT'I` Twice `T'TT'I` List) `L` (Alone `P'T'I'TT'I` Twice `T'TT'I` List) `T` Void) where
 mapping = rewrap `hc` \source -> wrap @(AR) @(List `T'TT'I` Scrolling List `L` Scrolling List `T` Void `T'I_` _)
  `ha__` Empty `hu` empty @List
    `has` map @T'I'II @T'I'II @(AR) @(AR) @(Nonempty List) @(Nonempty List `T'TT'I` Scrolling List `L` Scrolling List `T` Void) source `ho'st` Adapt `ho` to @List

-- TODO: Add a label
-- instance Mapping T'I'II T'I'II (AR) (AR) (Construction Optional) (Construction Optional `T'TT'I` Construction Optional) where
 -- mapping = rewrap `hc` \source -> \case
  -- F'T'I'TT'I (Recursive (T'I'TT'II (These e (T'I'II (This ()))))) ->
   -- T'TT'I `ha` F'T'I'TT'I
    -- `li` Last (F'T'I'TT'I (Recursive (T'I'TT'II (These (source e) (T'I'II (This ()))))))
  -- F'T'I'TT'I (Recursive (T'I'TT'II (These e (T'I'II (That es))))) ->
   -- T'TT'I `ha` F'T'I'TT'I
    -- `ha` Next (F'T'I'TT'I (Recursive (T'I'TT'II (These (source e) (T'I'II (That `hc`super (F'T'I'TT'I es `yo` source)))))))
    -- `li` Last (map @T'I'II @T'I'II @(AR) @(AR) source (F'T'I'TT'I es))

-- Define `Rewindable` typeclass, there should be instances for `Scrolling List``identity``Sliding List`

type family Vector x xs where
 Vector x (y `P` xs) = (x ~ y, Vector x xs)
 Vector x y = x ~ y

-- This transformation is not natural!
-- instance (forall i . Setoid (AR) i) => Mapping T'II'I T'I'II (AR) (AR) I Match where
--  mapping = rewrap `hc` \source -> rewrap `hc` \x x' -> is `hu` False Unit `has` Same `hu` True Unit `hc__` x `hjd'q` source x'

instance Semigroup (AR) Boolean where
 s (These x y) = x `hjd'ys'has` Try y

instance Quasigroup (AR) Boolean where
 p (These x y) = x `hjd'yp` Try `hc` y `yu` Unit

instance Semigroup (AR) (List item) where
 s (These x y) = x `yokl` Prior `ha` Apply `ha` State `ha` Event `ha` push `hc___` y `yv__` that

instance Semigroup (AR) (Construction Maybe item) where
 s (These x y) = x `yokl` Prior `ha` Apply `ha` State `ha` Event `ha` push `hc___` y `yv__` that

-- instance
 -- ( Covariant Endo Semi Functor (AR) t
 -- ) => Mapping T'I'II T'I'II (AR) (AR)
  -- (F'T'I'TT'I (T'I'II S) t)
  -- (F'T'I'TT'I (T'I'II S) t `T'TT'I` (I `S'T'I'TT'I` t) `L` (I `S'T'I'TT'I` t) `T` Void) where
 -- mapping = rewrap `hc` \source -> \case
  -- F'T'I'TT'I (Recursive (T'TT'I (T'I'II (This x)))) ->

  -- (\case
  --  T'TT'I (Break x) -> T'TT'I `ha` Vahjde `ha` Label `ha` T'TT'I'TTT'I @(S) @Alone @t `ha` This `ha` Identity `ha` source `hc` x
  --  T'TT'I (Valid x) -> (x :: _)
    
    -- T'TT'I `ha` Vahjde `ha` Label `ha` T'TT'I'TTT'I @(S) @Alone @t `ha` That `hc` (x `yo` source)
  -- )
  -- x
  -- ((T'TT'I `ha` Vahjde `ha` Label `ha` T'TT'I'TTT'I @(S) @Alone @t `ha` This `ha` Identity `ha` source)
  --  `has` (T'TT'I `ha` Vahjde `ha` Label `ha` (T'TT'I'TTT'I @(S) @Alone @t `ha` That `ha` (fo @AR @AR @t source)))
  -- :: Stops _ `T'TT'I` t `T'I_` _ `AR______` F'T'I'TT'I Stops t `T'TT'I_` Stops _ `T'TT'I` t `T'I__` _)
  

-- :: Stops _ `T'TT'I` t `T'I_` _ `AR` (F'T'I'TT'I (T'I'II S) t `T'TT'I` (I `S'T'I'TT'I` t) `L` (I `S'T'I'TT'I` t) `T` Void) _
