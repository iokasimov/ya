{-# OPTIONS_GHC -fno-warn-orphans #-}
{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE UndecidableInstances #-}
module Ya.Program.Interface (module Exports) where

import Ya.Algebra
import Ya.Program.Patterns
import Ya.Program.Primitive
import Ya.Program.Labels

import Ya.Program.Interface.Field as Exports
import Ya.Program.Interface.Stack as Exports
import Ya.Program.Interface.Scroll as Exports
import Ya.Program.Interface.Slide as Exports

on' :: Excludable a r => r `AR_` Unit `ML` a
on' x = on x `yui` Unit

class Layable a r where
 lay :: a `AR_` r

instance Layable a a where
 lay = identity

instance Layable a aa => Layable a (T l aa) where
 lay = wrap `ha` lay

instance Layable a (a `ML` aa) where
 lay = This

instance Layable a (aa `ML` a) where
 lay = That

instance Layable a (a `ML` aa `ML` aaa) where
 lay = This `ha` This

instance Layable a (aa `ML` a `ML` aaa) where
 lay = This `ha` That

instance Layable (a `ML` aaa) (a `ML` aa `ML` aaa) where
 lay = This `ha` This `la` That

instance Layable (aaa `ML` a) (a `ML` aa `ML` aaa) where
 lay = That `la` This `ha` This

-- TODO: define more Layable instances

class Fittable a r where
 fit :: r `AR_` MN a r `ML` a

instance
 ( Layable aa (MN a (aa `ML` aaa) `ML` a)
 , Layable aaa (MN a (aa `ML` aaa) `ML` a)
 ) => Fittable a (aa `ML` aaa) where
 fit = lay `la` lay

instance
 ( Layable aa (MN a (aa `ML` aaa `ML` aaaa) `ML` a)
 , Layable aaa (MN a (aa `ML` aaa `ML` aaaa) `ML` a)
 , Layable aaaa (MN a (aa `ML` aaa `ML` aaaa) `ML` a)
 ) => Fittable a (aa `ML` aaa `ML` aaaa) where
 fit = lay `la` lay `la` lay

type family Vector x xs where
 Vector x (y `LM` xs) = (x ~ y, Vector x xs)
 Vector x y = x ~ y

instance Mapping U_I_II U_I_II AR AR (Construction Optional) List where
 mapping = rewrap / \from -> rewrap / wrap `ho'yo` from `ho` Some

instance Mapping U_I_II U_I_II AR AR (Reverse List `LM'T'I'TT'I` Forward List) List where
 mapping = rewrap / \from (U_T_I_TT_I (These (Labeled bs) (Labeled fs))) -> that
  (bs `yokl` Prior `ha` New `ha` State `ha` Event `ha` push @List `he'he'hv____` fs) `yo` from

instance Mapping U_I_II U_I_II AR AR
  (Only `LM'T'I'TT'I` (Reverse List `LM'T'I'TT'I` Forward List))
  ((Only `LM'T'I'TT'I` (Reverse List `LM'T'I'TT'I` Forward List)) `T'TT'I` L Unit (Only `LM'T'I'TT'I` (Reverse List `LM'T'I'TT'I` Forward List))) where
  mapping = rewrap / \from x@(U_T_I_TT_I (These (Identity x') (U_T_I_TT_I (These rl fl)))) ->
   Identity `hv` Labeled x
    `lu__` (unwrap rl `yokl` Prior `ha` New `ha` State `ha` Event `ha` push @List `ha` Labeled `ha` that `ha` scroll (Back ()) `ha_` is `hu` x)
      `he'he'hv` Empty @List () `yi` that `ho` Reverse
     `lu_` (unwrap fl `yokl` Forth `ha` New `ha` State `ha` Event `ha` push @List `ha` Labeled `ha` that `ha` scroll (Fore ()) `ha_` is `hu` x)
      `he'he'hv` Empty @List () `yi` that `ho` Forward
     `yi_` U_T_I_TT_I
    `yi__` U_T_I_TT_I `ho` T'TT'I
    `yo__` from

instance Mapping U_I_II U_I_II Arrow Arrow (Construction List)
 ((Only `LM'T'I'TT'I` (Reverse List `LM'T'I'TT'I` Forward List)) `T'TT'I` Construction List `LM'T'I'TT'I` (Reverse List `T'TT'I` (Only `LM'T'I'TT'I` (Reverse List `LM'T'I'TT'I` Forward List) `T'TT'I` Construction List))) where
  mapping = rewrap / \from x -> U_T_I_TT_I
   (T'TT'I (U_T_I_TT_I ((Only `hv__` x `yo` from) `lu` U_T_I_TT_I (Reverse `hv` Empty @List Unit `lu`Forward `hv` Empty @List Unit))) `lu` T'TT'I (Reverse `hv` Empty @List Unit))

-- instance Mapping U_I_II U_I_II Arrow Arrow
 -- ((Only `LM'T'I'TT'I` (Reverse List `LM'T'I'TT'I` Forward List)) `T'TT'I` Construction List `LM'T'I'TT'I` (Reverse List `T'TT'I` (Only `LM'T'I'TT'I` (Reverse List `LM'T'I'TT'I` Forward List) `T'TT'I` Construction List)))
 -- ((Only `LM'T'I'TT'I` (Reverse List `LM'T'I'TT'I` Forward List)) `T'TT'I` Construction List) where
 -- mapping = rewrap / \from (U_T_I_TT_I (These sl xs)) ->
  -- T'TT'I `he` that ((unwrap xs `yokl` State `ha` Transition `ha_` restoring `ho'ho` (Unit `lu`)) `he_'he` unwrap sl) `yo` from where

   -- restoring (U_T_I_TT_I (These focus shafted)) scrolling_list_tree = U_T_I_TT_I
    -- `he__` Only (Tree `he` unwrap focus `he__` to @(Nonempty List) `he` scrolling_list_tree `yo` unwrap @AR `yi` unwrap @AR)
     -- `lu` unwrap shafted

instance Mapping U_I_II U_I_II AR AR (Construction Optional) (List `LM'T'I'TT'I` (Reverse List `LM'T'I'TT'I` Forward List)) where
 mapping = rewrap / \from x -> U_T_I_TT_I (Empty @List Unit `lu` U_T_I_TT_I (Reverse `hv` Empty @List Unit `lu` Forward `ha` List `hv` unwrap x)) `yo` from

instance Mapping U_I_II U_I_II AR AR List (List `LM'T'I'TT'I` (Reverse List `LM'T'I'TT'I` Forward List)) where
 mapping = rewrap / \from x -> U_T_I_TT_I (Empty @List Unit `lu` U_T_I_TT_I (Reverse `hv` Empty @List Unit `lu` Forward `hv` x)) `yo` from

instance Mapping U_I_II U_I_II AR AR (List `LM'T'I'TT'I` (Reverse List `LM'T'I'TT'I` Forward List)) List where
 mapping = rewrap / \from (U_T_I_TT_I (These w (U_T_I_TT_I (These (Labeled r) (Labeled f))))) ->
  that `ho'yo` from
  `hv_____` enter @(State `WR` List _)
    `yuk__` New (f `yokl` Prior `ha` New `ha` State `ha` Event `ha` push @List)
    `yuk__` New (w `yokl` Prior `ha` New `ha` State `ha` Event `ha` push @List)
    `yuk__` New (r `yokl` Forth `ha` New `ha` State `ha` Event `ha` push @List)
  `he'he'hv____` Empty @List Unit

instance Mapping U_I_II U_I_II AR AR
 (Only `LM'T'I'TT'I` (Reverse List `LM'T'I'TT'I` Forward List))
 (List `LM'T'I'TT'I` (Reverse List `LM'T'I'TT'I` Forward List)) where
 mapping = rewrap / \from -> rewrap / \x -> x
  `yoi` is `he'ho` (\i -> List `ha` Item (from i) `ha` Last `hv` Unit)
  `yio'yo` from

instance Mapping U_I_II U_I_II (->) (->)
 ((t `LM'T'I'TT'I` (Reverse tt `LM'T'I'TT'I` Forward ttt)) `T'TT'I` l `L` ll `L` tttt)
 ((t `LM'T'I'TT'I` (Reverse tt `LM'T'I'TT'I` Forward ttt)) `TT'T'I` tttt)
 where
  -- mapping = rewrap / \from -> rewrap / \(U_T_I_TT_I (These w (U_T_I_TT_I (These (Labeled r) (Labeled f))))) ->
   -- (wrapped (map @U_I_II @U_I_II @AR @AR @(t `T'TT'I` L l (L ll tttt)) @(t `TT'T'I` tttt) from) w :: _)

-- TODO: we are going to apply the same function to all items in a list but it's actually fine
instance Mapping U_I_II U_I_II (->) (->)
 (List `LM'T'I'TT'I` (Reverse List `LM'T'I'TT'I` Forward List))
 ((List `LM'T'I'TT'I` (Reverse List `LM'T'I'TT'I` Forward List)) `T'TT'I` Unit `L` (List `LM'T'I'TT'I` (Reverse List `LM'T'I'TT'I` Forward List))) where
 mapping = rewrap / \from x@(U_T_I_TT_I (These _ (U_T_I_TT_I (These rl fl)))) ->
  List `ha` Item (Labeled x) `ha` Last `hv` Unit
    `lu__` (unwrap rl `yokl` Prior `ha` New `ha` State `ha` Event `ha` push @List `ha` Labeled `ha` that `ha` slide (by Back) `ha_` is `hu` x)
      `he'he'hv` Empty @List () `yi` that `ho` Reverse
     `lu_` (unwrap fl `yokl` Forth `ha` New `ha` State `ha` Event `ha` push @List `ha` Labeled `ha` that `ha` slide (by Fore) `ha_` is `hu` x)
      `he'he'hv` Empty @List () `yi` that `ho` Forward
     `yi_` U_T_I_TT_I
    `yi__` U_T_I_TT_I `ho` T'TT'I
    `yo__` from

-- TODO: instance Scrollable (Construction (U_I_I LM `T'TT'I` Optional)) item where

-- TODO: think about alternative implementations
instance Mapping U_I_II U_I_II (->) (->) (List `T'TT'I` Cascading List) List where
 mapping = rewrap / \from -> \case
  T'TT'I (T'TT'I (U_I_II (This ())))
   -> T'TT'I (U_I_II (This ()))
  T'TT'I (T'TT'I (U_I_II (That (R_U_I_T_I (Recursive (U_I_T_II (These (Cascading (T'TT'I (U_I_II (This ())))) _)))))))
   -> T'TT'I (U_I_II (This ()))
  T'TT'I (T'TT'I (U_I_II (That (R_U_I_T_I (Recursive (U_I_T_II (These (Cascading (T'TT'I (U_I_II (That
   (R_U_I_T_I (Recursive (U_I_T_II (These x xx)))))))) xxx)))))))
   -> T'TT'I (U_I_II (That (R_U_I_T_I (Recursive (U_I_T_II (These (from x)
     (fo @Arrow unwrap `compose` unwrap @Arrow / map @U_I_II @U_I_II @(->) @(->) @(List `T'TT'I` Cascading List) @List from
      (T'TT'I (T'TT'I (U_I_II (That (R_U_I_T_I (Recursive (U_I_T_II (These (Cascading `ha` T'TT'I / xx `yo` R_U_I_T_I) xxx))))))))
     )
    ))))))

-- TODO: Add a label
-- instance Mapping U_I_II U_I_II (->) (->) (Construction Optional) (Construction Optional `T'TT'I` Construction Optional) where
 -- mapping = rewrap / \from -> \case
  -- R_U_I_T_I (Recursive (U_I_T_II (These e (U_I_II (This ()))))) ->
   -- T'TT'I `ha` R_U_I_T_I
    -- `li` Last (R_U_I_T_I (Recursive (U_I_T_II (These (from e) (U_I_II (This ()))))))
  -- R_U_I_T_I (Recursive (U_I_T_II (These e (U_I_II (That es))))) ->
   -- T'TT'I `ha` R_U_I_T_I
    -- `ha` Next (R_U_I_T_I (Recursive (U_I_T_II (These (from e) (U_I_II (That / unwrap (R_U_I_T_I es `yo` from)))))))
    -- `li` Last (map @U_I_II @U_I_II @(->) @(->) from (R_U_I_T_I es))

-- Define `Rewindable` typeclass, there should be instances for `Scrolling List`/`Sliding List`

class Literal datastructure item literal
 where as :: literal -> datastructure item

instance Literal (Construction Optional) item item where
 as x = Construct `li` Item x `ha` Last `hv` Unit

-- instance Literal (Construction Optional) item init =>
 -- Literal (Construction Optional) item (init `LM` item) where
 -- as (These init last) =
  -- that `li` (unwrap `compose` unwrap)
   -- (Reverse `he` as @(Construction Optional) @item init `yokl` push `ho` Transition `ho` State `ho` New)
   -- (Construct (Last last))

instance Literal (Construction (U_I_I LM `T'TT'I` Optional)) item item where
 as x = Root x (T'TT'I (U_I_I (None () `lu` None ())))

instance (Literal (Construction (U_I_I LM `T'TT'I` Optional)) item lst, Literal (Construction (U_I_I LM `T'TT'I` Optional)) item rst) =>
 Literal (Construction (U_I_I LM `T'TT'I` Optional)) item (item `LM` Optional lst `LM` Optional rst) where
 as (These (These x lx) rx) = Root x `ha` T'TT'I `ha` U_I_I
   `li_` (lx `yo` as @(Binary Tree) `ho` unwrap @Arrow)
    `lu` (rx `yo` as @(Binary Tree) `ho` unwrap @Arrow)

-- TODO: generalize over categories
class Excludable a r where
 on :: r `AR_` r `MN` a `ML` a

-- instance Excludable a aa => Excludable a (T e aa) where
 -- on = on `ha` unwrap @AR

instance Excludable a (l # a `ML` aa) where
 on = That `ha'he` is `la` This

instance (aa `ML` l # a `MN` a ~ aa)
 => Excludable a (aa `ML` l # a) where
 on = This `la` That `ha'he` is

instance (l # a `ML` aa `ML` aaa `MN` a ~ aa `ML` aaa)
 => Excludable a (l # a `ML` aa `ML` aaa) where
 on = That `ha'he` is `la` This `ha` This `la` This `ha` That

instance (aa `ML` l # a `ML` aaa `MN` a ~ aa `ML` aaa)
 => Excludable a (aa `ML` l # a `ML` aaa) where
 on = This `ha` This `la` That `ha'he` is `la` This `ha` That

instance (l # a `ML` aa `ML` aaa `ML` aaaa `MN` a ~ aa `ML` aaa `ML` aaaa)
 => Excludable a (l # a `ML` aa `ML` aaa `ML` aaaa) where
 on = That `ha'he` is `la` This `ha` This `ha` This `la` This `ha` This `ha` That `la` This `ha` That

instance (aa `ML` l # a `ML` aaa `ML` aaaa `MN` a ~ aa `ML` aaa `ML` aaaa)
 => Excludable a (aa `ML` l # a `ML` aaa `ML` aaaa) where
 on = This `ha` This `ha` This `la` That `ha'he` is `la` This `ha` This `ha` That `la` This `ha` That

instance (aa `ML` aaa `ML` l # a `ML` aaaa `MN` a ~ aa `ML` aaa `ML` aaaa)
 => Excludable a (aa `ML` aaa `ML` l # a `ML` aaaa) where
 on = This `ha` This `ha` This `la` This `ha` This `ha` That `la` That `ha'he` is `la` This `ha` That

-- instance (forall o . Excludable o e)
 -- => Mapping U_I_II U_I_II (U_I_UU_MN_I_II_II AR ML) AR
 -- (U_I_II (U_I_UU_MN_I_II_II AR ML) e)
 -- (U_I_II (U_I_UU_MN_I_II_II AR ML) e) where
 -- mapping = rewrap / \from -> rewrap `compose` rewrap / \into e ->
  -- case into e of
   -- This e_mn_a -> on e
   -- That a -> case unwrap from a of
    -- This a_mn_o -> on e
    -- That o -> That o

-- ASCII ~> Glyph
-- ASCII ~> Symbol

-- from : (a -> ((a - o) + o))

-- into : (e -> ((e - a) + a))

-- res : (e -> ((e - o) + o))

-- a - o

-- e - o

  -- case (into origin :: _) of
   -- That a -> case unwrap from a of
    -- That o -> That o
    -- This (mn_a_o :: _) -> This mn_a_o
   -- This a_e -> This origin

-- instance Mapping U_II_I U_I_II (U_I_UU_I_II AR ML) AR
 -- (U_II_I (U_I_UU_I_II AR ML) e)
 -- (U_II_I (U_I_UU_I_II AR ML) e) where
 -- mapping = rewrap / \into -> rewrap `compose` rewrap / \from origin ->
  -- case unwrap into origin of
   -- That a -> case from a of
    -- That o -> That o
    -- This o_a -> This origin
   -- This a_e -> This origin

-- instance Category (U_I_UU_I_II AR ML) where
 -- identity = U_I_UU_I_II That
