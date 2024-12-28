{-# OPTIONS_GHC -fno-warn-orphans #-}
{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE UndecidableInstances #-}
module Ya.Program.Interface where

import Ya.Algebra
import Ya.Program.Patterns
import Ya.Program.Primitive
import Ya.Program.Labels

class Field e r where
 at :: Reference LM r e e

instance Field e e where
 at = self

instance Field e (ee `LM` e) where
 at (These x xx) = xx `lu` (x `lu`)

instance {-# OVERLAPS #-} Field e ee => Field e (ee `LM` eee) where
 at (These x xs) = These
  `li` this (at @e @ee `hv` x)
  `li` \new -> adjust (Attribute (at @e @ee)) (constant new) x `lu` xs

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

type family Popped datastructure where
 Popped (Construction Optional) = Singular
 Popped (Optional `T'TT'I` Construction Optional) = Optional

type family Leftovers datastructure where
 Leftovers (Construction Optional) = List
 Leftovers (Optional `T'TT'I` Construction Optional) = List

class Stack datastructure where
 pop :: Automation `WR` datastructure item `WR` Supertype (Popped datastructure item) `WR` Leftovers datastructure item
 push :: item -> Automation `WR` datastructure item `WR` item `WR` datastructure item

-- TODO: refactor, it's hard to read
instance Stack List where
 pop = \case
  Empty @List _ -> This () `lu` Empty @List ()
  T'TT'I (Some (Construct (Recursive (U_I_T_II (These x xs))))) -> That x `lu` (T'TT'I / xs `yo` R_U_I_T_I)
 push item s = item `lu` rewrap
  (Some `ha` R_U_I_T_I `ha` Recursive `ha` U_I_T_II `ha` These item `ha` (`yo` unwrap @Arrow @(R_U_I_T_I _ _ _))) s

-- TODO: refactor, it's hard to read
instance Stack (Construction Optional) where
 pop = \case
  R_U_I_T_I (Recursive (U_I_T_II (These x (Some xs)))) -> x `lu` T'TT'I (Some (R_U_I_T_I xs))
  R_U_I_T_I (Recursive (U_I_T_II (These x (None _)))) -> x `lu` Empty @List ()
 push x = \old -> These x (Next x `rewrap` old)

type Shafted e = Reverse e `LM'T'I'TT'I` Forward e

type Leveled e = Scrolling List `T'TT'I` e

type family Scrolling datastructure = result | result -> datastructure where
 Scrolling (Construction Singular) = Only `LM'T'I'TT'I` (Stream `LM'T'I'TT'I` Stream)
 Scrolling (Optional `T'TT'I` Construction Optional) = Only `LM'T'I'TT'I` Shafted List
 Scrolling (Construction List) = Scrolling List `T'TT'I` Tree `LM'T'I'TT'I` Reverse List `T'TT'I` (Only `LM'T'I'TT'I` Shafted List `T'TT'I` Tree)

type family Scroller datastructure where
 Scroller Stream = () `ML` ()
 Scroller (Optional `T'TT'I` Construction Optional) = () `ML` ()
 Scroller (Construction (U_I_I LM `T'TT'I` Optional)) = () `ML` () `ML` ()
 Scroller (Construction List) = (Unit `ML` Unit) `ML` (Unit `ML` Unit)

type family Scrolled datastructure where
 Scrolled Stream = Only
 Scrolled (Optional `T'TT'I` Construction Optional) = Optional
 Scrolled (Construction (U_I_I LM `T'TT'I` Optional)) = Optional
 Scrolled (Construction List) = Optional

instance Mapping Straight Straight Arrow Arrow
 (Construction Optional)
 (Only `LM'T'I'TT'I` (Reverse List `LM'T'I'TT'I` Forward List)) where
 mapping = rewrap / \from (Root x xs) ->
  U_T_I_TT_I (Singular (from x) `lu` U_T_I_TT_I (Labeled (Empty @List ()) `lu` (Labeled (T'TT'I (xs `yo` R_U_I_T_I) `yo` from))))

instance
 Mapping Straight Straight Arrow Arrow
  (Only `LM'T'I'TT'I` (Reverse List `LM'T'I'TT'I` Forward List))
  (Construction Optional) where
 mapping = rewrap / \from (U_T_I_TT_I (These (Identity x) (U_T_I_TT_I (These l r)))) ->
  let f = State `ha` Transition `ha` push @(Nonempty List) `ha` from
  in enter @(State (Nonempty List _))
   -- TODO: replace with `yuk___'yokl` operator
   `yuk___` New (unwrap l `yokl` Prior `ha` New `ha` f)
   `yuk___` New (unwrap r `yokl` Forth `ha` New `ha` f)
   `he_____'he` Construct `ha` Last `hv` from x
   `yi_____` that

instance Mapping U_I_II U_I_II AR AR
  (Only `LM'T'I'TT'I` (Reverse List `LM'T'I'TT'I` Forward List))
  ((Only `LM'T'I'TT'I` (Reverse List `LM'T'I'TT'I` Forward List)) `T'TT'I` L Unit (Only `LM'T'I'TT'I` (Reverse List `LM'T'I'TT'I` Forward List))) where
  mapping = rewrap / \from x@(U_T_I_TT_I (These (Identity x') (U_T_I_TT_I (These rl fl)))) ->
   Identity `hv` Labeled x
    `lu__` (unwrap rl `yokl` Prior `ha` New `ha` State `ha` Event `ha` push @List `ha` Labeled `ha` that `ha` scroll (Back ()) `ha_` is `hu` x)
      `he'he` Empty @List () `yi` that `ho` Reverse
     `lu_` (unwrap fl `yokl` Forth `ha` New `ha` State `ha` Event `ha` push @List `ha` Labeled `ha` that `ha` scroll (Fore ()) `ha_` is `hu` x)
      `he'he` Empty @List () `yi` that `ho` Forward
     `yi_` U_T_I_TT_I
    `yi__` U_T_I_TT_I `ho` T'TT'I
    `yo__` from

instance Mapping Straight Straight Arrow Arrow (Construction List)
 ((Only `LM'T'I'TT'I` (Reverse List `LM'T'I'TT'I` Forward List)) `T'TT'I` Construction List `LM'T'I'TT'I` (Reverse List `T'TT'I` (Only `LM'T'I'TT'I` (Reverse List `LM'T'I'TT'I` Forward List) `T'TT'I` Construction List))) where
  mapping = rewrap / \from x -> U_T_I_TT_I
   (T'TT'I (U_T_I_TT_I ((Only `hv__` x `yo` from) `lu` U_T_I_TT_I (Reverse `hv` Empty @List Unit `lu`Forward `hv` Empty @List Unit))) `lu` T'TT'I (Reverse `hv` Empty @List Unit))

-- instance Mapping Straight Straight Arrow Arrow
 -- ((Only `LM'T'I'TT'I` (Reverse List `LM'T'I'TT'I` Forward List)) `T'TT'I` Construction List `LM'T'I'TT'I` (Reverse List `T'TT'I` (Only `LM'T'I'TT'I` (Reverse List `LM'T'I'TT'I` Forward List) `T'TT'I` Construction List)))
 -- ((Only `LM'T'I'TT'I` (Reverse List `LM'T'I'TT'I` Forward List)) `T'TT'I` Construction List) where
 -- mapping = rewrap / \from (U_T_I_TT_I (These sl xs)) ->
  -- T'TT'I `he` that ((unwrap xs `yokl` State `ha` Transition `ha_` restoring `ho'ho` (Unit `lu`)) `he_'he` unwrap sl) `yo` from where

   -- restoring (U_T_I_TT_I (These focus shafted)) scrolling_list_tree = U_T_I_TT_I
    -- `he__` Only (Tree `he` unwrap focus `he__` to @(Nonempty List) `he` scrolling_list_tree `yo` unwrap @AR `yi` unwrap @AR)
     -- `lu` unwrap shafted

-- TODO: maybe to add `path` method here? Check `Scrolling `WR` Tree` first
class Scrollable datastructure item where
 scroll :: Scroller datastructure
  `AR_` Automation
   `WR` Scrolling datastructure item
   `WR` Scrolled datastructure item
   `WR` Scrolling datastructure item

instance Scrollable (Optional `T'TT'I` Construction Optional) item where
 scroll way x = is
  `li` is `hu` (None () `lu` x)
  `la` is `ho'he` foi @_ @Arrow Some
  `li` flow `he'he` x where

  flow = enter @(State `WR` Scrolling List item `JNT` Halts)
   `yuk__` New `ha` State `hv__` Transition `hv` pop `ha_'he` Scope @(Shafted List item) at `ho'he` path way `yok__` Try `ha` Maybe
   `yok__` New `ha` State `ha__` Transition `ha` (auto `ho'hu`) `ho_'ha` Scope @(Focused item) at `he'ho'he` Scope self
   `yok__` New `ha` State `ha__` Transition `ha` push `ho_'ha` Scope @(Shafted List item) at `he'ho'he` path (not way)

  path = is `hu_` Scope @(Reverse List item) at `ho'he` Scope self
   `la___` is `hu_` Scope @(Forward List item) at `ho'he` Scope self

-- TODO: define instances to compose attributes like: attr `ha` attr

instance Scrollable (Construction (Optional `T'TT'I` Construction Optional)) item where
 scroll way x = is
  `li` is `hu` (None () `lu` x)
  `la` is `ho'he` foi @_ @Arrow Some
  `li` (horizontally `la_` vertical_deep `la` vertical_up `li_` way) `he'he` x where

  horizontally :: forall item . Way `AR___` State `WR` Scrolling Tree item `JNT` Halts `WR__` item
  horizontally way = enter @(State `WR` Scrolling Tree item `JNT` Halts)
   `yuk__` New `ha` State `hv__` Transition `hv` scroll way
   `ha_'he` Scope @((Scrolling List `T'TT'I` Tree) item) at
    `ho'he` Scope @(Scrolling List `T'I` Tree item) at
   `yok__` Try `ha___` is @(Optional _) `ho_'yo` this `compose` unwrap `compose` unwrap `compose` unwrap

  -- TODO: refactor, it's hard to catch an error here
  vertical_deep :: forall item . Unit `AR___` State `WR` Scrolling Tree item `JNT` Halts `WR__` item
  vertical_deep _ = enter @(State `WR` Scrolling Tree item `JNT` Halts)
   `yuk____` New `ha` State `hv____` Transition `hv` auto
   `ha___'he` Scope @((Scrolling List `T'TT'I` Tree) item) at
   `ho__'he'he` ((Scope @(Focused (Tree item)) at `ho'he'he'he'he`  Scope @(item `LM` _) self)
        `lo` Scope @(Shafted List `T'I` Tree item) at)
   `yok____` New `ha` State `ha____` Transition
   `ha_` (\(These (These e ee) eee) list -> (unwrap ee `yo` (e `lu`)) `lu` that `hv` push (U_T_I_TT_I (Only e `lu` wrap eee)) list)
   `ho_'ha'he` Scope @((Reverse List `T'TT'I` (Only `LM'T'I'TT'I` Shafted List `T'TT'I` Tree)) item) at
   `ho'he'he` Scope @(List ((Only `LM'T'I'TT'I` Shafted List `T'TT'I` Tree) item)) at
   `yok____'he`  Try `ha` Maybe
   `yok____` New `ha` State `ha____` Transition
   `ha_` (\(These previous new) _ -> previous `lu` to @(Scrolling List) (new `yo` R_U_I_T_I))
   `ho_'ha'he` Scope @((Scrolling List `T'TT'I` Tree) item) at
      `ho'he` Scope @(Scrolling List `T'I` Tree item) at

  vertical_up :: forall item . Unit `AR___` State `WR` Scrolling Tree item `JNT` Halts `WR__` item
  vertical_up _ = enter @(State `WR` Scrolling Tree item `JNT` Halts)
   `yuk___` New `ha` State `hv__` Transition `hv` pop
   `ha_'he` Scope @((Reverse List `T'TT'I_` (Only `LM'T'I'TT'I` Shafted List `T'TT'I` Tree)) item) at
   `ho'he'he` Scope @(List ((Only `LM'T'I'TT'I` Shafted List `T'TT'I` Tree) item)) at
   `yok___` Try `ha` Maybe
   `yok___` New `ha` State `ha__` Transition `ha_` restoring
   `ho_'ha'he` Scope @((Scrolling List `T'TT'I` Tree) item) at
      `ho'he` Scope @(Scrolling List `T'I` Tree item) at

  restoring (U_T_I_TT_I (These focus shafted)) scrolling_list_tree = unwrap focus `lu` (U_T_I_TT_I
    `hv__` Only (Tree `hv` unwrap focus `hv__` to @(Nonempty List) `hv` scrolling_list_tree `yo` unwrap @AR `yi` unwrap @AR)
     `lu` unwrap shafted)

-- TODO: instance Scrollable (Construction (U_I_I LM `T'TT'I` Optional)) item where

-- TODO: think about alternative implementations
instance Mapping Straight Straight (->) (->) (List `T'TT'I` Cascading List) List where
 mapping = rewrap / \from -> \case
  T'TT'I (T'TT'I (U_I_II (This ())))
   -> T'TT'I (U_I_II (This ()))
  T'TT'I (T'TT'I (U_I_II (That (R_U_I_T_I (Recursive (U_I_T_II (These (Cascading (T'TT'I (U_I_II (This ())))) _)))))))
   -> T'TT'I (U_I_II (This ()))
  T'TT'I (T'TT'I (U_I_II (That (R_U_I_T_I (Recursive (U_I_T_II (These (Cascading (T'TT'I (U_I_II (That
   (R_U_I_T_I (Recursive (U_I_T_II (These x xx)))))))) xxx)))))))
   -> T'TT'I (U_I_II (That (R_U_I_T_I (Recursive (U_I_T_II (These (from x)
     (fo @Arrow unwrap `compose` unwrap @Arrow / map @Straight @Straight @(->) @(->) @(List `T'TT'I` Cascading List) @List from
      (T'TT'I (T'TT'I (U_I_II (That (R_U_I_T_I (Recursive (U_I_T_II (These (Cascading `ha` T'TT'I / xx `yo` R_U_I_T_I) xxx))))))))
     )
    ))))))

-- TODO: Add a label
instance Mapping Straight Straight (->) (->) (Construction Optional) (Construction Optional `T'TT'I` Construction Optional) where
 mapping = rewrap / \from -> \case
  R_U_I_T_I (Recursive (U_I_T_II (These e (U_I_II (This ()))))) ->
   T'TT'I `ha` R_U_I_T_I
    `li` Last (R_U_I_T_I (Recursive (U_I_T_II (These (from e) (U_I_II (This ()))))))
  R_U_I_T_I (Recursive (U_I_T_II (These e (U_I_II (That es))))) ->
   T'TT'I `ha` R_U_I_T_I
    `ha` Next (R_U_I_T_I (Recursive (U_I_T_II (These (from e) (U_I_II (That / unwrap (R_U_I_T_I es `yo` from)))))))
    `li` Last (map @Straight @Straight @(->) @(->) from (R_U_I_T_I es))

class Literal datastructure item literal
 where as :: literal -> datastructure item

instance Literal (Construction Optional) item item where
 as x = Construct `li` Last x

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
