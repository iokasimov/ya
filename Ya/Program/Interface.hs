{-# OPTIONS_GHC -fno-warn-orphans #-}
{-# LANGUAGE AllowAmbiguousTypes #-}
module Ya.Program.Interface where

import Ya.Algebra
import Ya.Program.Patterns
import Ya.Program.Primitive

class Field e r where
 at :: Reference LM r e e

instance Field e e where
 at = self

instance Field e (ee `LM` e) where
 at (These x xx) = xx `lu` (x `lu`)

instance {-# OVERLAPS #-} Field e ee => Field e (ee `LM` eee) where
 at (These x xs) = These
  `li` this (at @e @ee `he` x)
  `li` \new -> adjust (Attribute (at @e @ee)) (but new) x `lu` xs

-- type family Handpicked a r where
 -- Handpicked a (a `ML` a_) = a `ML`()
 -- Handpicked a (a_ `ML` a) = a `ML` ()
 -- Handpicked a (a_ `ML` a__) = Handpicked a a_

-- class Matchable a r where
 -- match :: r -> Handpicked a r

-- instance Matchable a (a `ML` a_) where
 -- match = This `la` That `ha` but Unit

-- instance Matchable a (a_ `ML` a) where
 -- match = That `ha` but Unit `la` This

-- instance {-# OVERLAPS #-}
 -- ( Matchable a a_
 -- , Handpicked a (a_ `ML` a__) ~ a `ML` ()
 -- , Handpicked a a_ ~ a `ML` ()
 -- ) => Matchable a (a_ `ML` a__) where
 -- match = match @a @a_ `la` That `ha` but Unit

type family Excluded a r where
 Excluded a (a `ML` a_) = a_
 Excluded a (a_ `ML` a) = a_
 Excluded a (a_ `ML` a__) = Excluded a a_ `ML` a__

class Matchable a r where
 match :: r `AR_` a `ML` Excluded a r

instance Matchable a (a `ML` a_) where
 match = This `la` That

instance Matchable a (a_ `ML` a) where
 match = That `la` This

instance (Excluded a (a `ML` a_ `ML` a__) ~ (a_ `ML` a__))
 => Matchable a (a `ML` a_ `ML` a__) where
 match = This
  `la` That `ha` This
  `la` That `ha` That

instance (Excluded a (a_ `ML` a `ML` a__) ~ (a_ `ML` a__))
 => Matchable a (a_ `ML` a `ML` a__) where
 match = is
  `li` That `ha` This
  `la` This
  `la` That `ha` That

instance (Excluded a (a `ML` a_ `ML` a__ `ML` a___) ~ (a_ `ML` a__ `ML` a___))
 => Matchable a (a `ML` a_ `ML` a__ `ML` a___) where
 match = is
  `li` This
  `la` That `ha` This `ha` This
  `la` That `ha` This `ha` That
  `la` That `ha` That

instance (Excluded a (a_ `ML` a `ML` a__ `ML` a___) ~ (a_ `ML` a__ `ML` a___))
 => Matchable a (a_ `ML` a `ML` a__ `ML` a___) where
 match = is
  `li` That `ha` This `ha` This
  `la` This
  `la` That `ha` This `ha` That
  `la` That `ha` That

instance (Excluded a (a_ `ML` a__ `ML` a `ML` a___) ~ (a_ `ML` a__ `ML` a___))
 => Matchable a (a_ `ML` a__ `ML` a `ML` a___) where
 match = is
  `li` That `ha` This `ha` This
  `la` That `ha` This `ha` That
  `la` This
  `la` That `ha` That

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

instance Mapping Straight Straight Arrow Arrow (Construction Optional) (U_T_I_TT_I LM Only (U_T_I_TT_I LM (Reverse List) (Forward List))) where
 mapping = rewrap / \from (Root x xs) ->
  U_T_I_TT_I (Singular (from x) `lu` U_T_I_TT_I (T_'_I (Empty @List ()) `lu` (T_'_I (T'TT'I (xs `yo` R_U_I_T_I) `yo` from))))

instance
 Mapping Straight Straight Arrow Arrow (U_T_I_TT_I LM Only (U_T_I_TT_I LM (Reverse List) (Forward List))) (Construction Optional) where
 mapping = rewrap / \from (U_T_I_TT_I (These (Identity x) (U_T_I_TT_I (These l r)))) ->
  let f = State `ha` Transition `ha` push @(Nonempty List) `ha` from
  in enter @(State (Nonempty List _))
   `yuk___` New (unwrap l `yokl` Prior `ha` f)
   `yuk___` New (unwrap r `yokl` Forth `ha` f)
   `he_____'he` Construct `ha` Last `he` from x
   `yi_____` that

instance Mapping Straight Straight Arrow Arrow (Construction List)
 ((Only `LM'T'I'TT'I` (Reverse List `LM'T'I'TT'I` Forward List)) `T'TT'I` Construction List `LM'T'I'TT'I` (Reverse List `T'TT'I` (Only `LM'T'I'TT'I` (Reverse List `LM'T'I'TT'I` Forward List) `T'TT'I` Construction List))) where
  mapping = rewrap / \from x -> U_T_I_TT_I
   (T'TT'I (U_T_I_TT_I ((Only `he__` x `yo` from) `lu` U_T_I_TT_I (Reverse `he` Empty @List Unit `lu`Forward `he` Empty @List Unit))) `lu` T'TT'I (Reverse `he` Empty @List Unit))

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
   `yuk__` New `ha` State `he__` Transition `he` pop `ha_'he` Scope @(Shafted List item) at `ho'he` path way `yok__` Try `ha` Maybe
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
   `yuk__` New `ha` State `he__` Transition `he` scroll way
   `ha_'he` Scope @((Scrolling List `T'TT'I` Tree) item) at
    `ho'he` Scope @(Scrolling List `T'I` Tree item) at
   `yok__` Try `ha___` is @(Optional _) `ho_'yo` this `compose` unwrap `compose` unwrap `compose` unwrap

  -- TODO: refactor, it's hard to catch an error here
  vertical_deep :: forall item . Unit `AR___` State `WR` Scrolling Tree item `JNT` Halts `WR__` item
  vertical_deep _ = enter @(State `WR` Scrolling Tree item `JNT` Halts)
   `yuk____` New `ha` State `he____` Transition `he` auto
   `ha___'he` Scope @((Scrolling List `T'TT'I` Tree) item) at
   `ho__'he'he` ((Scope @(Focused (Tree item)) at `ho'he'he'he'he`  Scope @(item `LM` _) self)
        `lo` Scope @(Shafted List `T'I` Tree item) at)
   `yok____` New `ha` State `ha____` Transition
   `ha_` (\(These (These e ee) eee) list -> (unwrap ee `yo` (e `lu`)) `lu` that `he` push (U_T_I_TT_I (Only e `lu` wrap eee)) list)
   `ho_'ha'he` Scope @((Reverse List `T'TT'I` (Only `LM'T'I'TT'I` Shafted List `T'TT'I` Tree)) item) at
   `ho'he'he` Scope @(List ((Only `LM'T'I'TT'I` Shafted List `T'TT'I` Tree) item)) at
   `yok____'he`  Try `ha` Maybe
   `yok____` New `ha` State `ha____` Transition
   `ha_` (\(These previous new) _ -> previous `lu` to @(Scrolling List) (new `yo` R_U_I_T_I))
   `ho_'ha'he` Scope @((Scrolling List `T'TT'I` Tree) item) at
      `ho'he` Scope @(Scrolling List `T'I` Tree item) at

  vertical_up :: forall item . Unit `AR___` State `WR` Scrolling Tree item `JNT` Halts `WR__` item
  vertical_up _ = enter @(State `WR` Scrolling Tree item `JNT` Halts)
   `yuk___` New `ha` State `he__` Transition `he` pop
   `ha_'he` Scope @((Reverse List `T'TT'I_` (Only `LM'T'I'TT'I` Shafted List `T'TT'I` Tree)) item) at
   `ho'he'he` Scope @(List ((Only `LM'T'I'TT'I` Shafted List `T'TT'I` Tree) item)) at
   `yok___` Try `ha` Maybe
   `yok___` New `ha` State `ha__` Transition `ha_` restoring
   `ho_'ha'he` Scope @((Scrolling List `T'TT'I` Tree) item) at
      `ho'he` Scope @(Scrolling List `T'I` Tree item) at

  restoring (U_T_I_TT_I (These focus shafted)) scrolling_list_tree = unwrap focus `lu` (U_T_I_TT_I
    `he__` Only (Tree `he` unwrap focus `he__` to @(Nonempty List) `he` scrolling_list_tree `yo` unwrap @AR `yi` unwrap @AR)
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
