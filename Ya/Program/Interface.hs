{-# OPTIONS_GHC -fno-warn-orphans #-}
{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE UndecidableSuperClasses #-}
module Ya.Program.Interface where

import Ya.Algebra
import Ya.Program.Patterns
import Ya.Program.Primitive

class Field e r where
 at :: Attribute r e

instance Field e e where
 at = Attribute self

instance Field e (ee `LM` e) where
 at = Attribute `li` \(These x xx) -> xx `lu` (x `lu`)

instance {-# OVERLAPS #-} Field e ee => Field e (ee `LM` eee) where
 at = Attribute `he` \(These x xs) -> These
  `li` this (at @e @ee `he'he` x)
  `li` \new -> adjust (at @e @ee) (but new) x `lu` xs

type family Handpicked a r where
 Handpicked a (a `ML` aa) = a `ML`()
 Handpicked a (aa `ML` a) = a `ML` ()
 Handpicked a (aa `ML` aaa) = Handpicked a aa

class Matchable a r where
 match :: r -> Handpicked a r

instance Matchable a (a `ML` aa) where
 match = This `la` That `ha` but Unit

instance Matchable a (aa `ML` a) where
 match = That `ha` but Unit `la` This

instance {-# OVERLAPS #-}
 ( Matchable a aa
 , Handpicked a (aa `ML` aaa) ~ a `ML` ()
 , Handpicked a aa ~ a `ML` ()
 ) => Matchable a (aa `ML` aaa) where
 match = match @a @aa `la` That `ha` but Unit

type family Vector x xs where
 Vector x (y `LM` xs) = (x ~ y, Vector x xs)
 Vector x y = x ~ y

type family Popped datastructure where
 Popped (Construction Optional) = Singular
 Popped (Optional `T_TT_I` Construction Optional) = Optional

type family Leftovers datastructure where
 Leftovers (Construction Optional) = List
 Leftovers (Optional `T_TT_I` Construction Optional) = List

class Stack datastructure where
 pop :: Automation `WR` datastructure item `WR` Supertype (Popped datastructure item) `WR` Leftovers datastructure item
 push :: item -> Automation `WR` datastructure item `WR` item `WR` datastructure item

-- TODO: refactor, it's hard to read
instance Stack List where
 pop = \case
  Empty @List _ -> This () `lu` Empty @List ()
  T_TT_I (Some (Construct (Yet x xs))) -> That x `lu` (T_TT_I / xs `yo` R_U_I_T_I)
 push item s = item `lu` rewrap (Some `ha` R_U_I_T_I `ha` Yet item `ha` (`yo` unwrap @Arrow @(R_U_I_T_I _ _ _))) s

-- TODO: refactor, it's hard to read
instance Stack (Construction Optional) where
 pop = \case
  R_U_I_T_I (Recursive (U_I_T_II (These x (Some xs)))) -> x `lu` T_TT_I (Some (R_U_I_T_I xs))
  R_U_I_T_I (Recursive (U_I_T_II (These x (None _)))) -> x `lu` Empty @List ()
 push x = \old -> These x (Next x `rwr` old)

type Scrolling datastructure =
 U_T_I_TT_I LM Only (Shafted datastructure)

type family Shafted datastructure = result | result -> datastructure where
 Shafted (Construction Singular) = U_T_I_TT_I LM Stream Stream
 Shafted (Optional `T_TT_I` Construction Optional) = U_T_I_TT_I LM (Reverse List) (Forward List)
 Shafted (Construction (U_I_I LM `T_TT_I` Optional)) = U_T_I_TT_I LM
  (U_I_I LM `T_TT_I` Optional) (List `T_TT_I` U_I_I ML `T_TT_I` U_T_I_TT_I LM Only (Optional `T_TT_I` Binary Tree))
 Shafted (Construction List) = U_T_I_TT_I LM
  (U_T_I_TT_I LM (List `T_TT_I` Rose Tree) (Shafted List))
  (List `T_TT_I` (Scrolling List `T_TT_I` Rose Tree))

instance Mapping Straight Straight Arrow Arrow (Construction Optional) (U_T_I_TT_I LM Only (U_T_I_TT_I LM (Reverse List) (Forward List))) where
 mapping = rewrap / \from (Root x xs) ->
  U_T_I_TT_I (Singular (from x) `lu` U_T_I_TT_I (T_'_I (Empty @List ()) `lu` (T_'_I (T_TT_I (xs `yo` R_U_I_T_I) `yo` from))))

instance Mapping Straight Straight Arrow Arrow (Construction List)
 (U_T_I_TT_I LM Only (U_T_I_TT_I LM
  (U_T_I_TT_I LM (List `T_TT_I` Construction List) (U_T_I_TT_I LM (Reverse List) (Forward List)))
  (List `T_TT_I` (U_T_I_TT_I LM Only (U_T_I_TT_I LM (Reverse List) (Forward List)) `T_TT_I` Construction List)))) where
 mapping = rewrap / \from (Root x xs) ->
  U_T_I_TT_I (These (Only (from x))
   (U_T_I_TT_I (These (U_T_I_TT_I (These (T_TT_I ((xs `yo` fo from `compose` R_U_I_T_I) )) (U_T_I_TT_I (These (Reverse (Empty @List Unit)) (Forward (Empty @List Unit)))))) (T_TT_I (Empty @List Unit)))))

type family Scroller datastructure where
 Scroller Stream = () `ML` ()
 Scroller (Optional `T_TT_I` Construction Optional) = () `ML` ()
 Scroller (Construction (U_I_I LM `T_TT_I` Optional)) = () `ML` () `ML` ()
 Scroller (Construction List) = (Unit `ML` Unit) `ML` (Unit `ML` Unit)

type family Scrolled datastructure where
 Scrolled Stream = Only
 Scrolled (Optional `T_TT_I` Construction Optional) = Optional
 Scrolled (Construction (U_I_I LM `T_TT_I` Optional)) = Optional
 Scrolled (Construction List) = Optional

-- TODO: maybe to add `path` method here? Check `Scrolling `WR` Rose Tree` first
class Scrollable datastructure item where
 scroll :: Scroller datastructure
  `ARR` Automation
   `WR` Scrolling datastructure item
   `WR` Scrolled datastructure item
   `WR` Scrolling datastructure item

instance Scrollable (Optional `T_TT_I` Construction Optional) item where
 scroll way x = is
  `li` is `hu` (None () `lu` x)
  `la` is `ho'he` foi @_ @Arrow Some
  `li` unwrap (flow `he'he` x) where

  flow = enter @(State `WR` Scrolling List item `JNT` Halts)
   `yukkk` State `heee` Transition `he` pop `haa'he` at @(Shafted List item) `ho'he` path way `yokkk` Maybe
   `yokkk` State `haaa` Transition `ha` (auto `ho'hu`) `hoo'ha` at @(Focused item) `he'ho'he` Attribute self
   `yokkk` State `haaa` Transition `ha` push `hoo'ha` at @(Shafted List item) `he'ho'he` path (not way)

  path = is `huu` at @(Reverse List item) `ho'he` Attribute self
   `laaaa` is `huu` at @(Forward List item) `ho'he` Attribute self

-- TODO: instance Scrollable (Construction (U_I_I LM `T_TT_I` Optional)) item where

-- TODO: think about alternative implementations
instance Mapping Straight Straight (->) (->) (List `T_TT_I` Cascading List) List where
 mapping = rwr / \from -> \case
  T_TT_I (T_TT_I (U_I_II (This ())))
   -> T_TT_I (U_I_II (This ()))
  T_TT_I (T_TT_I (U_I_II (That (R_U_I_T_I (Recursive (U_I_T_II (These (Cascading (T_TT_I (U_I_II (This ())))) _)))))))
   -> T_TT_I (U_I_II (This ()))
  T_TT_I (T_TT_I (U_I_II (That (R_U_I_T_I (Recursive (U_I_T_II (These (Cascading (T_TT_I (U_I_II (That
   (R_U_I_T_I (Recursive (U_I_T_II (These x xx)))))))) xxx)))))))
   -> T_TT_I (U_I_II (That (R_U_I_T_I (Recursive (U_I_T_II (These (from x)
     (fo @Arrow unwrap `compose` unwrap @Arrow / map @Straight @Straight @(->) @(->) @(List `T_TT_I` Cascading List) @List from
      (T_TT_I (T_TT_I (U_I_II (That (R_U_I_T_I (Recursive (U_I_T_II (These (Cascading `ha` T_TT_I / xx `yo` R_U_I_T_I) xxx))))))))
     )
    ))))))

instance Mapping Straight Straight (->) (->) (Construction Optional) (Construction Optional `T_TT_I` Construction Optional) where
 mapping = rwr / \from -> \case
  R_U_I_T_I (Recursive (U_I_T_II (These e (U_I_II (This ()))))) ->
   T_TT_I `ha` R_U_I_T_I
    `li` Last (R_U_I_T_I (Recursive (U_I_T_II (These (from e) (U_I_II (This ()))))))
  R_U_I_T_I (Recursive (U_I_T_II (These e (U_I_II (That es))))) ->
   T_TT_I `ha` R_U_I_T_I
    `ha` Next (R_U_I_T_I (Recursive (U_I_T_II (These (from e) (U_I_II (That / unwrap (R_U_I_T_I es `yo` from)))))))
    `li` Last (map @Straight @Straight @(->) @(->) from (R_U_I_T_I es))

class Literal datastructure item literal
 where as :: literal -> datastructure item

instance Literal (Construction Optional) item item where
 as x = Construct `li` Last x

instance Literal (Construction Optional) item init =>
 Literal (Construction Optional) item (init `LM` item) where
 as (These init last) =
  that `li` (unwrap `compose` unwrap)
   (Reverse `he` as @(Construction Optional) @item init `yokl` push `ho` Transition `ho` State)
   (Construct (Last last))

instance Literal (Construction (U_I_I LM `T_TT_I` Optional)) item item where
 as x = Root x (T_TT_I (U_I_I (None () `lu` None ())))

instance (Literal (Construction (U_I_I LM `T_TT_I` Optional)) item lst, Literal (Construction (U_I_I LM `T_TT_I` Optional)) item rst) =>
 Literal (Construction (U_I_I LM `T_TT_I` Optional)) item (item `LM` Optional lst `LM` Optional rst) where
 as (These (These x lx) rx) = Root x `ha` T_TT_I `ha` U_I_I
   `lii` (lx `yo` as @(Binary Tree) `ho` unwrap @Arrow)
    `lu` (rx `yo` as @(Binary Tree) `ho` unwrap @Arrow)
