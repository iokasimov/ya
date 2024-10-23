{-# OPTIONS_GHC -fno-warn-orphans #-}
{-# LANGUAGE AllowAmbiguousTypes #-}
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

type Scrolling datastructure = Only `LM_T_I_TT_I` Shafted datastructure

type family Shafted datastructure = result | result -> datastructure where
 Shafted (Construction Singular) = Stream `LM_T_I_TT_I` Stream
 Shafted (Optional `T_TT_I` Construction Optional) = Reverse List `LM_T_I_TT_I` Forward List
 Shafted (Construction (U_I_I LM `T_TT_I` Optional)) = U_I_I LM `T_TT_I` Optional `LM_T_I_TT_I` (List `T_TT_I` U_I_I ML `T_TT_I` U_T_I_TT_I LM Only (Optional `T_TT_I` Construction (U_I_I LM `T_TT_I` Optional)))
 Shafted (Construction List) = List `T_TT_I` Tree `LM_T_I_TT_I` List `T_TT_I` (Only `LM_T_I_TT_I` Shafted List `T_TT_I` Tree)

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

instance Mapping Straight Straight Arrow Arrow (Construction Optional) (U_T_I_TT_I LM Only (U_T_I_TT_I LM (Reverse List) (Forward List))) where
 mapping = rewrap / \from (Root x xs) ->
  U_T_I_TT_I (Singular (from x) `lu` U_T_I_TT_I (T_'_I (Empty @List ()) `lu` (T_'_I (T_TT_I (xs `yo` R_U_I_T_I) `yo` from))))

instance
 Mapping Straight Straight Arrow Arrow (U_T_I_TT_I LM Only (U_T_I_TT_I LM (Reverse List) (Forward List))) (Construction Optional) where
 mapping = rewrap / \from (U_T_I_TT_I (These (Identity x) (U_T_I_TT_I (These l r)))) ->
  let f = State `ha` Transition `ha` push `ha` from in
  that (l `yokl` f `yukkkk` r `yokl` f `heeeeee'he` Construct `ha` Last `he` from x)

instance Mapping Straight Straight Arrow Arrow (Construction List)
 (U_T_I_TT_I LM Only (List `T_TT_I` Construction List `LM_T_I_TT_I` List `T_TT_I` (Only `LM_T_I_TT_I` (Reverse List `LM_T_I_TT_I` Forward List) `T_TT_I` Construction List))) where
  mapping = rewrap / \from (Root x xs) -> U_T_I_TT_I (Only `he` from x `lu` U_T_I_TT_I (T_TT_I (xs `yo` R_U_I_T_I) `yo` from `lu` T_TT_I `he` Empty @List Unit))

-- TODO: maybe to add `path` method here? Check `Scrolling `WR` Tree` first
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
  `li` flow `he'he` x where

  flow = enter @(State `WR` Scrolling List item `JNT` Halts)
   `yukkk` State `heee` Transition `he` pop `haa'he` at @(Shafted List item) `ho'he` path way `yokkk` Maybe
   `yokkk` State `haaa` Transition `ha` (auto `ho'hu`) `hoo'ha` at @(Focused item) `he'ho'he` Attribute self
   `yokkk` State `haaa` Transition `ha` push `hoo'ha` at @(Shafted List item) `he'ho'he` path (not way)

  path = is `huu` at @(Reverse List item) `ho'he` Attribute self
   `laaaa` is `huu` at @(Forward List item) `ho'he` Attribute self

instance Scrollable (Construction (Optional `T_TT_I` Construction Optional)) item where
 scroll way x = is
  `li` is `hu` (None () `lu` x)
  `la` is `ho'he` foi @_ @Arrow Some
  `li` (is `hu` flow_deep `la` is `hu` flow_lift `li` way) `he'he` x where

  flow_deep :: forall item . State `WR` Scrolling Tree item `JNT` Halts `WRRR` item
  flow_deep = enter @(State `WR` Scrolling Tree item `JNT` Halts)
   `yukkk` State `heee` Transition `he` auto
   `haa'he` at @(Shafted Tree item)
    `ho'he` at @((List `T_TT_I` Tree) item)
    `ho'he'he'he` Attribute self `yokkk` Maybe
   `yokkk` but (State `heee` Transition `he` auto `haa'he` at @(Focused item))
    `lo'yp` is @(Nonempty List `WR` Tree _) `ho` to @(Scrolling List) `ho` intro
   `yokkk` State `haaaa` Transition
   `haaa` (\(These e (U_T_I_TT_I (These ee eee))) xs ->
    push (U_T_I_TT_I (e `lu` T_TT_I eee)) xs `yui` unwrap ee)
   `hooo'ha'he` at @(Shafted Tree item)
    `ho'he` at @((List `T_TT_I` (Only `LM_T_I_TT_I` Shafted List `T_TT_I` Tree)) item)
    `ho'he` Attribute self
   `yokkk` State `haaaa` Transition
   `haaa` (\(Root e ee) _ -> Only e `lu` (T_TT_I (ee `yo` R_U_I_T_I)))
   `hooo'ha'he` at @(Shafted Tree item)
    `ho'he` at @((List `T_TT_I` Tree) item)
   `yokkk` State `haaaa` Transition `haaa` switch `ha` unwrap @AR
   `hooo'ha'he` at @(Focused item) `ho'he` Attribute self

  flow_lift :: forall item . State `WR` Scrolling Tree item `JNT` Halts `WRRR` item
  flow_lift = enter @(State `WR` Scrolling Tree item `JNT` Halts)
   `yukkk` State `heee` Transition `he` auto
   `haa'he` at @(Shafted Tree item)
    `ho'he` at @((List `T_TT_I` (Only `LM_T_I_TT_I` Shafted List `T_TT_I` Tree)) item)
    `ho'he'he'he` Attribute self `yokkk` Maybe
   `yokkk` State `haaa` Transition `ha` (\nl _ -> pop nl)
   `hoo'ha'he` at @(Shafted Tree item)
    `ho'he` at @((List `T_TT_I` (Only `LM_T_I_TT_I` Shafted List `T_TT_I` Tree)) item)
    `ho'he` Attribute self
   `yokkk` State `haaa` Transition
   `ha` (\(U_T_I_TT_I (These e ee)) focus -> (unwrap focus `lu`unwrap ee) `lu` e)
   `hoo'ha'he` at @(Focused item)
   `yokkk` State `haaa` Transition
   `ha` (\(These e ee) children -> e `lu` List `ha` Some `ha` to @(Nonempty List)
    `he` U_T_I_TT_I (Only (Root e (children `yo` unwrap @AR)) `lu`ee ))
   `hoo'ha'he` at @(Shafted Tree item)
    `ho'he` at @((List `T_TT_I` Tree) item)
    `ho'he` Attribute self

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
