module Ya.Program.Interface.Shiftable where

import Ya.Algebra
import Ya.Operators
import Ya.Program.Patterns
import Ya.Program.Primitive
import Ya.Program.Labels

import Ya.Program.Interface.Fieldable
import Ya.Program.Interface.Matchable
import Ya.Program.Interface.Stackable

type Shafted e = Reverse e `P'T'I'TT'I` Forward e

type Stacked window ee e = Reverse e `T'TT'I` (window `P'T'I'TT'I` Shafted e `T'TT'I` ee)

type family Shifting window datastructure = result | result -> window datastructure where
 Shifting window (Optional `T'TT'I` Construction Optional) = window `P'T'I'TT'I` Shafted List
 Shifting window (Construction List) = Shifting window List `T'TT'I` Tree `P'T'I'TT'I` Stacked window Tree List

type family Shifter t where
 Shifter (Optional `T'TT'I` Construction Optional) = Unit `S` Unit
 Shifter (Construction (T'I'I (P) `T'TT'I` Optional)) = Unit `S` Unit `S` Unit
 Shifter (Construction List) = Unit `S` Unit `S_` Unit `S` Unit

class Shiftable window datastructure where
 shift :: Shifter datastructure `AR___` Supertype (Event `T'I` Shifting window datastructure item `T'I` Optional item)

type Leveled e = Shifting Alone List `T'TT'I` e

type Scrolling datastructure = Shifting Alone datastructure

type Scrollable datastructure = Shiftable Alone datastructure

pattern Range :: forall t e . Scrollable t => e `AR__` Alone `L` Scrolling t `T` Void `T` e
pattern Range x = Labeled (Alone x)

type Sliding datastructure = Shifting List datastructure

pattern Lift x = This x :: Shifter List
pattern Down x = That x :: Shifter List

instance Shiftable Alone (Optional `T'TT'I` Construction Optional) where
 shift way x = is `li` None `hu` (None Unit `lu` x) `la` is `ho'he` foi @_ @(AR) Exist `li` shift' `he'he'hv` x where

  shift' = intro @(Halts `JNT` State `T` Scrolling List _) Unit
   `yuk__` New `ha` State `hv__` Event `hv` pop `ha_` Scope `ha` shaft `ha` (Back `la` Fore) `hv` way
   `yok__` Try
   -- `yok__` New `ha` State `ha__` Event `ha` (auto `ho'hu`) `ho_'ha` Scope @(Alone i) at `he'ho'he` Scope it
   `yok__` New `ha` State `ha__` Event `ha` relay `ho_'ha` Scope `hv` focus `ho'he` Scope it
   `yok__` New `ha` State `ha__` Event `ha` push `ho_'ha` Scope `ha` shaft `ha` (Fore `la` Back) `hv` way

instance Shiftable List (Optional `T'TT'I` Construction Optional) where
 shift way x = is
  `li` is `hu` (by None `lu` x)
  `la` is `ho'he` foi @_ @(AR) Exist
  `li` (slide_passed `lv` slide_future `li` way) `he'he'hv` x where

  slide_future = intro @(Halts `JNT` State `T` Sliding List _) Unit
   `yuk____` New `ha` State `hv__` Event `hv` pop `ha_` Scope `hv` focus
   `yok____` Try
   `yok____` New `ha` State `ha__` Event `ha` push `ho_'ha` Scope `ha` shaft `hv` by Passed
   `yuk____` New `ha` State `hv____` Event `hv` pop `ha_` Scope `ha` shaft `hv` by Future
   `yok____` Try
   `yok____` New `ha` State `ha____` Event `ha` window_future `ho_'ha` Scope `hv` focus

  slide_passed = intro @(Halts `JNT` State `T` Sliding List _) Unit
   `yuk____` New `ha` State `hv__` Event `hv` pop `ha_` Scope `ha` shaft `hv` by Passed
   `yok____` Try
   `yok____` New `ha` State `ha__` Event `ha` window_extract_last `ho_'ha` Scope `hv` focus
   `yok____` Try
   `yok____` New `ha` State `ha__` Event `ha` push `ho_'ha` Scope `ha` shaft `hv` by Future

  window_future r w = (is @(List _) w `yokl` Prior `ha` New `ha` State `ha` Event `ha` push `he'he'hv___` List `ha` Item r `ha` Last `hv` Unit) `yui` r

  window_extract_last passed w =
   push @List passed w `yi` that
    `yokl` Forth `ha` New `ha` State `ha` Event `ha` push
    `he'he'hv___` empty @List
    `yi__` that `ho` pop @List

-- TODO: define instances to compose attributes like: attr `ha` attr

pattern Broad x = This x :: Shifter Tree
pattern Level x = That x :: Shifter Tree

-- TODO: implement `locate` method
instance Shiftable Alone (Construction List) where
 shift way x = is
  `li` is `hu` (by None `lu` x)
  `la` is `ho'he` foi @_ @(AR) Exist
  `li` (horizontally `la_` vertical_deep `la` vertical_up `li_` way) `he'he'hv` x where

  horizontally :: forall i . Way `AR___` (Halts `JNT` State `T` Scrolling Tree i) `T'I` i
  horizontally way = intro @(Halts `JNT` State `T` Scrolling Tree i) Unit
   `yuk__` New `ha` State `hv__` Transition `hv` shift way
   `ha_'he` Scope @((Scrolling List `T'TT'I` Tree) i) at
    `ho'he` Scope @(Scrolling List `T'I` Tree i) at
   -- TODO: rewrite it, we need `ha'yo` operator for it
   `yok__` Try `ha___` is `ho_'yo` this `compose` unwrap `compose` unwrap `compose` unwrap

  -- TODO: refactor, it's hard to catch an error here
  vertical_deep :: forall i . Unit `AR___` (Halts `JNT` State `T` Scrolling Tree i) `T'I` i
  vertical_deep _ = intro @(Halts `JNT` State `T` Scrolling Tree i) Unit
   `yuk____` New `ha` State `hv____` Transition `hv` auto
   `ha___'he` Scope @((Scrolling List `T'TT'I` Tree) i) at
   `ho__'he'he` ((Scope @(Alone (Tree i)) at `ho'he'he'he'he`  Scope @(i `P` _) it)
        `lo` Scope @(Shafted List `T'I` Tree i) at)
   `yok____` New `ha` State `ha____` Transition
   `ha_` (\(These (These e ee) eee) list -> (unwrap ee `yo` (e `lu`)) `lu` that `hv` push (T'TT'I'TTT'I (Alone e `lu` wrap eee)) list)
   `ho_'ha'he` Scope @((Reverse List `T'TT'I` (Alone `P'T'I'TT'I` Shafted List `T'TT'I` Tree)) i) at
   `ho'he'he` Scope @(List ((Alone `P'T'I'TT'I` Shafted List `T'TT'I` Tree) i)) at
   `yok____` Try
   `yok____` New `ha` State `ha____` Transition
   `ha_` (\(These previous new) _ -> previous `lu` to @(Scrolling List) (new `yo` R_U_I_T_I))
   `ho_'ha'he` Scope @((Scrolling List `T'TT'I` Tree) i) at
      `ho'he` Scope @(Scrolling List `T'I` Tree i) at

  vertical_up :: forall i . Unit `AR___` (Halts `JNT` State `T` Scrolling Tree i) `T'I_` i
  vertical_up _ = intro @(Halts `JNT` State `T` Scrolling Tree i) Unit
   `yuk___` New `ha` State `hv__` Transition `hv` pop
   `ha_'he` Scope @((Reverse List `T'TT'I_` (Alone `P'T'I'TT'I` Shafted List `T'TT'I` Tree)) i) at
   `ho'he'he` Scope @(List ((Alone `P'T'I'TT'I` Shafted List `T'TT'I` Tree) i)) at
   `yok___` Try
   `yok___` New `ha` State `ha__` Transition `ha_` restoring
   `ho_'ha'he` Scope @((Scrolling List `T'TT'I` Tree) i) at
      `ho'he` Scope @(Scrolling List `T'I` Tree i) at

  restoring (T'TT'I'TTT'I (These focus shafted)) scrolling_list_tree = unwrap focus `lu` (T'TT'I'TTT'I
    `hv__` Alone (Tree `hv` unwrap focus `hv__` to @(Nonempty List) `hv` scrolling_list_tree `yo` unwrap @(AR) `yi` unwrap @(AR))
     `lu` unwrap shafted)

instance Mapping T'I'II T'I'II (AR) (AR)
 (Construction Optional)
 (Alone `P'T'I'TT'I` (Reverse List `P'T'I'TT'I` Forward List)) where
 mapping = rewrap `identity` \from (Root x xs) ->
  T'TT'I'TTT'I (Alone (from x) `lu` T'TT'I'TTT'I (Labeled (empty @List) `lu` (Labeled (T'TT'I (xs `yo` R_U_I_T_I) `yo` from))))

instance Mapping T'I'II T'I'II (AR) (AR) (Alone `P'T'I'TT'I` (Reverse List `P'T'I'TT'I` Forward List)) (Construction Optional) where
 mapping = rewrap `identity` \from (T'TT'I'TTT'I (These (Identity x) (T'TT'I'TTT'I (These l r)))) ->
  (unwrap l `yokl` Forth `ha` New `ha` State `ha` Event `ha` push)
   `he'he'hv__` Empty `hu` intro @(Nonempty List) x `la` push x `ho` that `li` unwrap r
   `yi_` that `ho'yo` from

locate :: forall window datastructure item .
 Shiftable window datastructure =>
 Fieldable (window item) (Supertype (Shifting window datastructure item)) =>
 Wrapper (AR) (Shifting window datastructure item) =>
 Shifter datastructure `P` Predicate (window item) `AR_` Supertype (Event `T'I` Shifting window datastructure item `T'I` Optional (Shifting window datastructure item))
locate (These way predicate) x = foi Exist `ha` auto `la` is `ho'he` foi @_ @(AR) (None `hu` by None) `li` locate' `he'he'hv` x where

 locate' = intro @(Stops `T` Shifting window  datastructure item `JNT` State `T` Shifting window datastructure item) Unit
  `yuk____` State `ho` New `hv____` Event `hv___` auto `ho'yoi` unwrap predicate `ha___'he` Scope `hv` at @(window item)
  `yok____` State `ho` New `ha____` Event `ha___` (Next `hu_` shift `hv` way `ho'yoi` Continue `la_` Same `hu_` auto `ho'yoi` Reach)
  `yok____` Check `ha__` Reach `la` Continue
  `yok____` Retry `ha__` Interrupt `hu` by Ok `la` Again `ha` Same `hu` by Reach

rewind :: forall window datastructure item .
 Shiftable window datastructure =>
 Shifter datastructure `AR___` Supertype (Event `T'I` Shifting window datastructure item `T'I` Unit)
rewind way = unwrap @(AR) `ha` unwrap @(AR)
 `hv_______` intro @(State `T` Shifting window datastructure item) Unit
   `yuk____` State `ho` New `hv____` Event `hv___` shift way
   `yok____` Retry `ha__` Exist `la` Exist `hu` by None

pattern Shrink e = This e
pattern Expand e = That e

-- TODO: it's here temporaly, I should find a way to generalize it:
adjust :: forall item . Unit `S` Unit `P` Shifter List `AR_` Supertype (Event `T'I` Sliding List item `T'I` Optional item)
adjust way x = is `hu` (by None `lu` x) `la` is `ho'he` foi @_ @(AR) Exist `li` router way `he'he'hv` x where

 -- TODO: there should be a way to shorten it
 router (These (This _) (This _)) = shrink_passed
 router (These (This _) (That _)) = shrink_future
 router (These (That _) (This _)) = expand_passed
 router (These (That _) (That _)) = expand_future

 -- [3 2 1] (4 5 6) [7 8 9] ---> [2 1] (3 4 5 6) [7 8 9]
 expand_passed = intro @(Halts `JNT` State `T` Sliding List _) Unit
  `yuk____` New `ha` State `hv__` Event `hv` pop @List `ha_` Scope `ha` shaft `hv` by Passed
  `yok____` Try
  `yok____` New `ha` State `ha__` Event `ha` push `ho_'ha` Scope `hv` focus

 -- [3 2 1] (4 5 6) [7 8 9] ---> [4 3 2 1] (5 6) [7 8 9]
 shrink_passed = intro @(Halts `JNT` State `T` Sliding List _) Unit
  `yuk____` New `ha` State `hv__` Event `hv` pop @List `ha_` Scope `hv` focus
  `yok____` Try
  `yok____` New `ha` State `ha__` Event `ha` push `ho_'ha` Scope `ha` shaft `hv` by Passed

 -- [3 2 1] (4 5 6) [7 8 9] ---> [3 2 1] (4 5 6 7) [8 9]
 expand_future = intro @(Halts `JNT` State `T` Sliding List _) Unit
  `yuk____` New `ha` State `hv__` Event `hv` pop `ha_` Scope `ha` shaft `hv` by Future
  `yok____` Try
  `yok____` New `ha` State `ha__` Event `ha` window_future `ho_'ha` Scope `hv` focus

 window_future r w = (is @(List _) w `yokl` Prior `ha` New `ha` State `ha` Event `ha` push `he'he'hv___` List `ha` Item r `ha` Last `hv` Unit) `yui` r

 -- [3 2 1] (4 5 6) [7 8 9] ---> [3 2 1] (4 5) [6 7 8 9]
 shrink_future = intro @(Halts `JNT` State `T` Sliding List _) Unit
  `yuk____` Old `ha` State `hv__` Event `hv` get_last_window_item `ha_` Scope `hv` focus
  `yok____` New `ha` State `ha__` Event `ha` rearrange_window_back `ho_'ha` Scope `hv` focus
  `yok____` Try
  `yok____` New `ha` State `ha__` Event `ha` push `ho_'ha` Scope `ha` shaft `hv` by Future

 get_last_window_item window = window
  `yokl` New `ha` State `ha` Event `ha` push @List `ho` Prior
  `yuk_` New `ha` State `ha` Event `hv` pop @List
  `he'he'hv_____` empty @List

 rearrange_window_back popped window =
  (window `yokl` New `ha` State `ha` Event `ha` push @List `ho` Prior
  `he'he'hv_____` empty @List) `yui` popped
