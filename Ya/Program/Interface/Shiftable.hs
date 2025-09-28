module Ya.Program.Interface.Shiftable where

import Ya.Algebra
import Ya.Operators
import Ya.Program.Patterns
import Ya.Program.Primitive
import Ya.Program.Labels

import Ya.Program.Interface.Fieldable
import Ya.Program.Interface.Matchable
import Ya.Program.Interface.Stackable

type Shafted t = Reverse t `P'T'I'TT'I` Forward t

type Unfoldings t tt = Reverse List `T'TT'I` (t `P'T'I'TT'I` Shafted List `T'TT'I` tt)

type family Shifting t tt = r | r -> t tt where
 Shifting t (Optional `T'TT'I` Construction Optional) = t `P'T'I'TT'I` Shafted List
 Shifting t (Construction List) = Shifting t List `T'TT'I` Tree `P'T'I'TT'I` Unfoldings t Tree

type family Shifter t where
 Shifter (Optional `T'TT'I` Construction Optional) = Unit `S` Unit
 Shifter (Construction (T'I'I (P) `T'TT'I` Optional)) = Unit `S` Unit `S` Unit
 Shifter (Construction List) = Unit `S` Unit `S_` Unit `S` Unit

class Shiftable t tt where
 shift :: Shifter tt `AR___` Supertype (Event `T'I` Shifting t tt i `T'I` Optional i)

type Leveled e = Shifting Alone List `T'TT'I` e

type Scrolling t = Shifting Alone t

type Scrollable t = Shiftable Alone t

pattern Range :: forall t e . Scrollable t => e `AR__` Alone `L` Scrolling t `T` Void `T` e
pattern Range x = Label (Alone x)

type Sliding t = Shifting List t

pattern Lift x = This x :: Shifter List
pattern Down x = That x :: Shifter List

instance Shiftable Alone (Optional `T'TT'I` Construction Optional) where
 shift way x = is `li` Empty `hu` (Empty Unit `lu` x) `la` is `ho'he` foi @_ @(AR) Exist `li` shift' `he'he'hv` x where

  shift' = intro @(Halts `JNT` State `T` Scrolling List _) Unit
   `yuk__` Apply `ha` State `hv__` Event `hv` pop `ha_` Scope `ha` shaft `ha` (Back `la` Fore) `hv` way
   `yok__` Check
   -- `yok__` Apply `ha` State `ha__` Event `ha` (auto `ho'hu`) `ho_'ha` Scope @(Alone i) at `he'ho'he` Scope it
   `yok__` Apply `ha` State `ha__` Event `ha` relay `ho_'ha` Scope `hv` at @(Alone _) `ho'he` Scope it
   `yok__` Apply `ha` State `ha__` Event `ha` push `ho_'ha` Scope `ha` shaft `ha` (Fore `la` Back) `hv` way

instance Shiftable List (Optional `T'TT'I` Construction Optional) where
 shift way x = is
  `li` is `hu` (by Empty `lu` x)
  `la` is `ho'he` foi @_ @(AR) Exist
  `li` (slide_passed `lv` slide_future `li` way) `he'he'hv` x where

  slide_future = intro @(Halts `JNT` State `T` Sliding List _) Unit
   `yuk____` Apply `ha` State `hv__` Event `hv` pop `ha_` Scope `hv` at @(List _)
   `yok____` Check
   `yok____` Apply `ha` State `ha__` Event `ha` push `ho_'ha` Scope `ha` shaft `hv` by Passed
   `yuk____` Apply `ha` State `hv____` Event `hv` pop `ha_` Scope `ha` shaft `hv` by Future
   `yok____` Check
   `yok____` Apply `ha` State `ha____` Event `ha` window_future `ho_'ha` Scope `hv` at @(List _)

  slide_passed = intro @(Halts `JNT` State `T` Sliding List _) Unit
   `yuk____` Apply `ha` State `hv__` Event `hv` pop `ha_` Scope `ha` shaft `hv` by Passed
   `yok____` Check
   `yok____` Apply `ha` State `ha__` Event `ha` window_extract_last `ho_'ha` Scope `hv` at @(List _)
   `yok____` Check
   `yok____` Apply `ha` State `ha__` Event `ha` push `ho_'ha` Scope `ha` shaft `hv` by Future

  window_future r w = (is @(List _) w `yokl` Prior `ha` Apply `ha` State `ha` Event `ha` push `he'he'hv___` List `ha` Item r `ha` Last `hv` Unit) `yui` r

  window_extract_last passed w =
   push @List passed w `yi` that
    `yokl` Forth `ha` Apply `ha` State `ha` Event `ha` push
    `he'he'hv___` empty @List
    `yi__` that `ho` pop @List

-- TODO: define instances to compose attributes like: attr `ha` attr

-- pattern Broad x = This x :: Shifter Tree
-- pattern Level x = That x :: Shifter Tree

instance Mapping T'I'II T'I'II (AR) (AR)
 (Construction Maybe `T'TT'I` Construction List)
 ((Alone `P'T'I'TT'I` Shafted List) `T'TT'I` Construction List `P'T'I'TT'I` Unfoldings Alone Tree) where
 mapping = rewrap `identity` \from x ->
  T'TT'I (to @(Scrolling List) `hv'he` x) `yo` from `lu` T'TT'I (Label `hv` empty @List) `yi` T'TT'I'TTT'I

-- TODO: implement `locate` method
instance Shiftable Alone (Construction List) where
 shift way x = is
  `li` is `hu` (by Empty `lu` x)
  `la` is `ho'he` foi @_ @(AR) Exist
  `li` (horizontally `la_` vertical_deep `la` vertical_up `li_` way) `he'he'hv` x where

  horizontally :: forall i . Way `AR___` (Halts `JNT` State `T` Scrolling Tree i) `T'I` i
  horizontally way = intro @(Halts `JNT` State `T` Scrolling Tree i) Unit
   `yuk__` Apply `ha` State @(Scrolling Tree i)
   `hv___` Event `hv` shift way
    `ha__` Scope `hv` at @(Scrolling List `T'TT'I` Tree `T'I_` i)
   `ho_'he` Scope `hv` it @(Scrolling List `T'I_` Tree i)
   `yok__` Check `ha_'yo` is `ho'he'he'he'he` this

  vertical_deep :: forall i . Unit `AR___` Halts `JNT` State `T'I` Scrolling Tree i `T'I_` i
  vertical_deep _ = intro @(Halts `JNT` State `T'I` Scrolling Tree i) Unit
   `yuk___` Apply `ha` State @(Scrolling Tree i)
   `hv____` Event `hv` get @(Alone (Tree i) `P` Shafted List (Tree i))
    `ha___` Scope `hv` at @(Scrolling List `T'TT'I` Tree `T'I_` i)
     `ho__` Scope `hv` at @(Alone `T'I` Tree i)
       `lo` Scope `hv` at @(Shafted List `T'I` Tree i)
   `yok___` Apply `ha` State
   `ha____` Event `ha__` (\(These (Alone tree) shafted) list ->
      let (These focus subtree) = objective @T'I'II @(AR) @(Tree i) @(i `P` List (Supertype (Tree i))) tree in
      (subtree `yo` wrap @(AR) @(Tree i)) `lu` that `hv` push (T'TT'I'TTT'I (Alone focus `lu` wrap shafted)) list
     )
   `ho__'ha` Scope `hv` at @(Reverse List `T'TT'I` (Alone `P'T'I'TT'I` Shafted List `T'TT'I` Tree) `T'I_` i)
   `ho_'he'he` Scope `hv` at @(List ((Alone `P'T'I'TT'I` Shafted List `T'TT'I` Tree) i))
   `yok___` Check `ha` unwrap @(AR)
   `yok___` Apply `ha` State
   `ha____` Event `ha` (\x _ -> top @(Nonempty List) `ho` this `ho` top @Tree `ho` this `lo` to @(Scrolling List) @(Nonempty List) `li` x)
   -- `ha____` Event `ha` put `ha` to @(Scrolling List) @(Nonempty List)
   `ho__'ha` Scope `hv` at @(Scrolling List `T'TT'I` Tree `T'I_` i)
    `ho_'he` Scope `hv` at @(Scrolling List `T'I_` Tree i)

  vertical_up :: forall i . Unit `AR___` (Halts `JNT` State `T` Scrolling Tree i) `T'I_` i
  vertical_up _ = intro @(Halts `JNT` State `T` Scrolling Tree i) Unit
   `yuk___` Apply `ha` State
   `hv____` Event `hv` pop @List @((Alone `P'T'I'TT'I` Shafted List `T'TT'I` Tree) i)
   `ha__'he` Scope `hv` at @(Reverse List `T'TT'I` (Alone `P'T'I'TT'I` Shafted List `T'TT'I` Tree) `T'I_` i) `ho_'he'he` Scope `hv` it
   `yok___` Check @((Alone `P'T'I'TT'I` Shafted List `T'TT'I` Tree) i)
   `yok___` Apply `ha` State
   `ha____` Event `ha` restoring
   `ho__'ha` Scope `hv` at @(Scrolling List `T'TT'I` Tree `T'I_` i)
    `ho_'he` Scope `hv` at @(Scrolling List `T'I_` Tree i)

  restoring :: (Alone `P'T'I'TT'I` Shafted List `T'TT'I` Tree) i `AR___` Scrolling List (Tree i) `AR__` i `P` Scrolling List (Tree i)
  restoring (T'TT'I'TTT'I (These focus shafted)) scrolling_list_tree = unwrap focus `lu` (T'TT'I'TTT'I
    `hv__` Alone (Tree `hv` unwrap focus `hv__` to @(Nonempty List) `hv` scrolling_list_tree `yo` unwrap @(AR) `yi` unwrap @(AR))
     `lu` unwrap shafted)

instance Mapping T'I'II T'I'II (AR) (AR)
 (Construction Optional)
 (Alone `P'T'I'TT'I` (Reverse List `P'T'I'TT'I` Forward List)) where
 mapping = rewrap `identity` \from (Root x xs) ->
  T'TT'I'TTT'I (Alone (from x) `lu` T'TT'I'TTT'I (Label (empty @List) `lu` (Label (T'TT'I (xs `yo` R_U_I_T_I) `yo` from))))

instance Mapping T'I'II T'I'II (AR) (AR) (Alone `P'T'I'TT'I` (Reverse List `P'T'I'TT'I` Forward List)) (Construction Optional) where
 mapping = rewrap `identity` \from (T'TT'I'TTT'I (These (Identity x) (T'TT'I'TTT'I (These l r)))) ->
  (unwrap l `yokl` Forth `ha` Apply `ha` State `ha` Event `ha` push)
   `he'he'hv__` Empty `hu` intro @(Nonempty List) x `la` push x `ho` that `li` unwrap r
   `yi_` that `ho'yo` from

spot :: forall t tt i .
 Shiftable t tt =>
 Fieldable (t i) (Shifting t tt i) =>
 Wrapper (AR) (Shifting t tt i) =>
 Shifter tt `P` Predicate (t i) `AR_` Supertype (Event `T'I` Shifting t tt i `T'I` Optional (Shifting t tt i))
spot (These way predicate) x = foi Exist `ha` get `la` is `ho'he` foi @_ @(AR) (Empty `hu` by Empty) `li` _locate_ `he'he'hv` x where

 found (These w sl) = unwrap (predicate `he'hv` w) `yui` sl `yiu` sl

 _locate_ = intro @(Stops `T` Shifting t tt i `JNT` State `T` Shifting t tt i) Unit
  `yuk____` Lease `ha` State `hv___` Event `hv__` get `ha__` Scope `hv` at @(t i) `lo` Scope `hv` it
  `yok____` Check `ha` Stops `ha___` not `ha` found
  `yuk____` Apply `ha` State `hv___` Event `hv__` shift `hv` way
  `yok____` Retry `ha` is `ha__` Break `hu` by Ok `la` Again `hu` Reach Unit

rewind :: forall t tt i .
 Shiftable t tt =>
 Shifter tt `AR___` Supertype (Event `T'I` Shifting t tt i `T'I` Unit)
rewind way = unwrap @(AR) `ha` unwrap @(AR)
 `hv_______` intro @(State `T` Shifting t tt i) Unit
   `yuk____` Apply `ha` State `ha` Event `hv` shift way
   `yok____` Retry `ha__` Exist `la` Exist `hu` by Empty

pattern Shrink e = This e
pattern Expand e = That e

-- TODO: it's here temporaly, I should find a way to generalize it:
adjust :: forall i . Unit `S` Unit `P` Shifter List `AR_` Supertype (Event `T'I` Sliding List i `T'I` Optional i)
adjust way x = is `hu` (by Empty `lu` x) `la` is `ho'he` foi @_ @(AR) Exist `li` router way `he'he'hv` x where

 -- TODO: there should be a way to shorten it
 router (These (This _) (This _)) = shrink_passed
 router (These (This _) (That _)) = shrink_future
 router (These (That _) (This _)) = expand_passed
 router (These (That _) (That _)) = expand_future

 -- [3 2 1] (4 5 6) [7 8 9] ---> [2 1] (3 4 5 6) [7 8 9]
 expand_passed = intro @(Halts `JNT` State `T` Sliding List _) Unit
  `yuk____` Apply `ha` State `hv__` Event `hv` pop @List `ha_` Scope `ha` shaft `hv` by Passed
  `yok____` Check
  `yok____` Apply `ha` State `ha__` Event `ha` push `ho_'ha` Scope `hv` at @(List i)

 -- [3 2 1] (4 5 6) [7 8 9] ---> [4 3 2 1] (5 6) [7 8 9]
 shrink_passed = intro @(Halts `JNT` State `T` Sliding List i) Unit
  `yuk____` Apply `ha` State `hv__` Event `hv` pop @List `ha_` Scope `hv` at @(List i)
  `yok____` Check
  `yok____` Apply `ha` State `ha__` Event `ha` push `ho_'ha` Scope `ha` shaft `hv` by Passed

 -- [3 2 1] (4 5 6) [7 8 9] ---> [3 2 1] (4 5 6 7) [8 9]
 expand_future = intro @(Halts `JNT` State `T` Sliding List _) Unit
  `yuk____` Apply `ha` State `hv__` Event `hv` pop `ha_` Scope `ha` shaft `hv` by Future
  `yok____` Check
  `yok____` Apply `ha` State `ha__` Event `ha` window_future `ho_'ha` Scope `hv` at @(List i)

 window_future r w = (is @(List _) w `yokl` Prior `ha` Apply `ha` State `ha` Event `ha` push `he'he'hv___` List `ha` Item r `ha` Last `hv` Unit) `yui` r

 -- [3 2 1] (4 5 6) [7 8 9] ---> [3 2 1] (4 5) [6 7 8 9]
 shrink_future = intro @(Halts `JNT` State `T` Sliding List _) Unit
  `yuk____` Old `ha` State `hv__` Event `hv` get_last_window_item `ha_` Scope `hv` at @(List i)
  `yok____` Apply `ha` State `ha__` Event `ha` rearrange_window_back `ho_'ha` Scope `hv` at @(List i)
  `yok____` Check
  `yok____` Apply `ha` State `ha__` Event `ha` push `ho_'ha` Scope `ha` shaft `hv` by Future

 get_last_window_item window = window
  `yokl` Apply `ha` State `ha` Event `ha` push @List `ho` Prior
  `yuk_` Apply `ha` State `ha` Event `hv` pop @List
  `he'he'hv_____` empty @List

 rearrange_window_back popped window =
  (window `yokl` Apply `ha` State `ha` Event `ha` push @List `ho` Prior
  `he'he'hv_____` empty @List) `yui` popped
