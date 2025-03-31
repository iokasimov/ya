module Ya.Program.Interface.Shiftable where

import Ya.Algebra
import Ya.Program.Patterns
import Ya.Program.Primitive
import Ya.Program.Labels

import Ya.Program.Interface.Field
import Ya.Program.Interface.Match
import Ya.Program.Interface.Stack

type Shafted e = Reverse e `P'T'I'TT'I` Forward e

type family Shifting window datastructure = result | result -> window datastructure where
 Shifting window (Optional `T'TT'I` Construction Optional) = window `P'T'I'TT'I` Shafted List
 Shifting window (Construction List) = Shifting window List `T'TT'I` Tree `P'T'I'TT'I` Reverse List `T'TT'I` (window `P'T'I'TT'I` Shafted List `T'TT'I` Tree)

type family Shifter t where
 Shifter (Optional `T'TT'I` Construction Optional) = Unit `S` Unit
 Shifter (Construction (U_I_I P `T'TT'I` Optional)) = Unit `S` Unit `S` Unit
 Shifter (Construction List) = Unit `S` Unit `S_` Unit `S` Unit

class Shiftable window datastructure item where
 shift :: Shifter datastructure `AR___` Supertype (Event `WR` Shifting window datastructure item `WR` Optional item)

type Leveled e = Shifting Only List `T'TT'I` e

type Scrolling datastructure = Shifting Only datastructure

type Sliding datastructure = Shifting List datastructure

instance Shiftable Only (Optional `T'TT'I` Construction Optional) i where
 shift way x = is `li` None `hu` (None Unit `lu` x) `la` is `ho'he` foi @_ @AR Some `li` shift' `he'he'hv` x where

  shift' = enter @(State `WR` Scrolling List i `JNT` Halts)
   `yuk__` New `ha` State `hv__` Event `hv` pop `ha_'he` Scope @(Shafted List i) at `ho'he` path way
   `yok__` Try
   -- `yok__` New `ha` State `ha__` Event `ha` (auto `ho'hu`) `ho_'ha` Scope @(Focused i) at `he'ho'he` Scope it
   `yok__` New `ha` State `ha__` Event `ha` switch `ho_'ha` Scope @(Focused i) at `he'ho'he` Scope it
   `yok__` New `ha` State `ha__` Event `ha` push `ho_'ha` Scope @(Shafted List i) at `he'ho'he` path (not way)

  path = Back `hu_` Scope @(Reverse List i) at `ho'he` Scope it
   `la___` Fore `hu_` Scope @(Forward List i) at `ho'he` Scope it

instance Shiftable List (Optional `T'TT'I` Construction Optional) item where
 shift way x = is
  `li` is `hu` (by None `lu` x)
  `la` is `ho'he` foi @_ @AR Some
  `li` (slide_passed `lv` slide_future `li` way) `he'he'hv` x where

  slide_future = enter @(State `WR` Sliding List item `JNT` Halts)
   `yuk____` New `ha` State `hv__` Event `hv` pop `ha_` Scope `hv` focus
   `yok____` Try
   `yok____` New `ha` State `ha__` Event `ha` push `ho_'ha` Scope `ha` shaft `hv` by Passed
   `yuk____` New `ha` State `hv____` Event `hv` pop `ha_` Scope `ha` shaft `hv` by Future
   `yok____` Try
   `yok____` New `ha` State `ha____` Event `ha` window_future `ho_'ha` Scope `hv` focus

  slide_passed = enter @(State `WR` Sliding List item `JNT` Halts)
   `yuk____` New `ha` State `hv__` Event `hv` pop `ha_` Scope `ha` shaft `hv` by Passed
   `yok____` Try
   `yok____` New `ha` State `ha__` Event `ha` window_extract_last `ho_'ha` Scope `hv` focus
   `yok____` Try
   `yok____` New `ha` State `ha__` Event `ha` push `ho_'ha` Scope `ha` shaft `hv` by Future

  window_future r w = (is @(List _) w `yokl` Prior `ha` New `ha` State `ha` Event `ha` push `he'he'hv___` List `ha` Item r `ha` Last `hv` Unit) `yui` r

  window_extract_last passed w =
   push @List passed w `yi` that
    `yokl` Forth `ha` New `ha` State `ha` Event `ha` push
    `he'he'hv___` by `hv` Empty @List
    `yi__` that `ho` pop @List

-- TODO: define instances to compose attributes like: attr `ha` attr

-- TODO: implement `locate` method
instance Shiftable Only (Construction (Optional `T'TT'I` Construction Optional)) i where
 shift way x = is
  `li` is `hu` (by None `lu` x)
  `la` is `ho'he` foi @_ @AR Some
  `li` (horizontally `la_` vertical_deep `la` vertical_up `li_` way) `he'he'hv` x where

  horizontally :: forall i . Way `AR___` State `WR` Scrolling Tree i `JNT` Halts `WR__` i
  horizontally way = enter @(State `WR` Scrolling Tree i `JNT` Halts)
   `yuk__` New `ha` State `hv__` Transition `hv` shift way
   `ha_'he` Scope @((Scrolling List `T'TT'I` Tree) i) at
    `ho'he` Scope @(Scrolling List `T'I` Tree i) at
   -- TODO: rewrite it, we need `ha'yo` operator for it
   `yok__` Try `ha___` is `ho_'yo` this `compose` unwrap `compose` unwrap `compose` unwrap

  -- TODO: refactor, it's hard to catch an error here
  vertical_deep :: forall i . Unit `AR___` State `WR` Scrolling Tree i `JNT` Halts `WR__` i
  vertical_deep _ = enter @(State `WR` Scrolling Tree i `JNT` Halts)
   `yuk____` New `ha` State `hv____` Transition `hv` auto
   `ha___'he` Scope @((Scrolling List `T'TT'I` Tree) i) at
   `ho__'he'he` ((Scope @(Focused (Tree i)) at `ho'he'he'he'he`  Scope @(i `P` _) it)
        `lo` Scope @(Shafted List `T'I` Tree i) at)
   `yok____` New `ha` State `ha____` Transition
   `ha_` (\(These (These e ee) eee) list -> (unwrap ee `yo` (e `lu`)) `lu` that `hv` push (U_T_I_TT_I (Only e `lu` wrap eee)) list)
   `ho_'ha'he` Scope @((Reverse List `T'TT'I` (Only `P'T'I'TT'I` Shafted List `T'TT'I` Tree)) i) at
   `ho'he'he` Scope @(List ((Only `P'T'I'TT'I` Shafted List `T'TT'I` Tree) i)) at
   `yok____` Try
   `yok____` New `ha` State `ha____` Transition
   `ha_` (\(These previous new) _ -> previous `lu` to @(Scrolling List) (new `yo` R_U_I_T_I))
   `ho_'ha'he` Scope @((Scrolling List `T'TT'I` Tree) i) at
      `ho'he` Scope @(Scrolling List `T'I` Tree i) at

  vertical_up :: forall i . Unit `AR___` State `WR` Scrolling Tree i `JNT` Halts `WR__` i
  vertical_up _ = enter @(State `WR` Scrolling Tree i `JNT` Halts)
   `yuk___` New `ha` State `hv__` Transition `hv` pop
   `ha_'he` Scope @((Reverse List `T'TT'I_` (Only `P'T'I'TT'I` Shafted List `T'TT'I` Tree)) i) at
   `ho'he'he` Scope @(List ((Only `P'T'I'TT'I` Shafted List `T'TT'I` Tree) i)) at
   `yok___` Try
   `yok___` New `ha` State `ha__` Transition `ha_` restoring
   `ho_'ha'he` Scope @((Scrolling List `T'TT'I` Tree) i) at
      `ho'he` Scope @(Scrolling List `T'I` Tree i) at

  restoring (U_T_I_TT_I (These focus shafted)) scrolling_list_tree = unwrap focus `lu` (U_T_I_TT_I
    `hv__` Only (Tree `hv` unwrap focus `hv__` to @(Nonempty List) `hv` scrolling_list_tree `yo` unwrap @AR `yi` unwrap @AR)
     `lu` unwrap shafted)

instance Mapping U_I_II U_I_II AR AR
 (Construction Optional)
 (Only `P'T'I'TT'I` (Reverse List `P'T'I'TT'I` Forward List)) where
 mapping = rewrap / \from (Root x xs) ->
  U_T_I_TT_I (Only (from x) `lu` U_T_I_TT_I (Labeled (Empty @List Unit) `lu` (Labeled (T'TT'I (xs `yo` R_U_I_T_I) `yo` from))))

instance Mapping U_I_II U_I_II AR AR
  (Only `P'T'I'TT'I` (Reverse List `P'T'I'TT'I` Forward List))
  (Construction Optional) where
 mapping = rewrap / \from (U_T_I_TT_I (These (Identity x) (U_T_I_TT_I (These l r)))) ->
  let f = State `ha` Transition `ha` push @(Nonempty List) `ha` from
  in enter @(State (Nonempty List _))
   -- TODO: replace with `yuk___'yokl` operator
   `yuk___` New (unwrap l `yokl` Prior `ha` New `ha` f)
   `yuk___` New (unwrap r `yokl` Forth `ha` New `ha` f)
   `he'he'hv_____` Construct `ha` (\x' -> Item x' `ha` Last `hv` Unit) `hv` from x
   `yi_____` that

-- TODO: it's here temporaly, I should find a way to generalize it
adjust :: Shifter List `AR_` Supertype (Event `WR` Sliding List item `WR` Optional item)
adjust way x = is
 `li` is `hu` (by None `lu` x)
 `la` is `ho'he` foi @_ @AR Some
 `li` (extend_passed `lv` extend_future `li` way) `he'he'hv` x where

 extend_passed = enter @(State `WR` Sliding List _ `JNT` Halts)
  `yuk____` New `ha` State `hv__` Event `hv` pop @List `ha_` Scope `ha` shaft `hv` by Passed
  `yok____` Try
  `yok____` New `ha` State `ha__` Event `ha` push `ho_'ha` Scope `hv` focus

 extend_future = enter @(State `WR` Sliding List _ `JNT` Halts)
  `yuk____` New `ha` State `hv__` Event `hv` pop `ha_` Scope `ha` shaft `hv` by Future
  `yok____` Try
  `yok____` New `ha` State `ha__` Event `ha` window_future `ho_'ha` Scope `hv` focus

 window_future r w = (is @(List _) w `yokl` Prior `ha` New `ha` State `ha` Event `ha` push `he'he'hv___` List `ha` Item r `ha` Last `hv` Unit) `yui` r

locate :: forall window datastructure item .
 Shiftable window datastructure item =>
 Field (window item) (Supertype (Shifting window datastructure item)) =>
 Wrapper AR (Shifting window datastructure item) =>
 Shifter datastructure `P` Predicate (window item) `AR_` Supertype (Event `WR` Shifting window datastructure item `WR_` Optional (Shifting window datastructure item))
locate (These way predicate) x = foi Some `ha` auto `la` is `ho'he` foi @_ @AR (None `hu` by None) `li` locate' `he'he'hv` x where

 locate' = enter @(State `WR` Shifting window datastructure item `JNT` Reach `WR` Shifting window datastructure item)
  `yuk____` State `ho` New `hv____` Event `hv___` auto `ho'yoi` unwrap predicate `ha___'he` Scope `hv` at @(window item)
  `yok____` State `ho` New `ha____` Event `ha___` (Next `hu_` shift `hv` way `ho'yoi` Continue `la_` Same `hu_` auto `ho'yoi` Reach)
  `yok____` Check `ha__` Reach `la` Continue
  `yok____` Retry `ha__` Interrupt `hu` by Ok `la` Again `ha` Same `hu` by Reach

-- TODO: rewind :: forall window datastructure item .