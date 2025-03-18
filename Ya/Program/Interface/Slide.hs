module Ya.Program.Interface.Slide where

import Ya.Algebra
import Ya.Program.Patterns
import Ya.Program.Primitive
import Ya.Program.Labels

import Ya.Program.Interface.Field
import Ya.Program.Interface.Stack
import Ya.Program.Interface.Scroll

type family Sliding datastructure = result | result -> datastructure where
 -- TODO: Ideally there should be `Queue` instead of `List`, but we don't have it for now
 Sliding (Optional `T'TT'I` Construction Optional) = List `P'T'I'TT'I` Shafted List

class Scrollable datastructure item
 => Slidable datastructure item where
 slide :: Scroller datastructure `AR_` Automation `WR` Sliding datastructure item `WR` Scrolled datastructure item `WR` Sliding datastructure item
 extend :: Scroller datastructure `AR_` Automation `WR` Sliding datastructure item `WR` Scrolled datastructure item `WR` Sliding datastructure item

instance Slidable (Optional `T'TT'I` Construction Optional) item where
 slide way x = is
  `li` is `hu` (by None `lu` x)
  `la` is `ho'he` foi @_ @Arrow Some
  `li` (slide_passed `lv` slide_future `li` way) `he'he'hv` x where

  slide_future = enter @(State `WR` Sliding List item `JNT` Halts)
   `yuk____` New `ha` State `hv__` Event `hv` pop `ha_` Scope `hv` focus
   `yok____` Try `ha` Maybe
   `yok____` New `ha` State `ha__` Event `ha` push `ho_'ha` Scope `ha` shaft `hv` by Passed
   `yuk____` New `ha` State `hv____` Event `hv` pop `ha_` Scope `ha` shaft `hv` by Future
   `yok____` Try `ha` Maybe
   `yok____` New `ha` State `ha____` Event `ha` window_future `ho_'ha` Scope `hv` focus

  slide_passed = enter @(State `WR` Sliding List item `JNT` Halts)
   `yuk____` New `ha` State `hv__` Event `hv` pop `ha_` Scope `ha` shaft `hv` by Passed
   `yok____` Try `ha` Maybe
   `yok____` New `ha` State `ha__` Event `ha` window_extract_last `ho_'ha` Scope `hv` focus
   `yok____` Try `ha` Maybe
   `yok____` New `ha` State `ha__` Event `ha` push `ho_'ha` Scope `ha` shaft `hv` by Future

  window_future r w = (is @(List _) w `yokl` Prior `ha` New `ha` State `ha` Event `ha` push `he'he'hv___` List `ha` Item r `ha` Last `hv` Unit) `yui` r

  window_extract_last passed w =
   push @List passed w `yi` that
    `yokl` Forth `ha` New `ha` State `ha` Event `ha` push
    `he'he'hv___` by `hv` Empty @List
    `yi__` that `ho` pop @List

 extend way x = is
  `li` is `hu` (by None `lu` x)
  `la` is `ho'he` foi @_ @Arrow Some
  `li` (extend_passed `lv` extend_future `li` way) `he'he'hv` x where

  extend_passed = enter @(State `WR` Sliding List item `JNT` Halts)
   `yuk____` New `ha` State `hv____` Event `hv` pop @List `ha_` Scope `ha` shaft `hv` by Passed
   `yok____` Try `ha` Maybe
   `yok____` New `ha` State `ha__` Event `ha` push `ho_'ha` Scope `hv` focus

  extend_future = enter @(State `WR` Sliding List item `JNT` Halts)
   `yuk____` New `ha` State `hv____` Event `hv` pop `ha_` Scope `ha` shaft `hv` by Future
   `yok____` Try `ha` Maybe
   `yok____` New `ha` State `ha____` Event `ha` window_future `ho_'ha` Scope `hv` focus

  window_future r w = (is @(List _) w `yokl` Prior `ha` New `ha` State `ha` Event `ha` push `he'he'hv___` List `ha` Item r `ha` Last `hv` Unit) `yui` r
