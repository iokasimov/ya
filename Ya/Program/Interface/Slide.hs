module Ya.Program.Interface.Slide where

import Ya.Algebra
import Ya.Program.Patterns
import Ya.Program.Primitive
import Ya.Program.Labels

import Ya.Program.Interface.Field
import Ya.Program.Interface.Stack
import Ya.Program.Interface.Scroll

type family Sliding datastructure = result | result -> datastructure where
 -- Ideally there should be `Queue` instead of `List`, but we don't have it for now
 Sliding (Optional `T'TT'I` Construction Optional) = List `LM'T'I'TT'I` Shafted List

class Scrollable datastructure item
 => Slidable datastructure item where
 slide :: Scroller datastructure `AR_` Automation `WR` Sliding datastructure item `WR` Supertype (Scrolled datastructure item) `WR` Sliding datastructure item
 extend :: Scroller datastructure `AR_` Automation `WR` Sliding datastructure item `WR` Supertype (Scrolled datastructure item) `WR` Sliding datastructure item

instance Slidable (Optional `T'TT'I` Construction Optional) item where
 slide way x = is
  `li` is `hu` (This () `lu` x)
  `la` is `ho'he` foi @_ @Arrow That
  `li` (slide_passed `lv` slide_future `li` way) `he'he'hv` x where

  slide_future = enter @(State `WR` Sliding List item `JNT` Halts)
   `yuk____` New `ha` State `hv___` Event `hv` pop
   `ha__'he` Scope `hv` at @(List item)
   `yok____` Try `ha` Maybe
   `yok____` New `ha` State `ha__` Event `ha` push
   `ho_'ha'he` Scope @(Shafted List item) at
      `ho'he` Scope @(Reverse List item) at
      `ho'he` Scope it
   `yuk____` New `ha` State `hv____` Event `hv` pop
   `ha___'he` Scope `hv` at @(Shafted List item)
      `ho'he` Scope @(Forward List item) at
      `ho'he` Scope it
   `yok____` Try `ha` Maybe
   `yok____` New `ha` State `ha____` Event `ha` window_future
   `ho_'ha'he` Scope `hv` at @(List item)

  slide_passed = enter @(State `WR` Sliding List item `JNT` Halts)
   `yuk____` New `ha` State `hv____` Event `hv` pop
   `ha___'he` Scope @(Shafted List item) at
      `ho'he` Scope @(Reverse List item) at
      `ho'he` Scope it
   `yok____` Try `ha` Maybe
   `yok____` New `ha` State `ha__` Event `ha` window_extract_last
   `ho_'ha'he` Scope `hv` at @(List item)
   `yok____` Try `ha` Maybe
   `yok____` New `ha` State `ha__` Event `ha` push
   `ho_'ha'he` Scope @(Shafted List item) at
      `ho'he` Scope @(Forward List item) at
      `ho'he` Scope it

  window_future r w = (is @(List _) w `yokl` Prior `ha` New `ha` State `ha` Event `ha` push `he'he'hv___` List `ha` Item r `ha` Last `hv` Unit) `yui` r

  window_extract_last passed window =
   push @List passed window `yi` that
    `yokl` Forth `ha` New `ha` State `ha` Event `ha` push
    `he'he'hv___` by `hv` Empty @List
    `yi__` that `ho` pop @List

 extend way x = is
  `li` is `hu` (This () `lu` x)
  `la` is `ho'he` foi @_ @Arrow That
  `li` (extend_passed `lv` extend_future `li` way) `he'he'hv` x where

  extend_passed = enter @(State `WR` Sliding List item `JNT` Halts)
   `yuk____` New `ha` State `hv____` Event `hv` pop @List
   `ha___'he` Scope @(Shafted List item) at
      `ho'he` Scope @(Reverse List item) at
      `ho'he` Scope it
   `yok____` Try `ha` Maybe
   `yok____` New `ha` State `ha__` Event `ha` push
   `ho_'ha'he` Scope `hv` at @(List item)

  extend_future = enter @(State `WR` Sliding List item `JNT` Halts)
   `yuk____` New `ha` State `hv____` Event `hv` pop
   `ha___'he` Scope `hv` at @(Shafted List item)
     `ho_'he` Scope `hv` at @(Forward List item) 
     `ho_'he` Scope `hv` it @(List item) -- @Transition
   `yok____` Try `ha` Maybe
   `yok____` New `ha` State `ha____` Event `ha` window_future
   `ho_'ha'he` Scope `hv` at @(List item)

  window_future r w = (is @(List _) w `yokl` Prior `ha` New `ha` State `ha` Event `ha` push `he'he'hv___` List `ha` Item r `ha` Last `hv` Unit) `yui` r
