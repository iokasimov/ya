module Ya.Program.Interface.Scroll where

import Ya.Algebra
import Ya.Program.Patterns
import Ya.Program.Primitive
import Ya.Program.Labels

import Ya.Program.Interface.Field
import Ya.Program.Interface.Match
import Ya.Program.Interface.Stack

type Leveled e = Scrolling List `T'TT'I` e

type Shafted e = Reverse e `P'T'I'TT'I` Forward e

type family Scrolling t = result | result -> t where
 Scrolling (Construction Singular) = Only `P'T'I'TT'I` (Stream `P'T'I'TT'I` Stream)
 Scrolling (Optional `T'TT'I` Construction Optional) = Only `P'T'I'TT'I` Shafted List
 Scrolling (Construction List) = Scrolling List `T'TT'I` Tree `P'T'I'TT'I` Reverse List `T'TT'I` (Only `P'T'I'TT'I` Shafted List `T'TT'I` Tree)

type family Scroller t where
 Scroller Stream = () `S` ()
 Scroller (Optional `T'TT'I` Construction Optional) = () `S` ()
 Scroller (Construction (U_I_I P `T'TT'I` Optional)) = () `S` () `S` ()
 Scroller (Construction List) = (Unit `S` Unit) `S` (Unit `S` Unit)

type family Scrolled t where
 Scrolled Stream = Only
 Scrolled (Optional `T'TT'I` Construction Optional) = Optional
 Scrolled (Construction (U_I_I P `T'TT'I` Optional)) = Optional
 Scrolled (Construction List) = Optional

class Scrollable t i where
 scroll :: Scroller t `AR___` Supertype (Transition `WR` Scrolling t i `WR` Scrolled t i)
 locate :: Scroller t `P` Predicate i `AR__` Supertype (Transition `WR` Scrolling t i `WR_` Optional `WR` Scrolling t i)

instance Scrollable (Optional `T'TT'I` Construction Optional) i where
 scroll way x = is `li` None `hu` (None Unit `lu` x) `la` is `ho'he` foi @_ @Arrow Some `li` scroll' `he'he'hv` x where

  scroll' = enter @(State `WR` Scrolling List i `JNT` Halts)
   `yuk__` New `ha` State `hv__` Transition `hv` pop `ha_'he` Scope @(Shafted List i) at `ho'he` path way
   `yok__` Try `ha` Maybe
   -- `yok__` New `ha` State `ha__` Transition `ha` (auto `ho'hu`) `ho_'ha` Scope @(Focused i) at `he'ho'he` Scope it
   `yok__` New `ha` State `ha__` Transition `ha` switch `ho_'ha` Scope @(Focused i) at `he'ho'he` Scope it
   `yok__` New `ha` State `ha__` Transition `ha` push `ho_'ha` Scope @(Shafted List i) at `he'ho'he` path (not way)

  path = Back `hu_` Scope @(Reverse List i) at `ho'he` Scope it
   `la___` Fore `hu_` Scope @(Forward List i) at `ho'he` Scope it

 locate (These way predicate) x = foi Some `ha` auto `la` is `ho'he` foi @_ @Arrow (None `hu` by None) `li` locate' `he'he'hv` x where

  locate' = enter @(State `WR` Scrolling List i `JNT` Reach `WR` Scrolling List i)
   `yuk____` State `ho` New `hv____` Event `hv___` auto `ho'yoi` unwrap predicate `ha___'he` Scope `hv` at @(Focused i) `ho_'he` Scope `hv` it @i
   `yok____` State `ho` New `ha____` Event `ha___` (Next `hu_` scroll `hv` way `ho'yoi` Continue `la_` Same `hu_` auto `ho'yoi` Reach)
   `yok____` Check `ha__` Reach `la` Continue
   `yok____` Retry `ha__` Interrupt `hu` by Ok `la` Again `ha` Same `hu` by Reach

-- TODO: define instances to compose attributes like: attr `ha` attr

-- TODO: implement `locate` method
instance Scrollable (Construction (Optional `T'TT'I` Construction Optional)) i where
 scroll way x = is
  `li` is `hu` (by None `lu` x)
  `la` is `ho'he` foi @_ @Arrow Some
  `li` (horizontally `la_` vertical_deep `la` vertical_up `li_` way) `he'he'hv` x where

  horizontally :: forall i . Way `AR___` State `WR` Scrolling Tree i `JNT` Halts `WR__` i
  horizontally way = enter @(State `WR` Scrolling Tree i `JNT` Halts)
   `yuk__` New `ha` State `hv__` Transition `hv` scroll way
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
   `yok____'he`  Try `ha` Maybe
   `yok____` New `ha` State `ha____` Transition
   `ha_` (\(These previous new) _ -> previous `lu` to @(Scrolling List) (new `yo` R_U_I_T_I))
   `ho_'ha'he` Scope @((Scrolling List `T'TT'I` Tree) i) at
      `ho'he` Scope @(Scrolling List `T'I` Tree i) at

  vertical_up :: forall i . Unit `AR___` State `WR` Scrolling Tree i `JNT` Halts `WR__` i
  vertical_up _ = enter @(State `WR` Scrolling Tree i `JNT` Halts)
   `yuk___` New `ha` State `hv__` Transition `hv` pop
   `ha_'he` Scope @((Reverse List `T'TT'I_` (Only `P'T'I'TT'I` Shafted List `T'TT'I` Tree)) i) at
   `ho'he'he` Scope @(List ((Only `P'T'I'TT'I` Shafted List `T'TT'I` Tree) i)) at
   `yok___` Try `ha` Maybe
   `yok___` New `ha` State `ha__` Transition `ha_` restoring
   `ho_'ha'he` Scope @((Scrolling List `T'TT'I` Tree) i) at
      `ho'he` Scope @(Scrolling List `T'I` Tree i) at

  restoring (U_T_I_TT_I (These focus shafted)) scrolling_list_tree = unwrap focus `lu` (U_T_I_TT_I
    `hv__` Only (Tree `hv` unwrap focus `hv__` to @(Nonempty List) `hv` scrolling_list_tree `yo` unwrap @AR `yi` unwrap @AR)
     `lu` unwrap shafted)

instance Mapping U_I_II U_I_II Arrow Arrow
 (Construction Optional)
 (Only `P'T'I'TT'I` (Reverse List `P'T'I'TT'I` Forward List)) where
 mapping = rewrap / \from (Root x xs) ->
  U_T_I_TT_I (Singular (from x) `lu` U_T_I_TT_I (Labeled (Empty @List ()) `lu` (Labeled (T'TT'I (xs `yo` R_U_I_T_I) `yo` from))))

instance Mapping U_I_II U_I_II Arrow Arrow
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
