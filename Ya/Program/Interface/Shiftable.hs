module Ya.Program.Interface.Shiftable where

import Ya.Algebra
import Ya.Operators
import Ya.Program.Patterns
import Ya.Program.Primitive
import Ya.Program.Labels

import Ya.Program.Interface.Fieldable
import Ya.Program.Interface.Matchable
import Ya.Program.Interface.Stackable

type family Shafted t where
 Shafted List = Twice `T'TT'I` List
 Shafted Tree = List `T'TT'I` (Alone `P'T'I'TT'I` Shafted List `T'TT'I` Tree)

type Unfolding t tt = t `P'T'I'TT'I` Twice `T'TT'I` List `T'TT'I` tt

type family Shifting t tt = r | r -> t tt where
 Shifting t (Maybe `T'TT'I` Construction Maybe) = t `P'T'I'TT'I` Twice `T'TT'I` List
 Shifting Alone (Construction List) = Tree `P'T'I'TT'I` List `T'TT'I` (Alone `P'T'I'TT'I` Twice `T'TT'I` List `T'TT'I` Tree)

type family Shifter t where
 Shifter (Maybe `T'TT'I` Construction Maybe) = Unit `S` Unit
 Shifter (Construction (Twice `T'TT'I` Maybe)) = Unit `S` Unit `S` Unit
 Shifter (Construction List) = Unit `S` Unit `S_` Unit `S` Unit

-- TODO: Replace with a natural transformation?
-- focus :: Supertype (Scope `T'I` Shifting t tt i `T'I` t i)

-- TODO: flux, axis, rest
class Shiftable t tt where
 shift :: Shifter tt `AR___` Supertype (Event `T'I` Shifting t tt i `T'I` Maybe (t i))
 spot :: Shifter tt `P` Match (t i) `AR_` Supertype (Event `T'I` Shifting t tt i `T'I` Maybe `T` Shifting t tt i)

type Scrolling t = Shifting Alone t

type Scrollable t = Shiftable Alone t

pattern Range :: forall t e . Scrollable t => e `AR__` Alone `L` Scrolling t `T` Void `T` e
pattern Range x = Label (Alone x)

type Sliding t = Shifting List t

pattern Aback x = This x :: Shifter List
pattern Ahead x = That x :: Shifter List

pattern Above x = This x :: Shifter List
pattern Below x = That x :: Shifter List

instance Shiftable Alone (Maybe `T'TT'I` Construction Maybe) where
 shift :: forall i . Shifter List `AR___` Supertype (Event `T'I` Shifting Alone List i `T'I` Maybe (Alone i))
 shift way x = is `li` Empty `hu` (Empty Unit `lu` x) `la` is `ho'he` foi @_ @(AR) Exist `li` _shift_ `he'he'hv` x where

  _shift_ = intro @(Halts `JNT` State `T` Scrolling List i) Unit
   `yuk__` Apply `ha` State `hv___` Event `hv` pop `ha__` Scope `hv` at @(Shafted List i) `ho_'he` Scope `ha` rep @Twice `ha` (Back `la` Fore) `hv` way
   `yok__` Check
   `yok__` Apply `ha` State `ha___` Event `ha` relay `ho__'ha` Scope `hv` at @(Alone i) `ho_'he` Scope `hv` it
   `yok__` Apply `ha` State `ha___` Event `ha` push `ho__'ha` Scope `hv` at @(Shafted List i) `ho_'he` Scope `ha` rep `ha` (Fore `la` Back) `hv` way
   -- TODO: there it is - if I use `Lease` label instead of `Apply` state doesn't change
   `yuk__` Apply `ha` State `hv__` Event `hv` fetch `ha_` Scope `hv` at @(Alone i)

 spot :: forall i . Shifter List `P` Match (Alone i) `AR_` Supertype (Event `T'I` Shifting Alone List i `T'I` Maybe `T` Shifting Alone List i)
 spot (These way predicate) x = foi Exist `ha` fetch `la` is `ho'he` foi @_ @(AR) (Empty `hu` Empty Unit) `li` _spot_ `he'he'hv` x where

  found (These w sl) = unwrap (predicate `he'hv` w) `yui` sl `yiu` sl

  _spot_ = intro @(Stops `T` Scrolling List i `JNT` State `T` Scrolling List i) Unit
   `yuk____` Lease `ha` State `hv___` Event `hv__` fetch `ha__` Scope `hv` at @(Alone i) `lo` Scope `hv` it
   `yok____` Check `ha` Stops `ha___` not `ha` found
   `yuk____` Apply `ha` State `hv___` Event `hv__` shift `hv` way
   `yok____` Retry `ha` is `ha__` Break `hu` Ok Unit `la` Again `hu` Reach Unit

instance Shiftable List (Maybe `T'TT'I` Construction Maybe) where
 shift :: forall i . Shifter List `AR___` Supertype (Event `T'I` Shifting List List i `T'I` Maybe (List i))
 shift way x = is
  `li` is `hu` (Empty Unit `lu` x)
  `la` is `ho'he` foi @_ @(AR) Exist
  `li` (slide_passed `lv` slide_future `li` way) `he'he'hv` x where

  slide_future = intro @(Halts `JNT` State `T` Sliding List i) Unit
   `yuk____` Apply `ha` State `hv___` Event `hv` pop `ha_` Scope `hv` at @(List _)
   `yok____` Check
   `yok____` Apply `ha` State `ha___` Event `ha` push `ho__'ha` Scope `hv` at @(Shafted List i) `ho_'he` Scope `ha` rep `hv'he` Aback
   `yuk____` Apply `ha` State `hv___` Event `hv` pop `ha__` Scope `hv` at @(Shafted List i) `ho_'he` Scope `ha` rep `hv'he` Ahead
   `yok____` Check
   `yok____` Apply `ha` State `ha____` Event `ha` window_future `ho_'ha` Scope `hv` at @(List _)

  slide_passed = intro @(Halts `JNT` State `T` Sliding List _) `hv` Unit
   `yuk____` Apply `ha` State `hv___` Event `hv` pop `ha__` Scope `hv` at @(Shafted List i) `ho_'he` Scope `ha` rep `hv'he` Aback
   `yok____` Check
   `yok____` Apply `ha` State `ha___` Event `ha` window_extract_last `ho_'ha` Scope `hv` at @(List _)
   `yok____` Check
   `yok____` Apply `ha` State `ha___` Event `ha` push `ho__'ha` Scope `hv` at @(Shafted List i) `ho_'he` Scope `ha` rep `hv'he` Ahead
   `yuk____` Apply `ha` State `hv___` Event `hv` fetch `ha__` Scope `hv` at @(List _)

  window_future :: i `AR_____` List i `AR___` List i `P` List i
  window_future r w = is @(List _) w `yokl` Prior `ha` Apply `ha` State `ha` Event `ha` push `he'he'hv___` List `ha` Exist `ha` Build `ha` Item r `ha` T'I'II `ha` This `hv` Unit -- `yui` r

  window_extract_last passed w =
   push @List passed w `yi` that
    `yokl` Forth `ha` Apply `ha` State `ha` Event `ha` push
    `he'he'hv___` empty @List
    `yi__` that `ho` pop @List

-- TODO: define instances to compose attributes like: attr `ha` attr

-- pattern Broad x = This x :: Shifter Tree
-- pattern Level x = That x :: Shifter Tree

 --  _spot_ = intro @(Stops `T` Scrolling Tree i `JNT` State `T` Scrolling Tree i) Unit
 --   `yuk____` Lease `ha` State `hv____` Event `hv___` fetch
 --     `ha___` Scope `hv` at @(Scrolling List `T'TT'I` Tree `T'I_` i)
 --       `ho_` Scope `hv` at @(Alone `T'I_` Tree `T` i)
 --        `lo` Scope `hv` it @(Scrolling Tree i)
 --   `yok____` Check `ha` Stops `ha___` not `ha` found
 --   `yuk____` Apply `ha` State `hv___` Event `hv__` shift `hv` way
 --   `yok____` Retry `ha` is `ha__` Break `hu` Ok Unit `la` Again `hu` Reach Unit

instance Mapping T'I'II T'I'II (AR) (AR) (Construction Maybe) (I `P'T'I'TT'I` Twice `T'TT'I` List) where
 mapping = rewrap `identity` \source (Root x xs) ->
  T'TT'I'TTT'I (Alone (source x) `lu` T'TT'I (T'I'I (empty @List `lu` (T'TT'I (xs `yo` F'T'I'TT'I) `yo` source))))

instance Mapping T'I'II T'I'II (AR) (AR) (I `P'T'I'TT'I` Twice `T'TT'I` List) (Construction Maybe) where
 mapping = rewrap `identity` \source (T'TT'I'TTT'I (These (Identity x) (T'TT'I (T'I'I (These l r))))) ->
  (l `yokl` Forth `ha` Apply `ha` State `ha` Event `ha` push)
   `he'he'hv__` Empty `hu` intro @(Nonempty List) x `la` push x `ho` that `li` r
   `yi_` that `ho'yo` source

-- instance Mapping T'I'II T'I'II (AR) (AR)
--  ((Shifting Alone List `T'TT'I` Tree `P'T'I'TT'I` Unfoldings Alone Tree) `T'TT'I` t `L` t `T` Void `L` (Shifting Alone List `T'TT'I` Tree `P'T'I'TT'I` Unfoldings Alone Tree) `T` Void)
--  ((Shifting Alone List `T'TT'I` Tree `P'T'I'TT'I` Unfoldings Alone Tree) `TT'T'I` t) where
--  mapping = rewrap `identity` \source -> rewrap `identity`
--   \(T'TT'I'TTT'I (These x (T'TT'I (T'I'I (These l r))))) ->

-- spot :: forall t tt i .
--  Shiftable t tt =>
--  Fieldable (t i) (Shifting t tt i) =>
--  Wrapper (AR) (Shifting t tt i) =>
--  Shifter tt `P` Match (t i) `AR_` Supertype (Event `T'I` Shifting t tt i `T'I` Maybe (Shifting t tt i))
-- spot (These way predicate) x = foi Exist `ha` fetch `la` is `ho'he` foi @_ @(AR) (Empty `hu` by Empty) `li` _spot_ `he'he'hv` x where

--  found (These w sl) = unwrap (predicate `he'hv` w) `yui` sl `yiu` sl

--  _spot_ = intro @(Stops `T` Shifting t tt i `JNT` State `T` Shifting t tt i) Unit
--   `yuk____` Lease `ha` State `hv___` Event `hv__` fetch `ha__` Scope `hv` at @(t i) `lo` Scope `hv` it
--   `yok____` Check `ha` Stops `ha___` not `ha` found
--   `yuk____` Apply `ha` State `hv___` Event `hv__` shift `hv` way
--   `yok____` Retry `ha` is `ha__` Break `hu` by Ok `la` Again `hu` Reach Unit

rewind :: forall t tt i .
 Shiftable t tt =>
 Shifter tt `AR___` Supertype (Event `T'I` Shifting t tt i `T'I` Unit)
rewind way = unwrap @(AR) `ha` unwrap @(AR)
 `hv_______` intro @(State `T` Shifting t tt i) Unit
   `yuk____` Apply `ha` State `ha` Event `hv` shift way
   `yok____` Retry `ha__` Exist `la` Exist `hu` Empty Unit

pattern Shrink e = This e
pattern Expand e = That e

-- TODO: it's here temporaly, I should find a way to generalize it:
adjust :: forall i . Unit `S` Unit `P` Shifter List `AR_` Supertype (Event `T'I` Sliding List i `T'I` Maybe i)
adjust way x = is `hu` (Empty Unit `lu` x) `la` is `ho'he` foi @_ @(AR) Exist `li` router way `he'he'hv` x where

 -- TODO: there should be a way to shorten it
 router (These (This _) (This _)) = shrink_passed
 router (These (This _) (That _)) = shrink_future
 router (These (That _) (This _)) = expand_passed
 router (These (That _) (That _)) = expand_future

 -- [3 2 1] (4 5 6) [7 8 9] ---> [2 1] (3 4 5 6) [7 8 9]
 expand_passed = intro @(Halts `JNT` State `T` Sliding List _) Unit
  `yuk____` Apply `ha` State `hv___` Event `hv` pop @List `ha__` Scope `hv` at @(Shafted List i) `ho_'he` Scope `ha` rep `hv'he` Aback
  `yok____` Check
  `yok____` Apply `ha` State `ha___` Event `ha` push `ho_'ha` Scope `hv` at @(List i)

 -- [3 2 1] (4 5 6) [7 8 9] ---> [4 3 2 1] (5 6) [7 8 9]
 shrink_passed = intro @(Halts `JNT` State `T` Sliding List i) Unit
  `yuk____` Apply `ha` State `hv___` Event `hv` pop @List `ha_` Scope `hv` at @(List i)
  `yok____` Check
  `yok____` Apply `ha` State `ha___` Event `ha` push `ho__'ha` Scope `hv` at @(Shafted List i) `ho_'he` Scope `ha` rep `hv'he` Aback

 -- [3 2 1] (4 5 6) [7 8 9] ---> [3 2 1] (4 5 6 7) [8 9]
 expand_future = intro @(Halts `JNT` State `T` Sliding List _) Unit
  `yuk____` Apply `ha` State `hv___` Event `hv` pop `ha__` Scope `hv` at @(Shafted List i) `ho_'he` Scope `ha` rep `hv'he` Ahead
  `yok____` Check
  `yok____` Apply `ha` State `ha___` Event `ha` window_future `ho_'ha` Scope `hv` at @(List i)

 window_future r w = (is @(List _) w `yokl` Prior `ha` Apply `ha` State `ha` Event `ha` push `he'he'hv___` List `ha` Exist `ha` Build `ha` Item r `ha` T'I'II `ha` This `hv` Unit) `yui` r

 -- [3 2 1] (4 5 6) [7 8 9] ---> [3 2 1] (4 5) [6 7 8 9]
 shrink_future = intro @(Halts `JNT` State `T` Sliding List _) Unit
  `yuk____` Apply `ha` State `hv___` Event `hv` get_last_window_item `ha_` Scope `hv` at @(List i)
  `yok____` Apply `ha` State `ha___` Event `ha` rearrange_window_back `ho_'ha` Scope `hv` at @(List i)
  `yok____` Check
  `yok____` Apply `ha` State `ha___` Event `ha` push `ho__'ha` Scope `hv` at @(Shafted List i) `ho_'he` Scope `ha` rep `hv'he` Ahead

 get_last_window_item window = window
  `yokl` Apply `ha` State `ha` Event `ha` push @List `ho` Prior
  `yuk_` Apply `ha` State `ha` Event `hv` pop @List
  `he'he'hv_____` empty @List

 rearrange_window_back popped window =
  (window `yokl` Apply `ha` State `ha` Event `ha` push @List `ho` Prior
  `he'he'hv_____` empty @List) `yui` popped
