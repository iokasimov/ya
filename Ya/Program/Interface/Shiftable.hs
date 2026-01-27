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

-- TODO: Rephasce with a natural transformation?
-- focus :: Supertype (Scope `T'I` Shifting t tt i `T'I` t i)

-- TODO: flux, axis, rest
class Shiftable t tt where
 shift :: Shifter tt `AR___` Supertype (Event `T'I` Shifting t tt i `T'I` Maybe (t i))
 spot :: Shifter tt `P` Match (t i) `AR_` Supertype (Event `T'I` Shifting t tt i `T'I` Maybe `T` Shifting t tt i)

type Scrolling t = Shifting Alone t

type Scrollable t = Shiftable Alone t

-- pattern Range :: forall t e . Scrollable t => e `AR__` Alone `L` Scrolling t `T` Void `T` e
pattern Range :: forall t tt e . (t ~ Scrolling tt, Scrollable tt) => e `AR__` Alone `L` t `T` Void `T` e
pattern Range x = Label (Alone x)

type Sliding t = Shifting List t

-- TODO: define instances to compose attributes like: attr `ha` attr

-- pattern Broad x = This x :: Shifter Tree
-- pattern Level x = That x :: Shifter Tree

 --  _spot_ = intro @(Stops `T` Scrolling Tree i `JNT` State `T` Scrolling Tree i) Unit
 --   `yuk____` Lease `ha` State `hc____` Event `hc___` fetch
 --     `ha___` Scope `hc` at @(Scrolling List `T'TT'I` Tree `T'I_` i)
 --       `ho_` Scope `hc` at @(Alone `T'I_` Tree `T` i)
 --        `hop` Scope `hc` it @(Scrolling Tree i)
 --   `yok____` Check `ha` Stops `ha___` not `ha` found
 --   `yuk____` Apply `ha` State `hc___` Event `hc__` shift `hc` way
 --   `yok____` Retry `ha` is `ha__` Break `hu` Ok Unit `has` Again `hu` Reach Unit

instance Mapping T'I'II T'I'II (AR) (AR)
 (Construction Maybe `L` (I `P'T'I'TT'I` Twice `T'TT'I` List) `T` (Void))
 (I `P'T'I'TT'I` Twice `T'TT'I` List) where
 mapping = rewrap `hc` \source (Label (Root x xs)) ->
  Alone `hc` source x `hjd___` empty @List `hjd_` T'TT'I (xs `yo` F'T'I'TT'I) `yo` source

instance Mapping T'I'II T'I'II (AR) (AR) ((I `P'T'I'TT'I` Twice `T'TT'I` List) `L` Construction Maybe `T` Void) (Construction Maybe) where
 mapping = rewrap `hc` \source (Label (T'TT'I'TTT'I (These (Identity x) (T'TT'I (T'I'I (These l r)))))) ->
  l `yokl` Forth `ha` Apply `ha` State `ha` Event `ha` push
  `hc___` Empty `hu` (x `ryu` Enter @(Nonempty List)) `has` push x `ho` that `hc_` r
  `yi__` that `ho'yo` source

-- instance Mapping T'I'II T'I'II (AR) (AR)
--  ((Shifting Alone List `T'TT'I` Tree `P'T'I'TT'I` Unfoldings Alone Tree) `T'TT'I` t `L` t `T` Void `L` (Shifting Alone List `T'TT'I` Tree `P'T'I'TT'I` Unfoldings Alone Tree) `T` Void)
--  ((Shifting Alone List `T'TT'I` Tree `P'T'I'TT'I` Unfoldings Alone Tree) `TT'T'I` t) where
--  mapping = rewrap `hc` \source -> rewrap `identity`
--   \(T'TT'I'TTT'I (These x (T'TT'I (T'I'I (These l r))))) ->

-- spot :: forall t tt i .
--  Shiftable t tt =>
--  Fieldable (t i) (Shifting t tt i) =>
--  Wrapper (AR) (Shifting t tt i) =>
--  Shifter tt `P` Match (t i) `AR_` Supertype (Event `T'I` Shifting t tt i `T'I` Maybe (Shifting t tt i))
-- spot (These way predicate) x = foi Exist `ha` fetch `has` is `ho'st` foi @_ @(AR) (Empty `hu` by Empty) `li` _spot_ `hc` x where

--  found (These w sl) = super (predicate `hc` w) `yui` sl `yiu` sl

--  _spot_ = intro @(Stops `T` Shifting t tt i `JNT` State `T` Shifting t tt i) Unit
--   `yuk____` Lease `ha` State `hc___` Event `hc__` fetch `ha__` Scope `hc` at @(t i) `hop` Scope `hc` it
--   `yok____` Check `ha` Stops `ha___` not `ha` found
--   `yuk____` Apply `ha` State `hc___` Event `hc__` shift `hc` way
--   `yok____` Retry `ha` is `ha__` Break `hu` by Ok `has` Again `hu` Reach Unit

-- rewind :: forall t tt i .
--  Shiftable t tt =>
--  Shifter tt `AR___` Supertype (Event `T'I` Shifting t tt i `T'I` Unit)
-- rewind way = super @(AR) `ha` super @(AR)
--  `hc____` intro @(State `T` Shifting t tt i) Unit
--    `yuk_` Apply `ha` State `ha` Event `hc` shift way
--    `yok_` Retry `ha__` Exist `has` Exist `hu` Empty Unit

pattern Shrink e = This e
pattern Expand e = That e

-- TODO: it's here temporaly, I should find a way to generalize it:
-- adjust :: forall i . Unit `S` Unit `P` Shifter List `AR_` Supertype (Event `T'I` Sliding List i `T'I` Maybe i)
-- adjust way x = is `hu` (Empty Unit `lu` x) `has` is `ho'st` foi @_ @(AR) Exist `li` router way `hc` x where

--  -- TODO: there should be a way to shorten it
--  router (These (This _) (This _)) = shrink_passed
--  router (These (This _) (That _)) = shrink_future
--  router (These (That _) (This _)) = expand_passed
--  router (These (That _) (That _)) = expand_future

--  -- [3 2 1] (4 5 6) [7 8 9] ---> [2 1] (3 4 5 6) [7 8 9]
--  expand_passed = intro @(Halts `JNT` State `T` Sliding List _) Unit
--   `yuk____` Apply `ha` State `hc___` Event `hc` pop @List `ha__` Scope `hc` at @(Shafted List i) `ho_'st` Scope `ha` rep `hc'st` Aback
--   `yok____` Check
--   `yok____` Apply `ha` State `ha___` Event `ha` push `ho_'ha` Scope `hc` at @(List i)

--  -- [3 2 1] (4 5 6) [7 8 9] ---> [4 3 2 1] (5 6) [7 8 9]
--  shrink_passed = intro @(Halts `JNT` State `T` Sliding List i) Unit
--   `yuk____` Apply `ha` State `hc___` Event `hc` pop @List `ha_` Scope `hc` at @(List i)
--   `yok____` Check
--   `yok____` Apply `ha` State `ha___` Event `ha` push `ho__'ha` Scope `hc` at @(Shafted List i) `ho_'st` Scope `ha` rep `hc'st` Aback

--  -- [3 2 1] (4 5 6) [7 8 9] ---> [3 2 1] (4 5 6 7) [8 9]
--  expand_future = intro @(Halts `JNT` State `T` Sliding List _) Unit
--   `yuk____` Apply `ha` State `hc___` Event `hc` pop `ha__` Scope `hc` at @(Shafted List i) `ho_'st` Scope `ha` rep `hc'st` Ahead
--   `yok____` Check
--   `yok____` Apply `ha` State `ha___` Event `ha` window_future `ho_'ha` Scope `hc` at @(List i)

--  window_future r w = (is @(List _) w `yokl` Prior `ha` Apply `ha` State `ha` Event `ha` push `hc___` List `ha` Exist `ha` Build `ha` Item r `ha` T'I'II `ha` This `hc` Unit) `yui` r

--  -- [3 2 1] (4 5 6) [7 8 9] ---> [3 2 1] (4 5) [6 7 8 9]
--  shrink_future = intro @(Halts `JNT` State `T` Sliding List _) Unit
--   `yuk____` Apply `ha` State `hc___` Event `hc` get_hasst_window_item `ha_` Scope `hc` at @(List i)
--   `yok____` Apply `ha` State `ha___` Event `ha` rearrange_window_back `ho_'ha` Scope `hc` at @(List i)
--   `yok____` Check
--   `yok____` Apply `ha` State `ha___` Event `ha` push `ho__'ha` Scope `hc` at @(Shafted List i) `ho_'st` Scope `ha` rep `hc'st` Ahead

--  get_hasst_window_item window = window
--   `yokl` Apply `ha` State `ha` Event `ha` push @List `ho` Prior
--   `yuk_` Apply `ha` State `ha` Event `hc` pop @List
--   `hc_____` empty @List

--  rearrange_window_back popped window =
--   (window `yokl` Apply `ha` State `ha` Event `ha` push @List `ho` Prior
--   `hc_____` empty @List) `yui` popped
