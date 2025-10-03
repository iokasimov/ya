module Ya.Program.Interface.Instances where

import Ya.Algebra
import Ya.Operators
import Ya.Program.Patterns
import Ya.Program.Primitive
import Ya.Program.Labels

import Ya.Program.Interface.Fieldable
import Ya.Program.Interface.Matchable
import Ya.Program.Interface.Stackable
import Ya.Program.Interface.Shiftable

instance Mapping T'I'II T'I'II (AR) (AR) (Construction Optional) List where
 mapping = rewrap `identity` \from -> rewrap `li_` wrap `ho'yo` from `ho` Exist

pattern Stump :: forall i e .
 Component (AR) (S'I'II i) (S'I'II Unit) =>
 S'I'II i e `AR__` S'I'II i `L` S'I'II i `T` Void `T` e
pattern Stump x = Label x

instance Mapping T'I'II T'I'II (AR) (AR) (S'I'II e `L` S'I'II e `T` Void) (S'I'II Unit) where
 mapping = rewrap `identity` \from ->
  rewrap `identity` ((This `compose` constant Unit `la` That `compose` from) `compose` unwrap)

pattern Spare :: forall i ii .
 Component (AR) ((P'II'I i `T'TT'I` S'I'II Unit) `L` (P'II'I i `T'TT'I` S'I'II Unit) `T` Void) (S'I'II i) =>
 P'II'I i (S'I'II Unit ii) `AR___` (P'II'I i `T'TT'I` S'I'II Unit) `L` (P'II'I i `T'TT'I` S'I'II Unit) `T` Void `T` ii
pattern Spare x = Label (T'TT'I x)

instance Mapping T'I'II T'I'II (AR) (AR) ((P'II'I i `T'TT'I` S'I'II Unit) `L` (P'II'I i `T'TT'I` S'I'II Unit) `T` Void) (S'I'II i) where
 mapping = rewrap `identity` \from (Label (T'TT'I (T'II'I (These x i)))) -> Empty `hu` Error i `la` Valid `ha` from `li` x

pattern Aloft :: forall t e .
 Component (AR) (((Alone `P'T'I'TT'I` Shafted List) `P'T'I'TT'I` Tree) `L` ((Alone `P'T'I'TT'I` Shafted List) `P'T'I'TT'I` Tree) `T` Void) Tree =>
 (t `P'T'I'TT'I` Tree) e `AR___` (t `P'T'I'TT'I` Tree) `L` (t `P'T'I'TT'I` Tree) `T` Void `T` e
pattern Aloft x = Label x

instance Mapping T'I'II T'I'II Arrow Arrow (((Alone `P'T'I'TT'I` Shafted List) `P'T'I'TT'I` Tree) `L` ((Alone `P'T'I'TT'I` Shafted List) `P'T'I'TT'I` Tree) `T` Void) Tree where
  mapping = rewrap `identity` \from (Label (T'TT'I'TTT'I (These scrolling_list tree))) ->
   rewrap (\x -> Alone tree `lu` that @(Shafted List _) `ho'yo` intro @Tree @(AR) `hv` x) scrolling_list
    `yi` is @(Scrolling List _) `ho` to @(Nonempty List) `ho` to @List `ho'yo` unwrap @(AR)
    `yi` this @(Alone _) `ho'he` Root `hv` unwrap scrolling_list
    `yo` from
