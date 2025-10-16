{-# LANGUAGE UndecidableInstances #-}
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

instance Mapping T'I'II T'I'II (AR) (AR) (((Alone `P'T'I'TT'I` Shafted List) `P'T'I'TT'I` Tree) `L` ((Alone `P'T'I'TT'I` Shafted List) `P'T'I'TT'I` Tree) `T` Void) Tree where
  mapping = rewrap `identity` \from (Label (T'TT'I'TTT'I (These scrolling_list tree))) ->
   rewrap (\x -> Alone tree `lu` that @(Shafted List _) `ho'yo` intro @Tree @(AR) `hv` x) scrolling_list
    `yi` is @(Scrolling List _) `ho` to @(Nonempty List) `ho` to @List `ho'yo` unwrap @(AR)
    `yi` this @(Alone _) `ho'he` Root `hv` unwrap scrolling_list
    `yo` from

pattern Alter :: forall t i .
 Component (AR) (T'I'I t `L` T'I'I t `T` Void) (T'I'I t) =>
 T'I'I t i `AR__` T'I'I t `L` T'I'I t `T` Void `T` i
pattern Alter x = Label x

instance Mapping T'I'II T'I'II (AR) (AR) (T'I'I P `L` T'I'I P `T` Void) (T'I'I P) where
 mapping = rewrap `identity` \from -> rewrap `identity` (from `ha` that `lo` from `ha` this `ha__` unwrap @(AR))

instance Mapping T'I'II T'I'II (AR) (AR) (T'I'I S `L` T'I'I S `T` Void) (T'I'I S) where
 mapping = rewrap `identity` \from -> rewrap `identity` (from `ho` That `la` from `ho` This `ha__` unwrap @(AR))

instance
 ( Covariant Endo Semi Functor (AR) t
 , Covariant Endo Semi Functor (AR) tt
 , Mapping T'I'II T'I'II (AR) (AR) t (t `T'TT'I` t `L` t `T` Void)
 , Mapping T'I'II T'I'II (AR) (AR) tt (tt `T'TT'I` tt `L` tt `T` Void)
 ) => Mapping T'I'II T'I'II (AR) (AR) (t `S'T'I'TT'I` tt) ((t `S'T'I'TT'I` tt) `T'TT'I` (t `S'T'I'TT'I` tt) `L` (t `S'T'I'TT'I` tt) `T` Void) where
 mapping = rewrap `hv` \from -> T'TT'I'TTT'I `ho` T'TT'I
  `ha____` map @T'I'II @T'I'II @AR @AR @t @(t `T'TT'I` t `L` t `T` Void) from
    `ho__` unwrap @AR @(t `T'TT'I` t `L` t `T` Void `T'I_` _)
    `ho__'yo` rewrap @AR @(t `L` t `T` Void `T` _) @((t `S'T'I'TT'I` tt) `L` (t `S'T'I'TT'I` tt) `T` Void `T` _) `hv_` This `ho` T'TT'I'TTT'I
    `ho__` This
    `la__` map @T'I'II @T'I'II @AR @AR @tt @(tt `T'TT'I` tt `L` tt `T` Void) from
    `ho__` unwrap @AR @(tt `T'TT'I` tt `L` tt `T` Void `T'I_` _)
    `ho__'yo` rewrap @AR @(tt `L` tt `T` Void `T` _) @((t `S'T'I'TT'I` tt) `L` (t `S'T'I'TT'I` tt) `T` Void `T` _) `hv_` That `ho` T'TT'I'TTT'I
    `ho__` That

instance
 ( Covariant Endo Semi Functor (AR) t
 , Covariant Endo Semi Functor (AR) tt
 , Mapping T'I'II T'I'II (AR) (AR) t (t `T'TT'I` t `L` t `T` Void)
 , Mapping T'I'II T'I'II (AR) (AR) tt (tt `T'TT'I` tt `L` tt `T` Void)
 ) => Mapping T'I'II T'I'II (AR) (AR) (t `P'T'I'TT'I` tt) ((t `P'T'I'TT'I` tt) `T'TT'I` (t `P'T'I'TT'I` tt) `L` (t `P'T'I'TT'I` tt) `T` Void) where
 mapping = rewrap `hv` \from -> T'TT'I'TTT'I `ho` T'TT'I
  `ha____` (is `ho'he` this
    `ho` map @T'I'II @T'I'II @AR @AR @t @(t `T'TT'I` t `L` t `T` Void) from
    `ho` unwrap @AR @(t `T'TT'I` t `L` t `T` Void `T'I_` _)
    `lo` is `ho'he` that `ho'yo` from
   `ho__` (\(These x xx) -> x `yo` rewrap ((`lu_` xx) `ho` T'TT'I'TTT'I)))
   `lo__` (is `ho'he` that
    `ho` map @T'I'II @T'I'II @AR @AR @tt @(tt `T'TT'I` tt `L` tt `T` Void) from
    `ho` unwrap @AR @(tt `T'TT'I` tt `L` tt `T` Void `T'I_` _)
    `lo` is `ho'he` this `ho'yo` from
   `ho__` (\(These x xx) -> x `yo` rewrap ((xx `lu_`) `ho` T'TT'I'TTT'I)))
