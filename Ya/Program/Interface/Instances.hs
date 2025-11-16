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
 mapping = rewrap `identity` \source -> rewrap `li_` wrap `ho'yo` source `ho` Exist

pattern Stump :: forall i e .
 Component (AR) (S'I'II i `L` S'I'II i `T` Void) (S'I'II Unit) =>
 S'I'II i e `AR__` S'I'II i `L` S'I'II i `T` Void `T` e
pattern Stump x = Label x

instance Mapping T'I'II T'I'II (AR) (AR) (S'I'II e `L` S'I'II e `T` Void) (S'I'II Unit) where
 mapping = rewrap `identity` \source ->
  rewrap `identity` ((This `compose` constant Unit `la` That `compose` source) `compose` unwrap)

pattern Spare :: forall i ii .
 Component (AR) ((P'II'I i `T'TT'I` S'I'II Unit) `L` (P'II'I i `T'TT'I` S'I'II Unit) `T` Void) (S'I'II i) =>
 P'II'I i (S'I'II Unit ii) `AR___` (P'II'I i `T'TT'I` S'I'II Unit) `L` (P'II'I i `T'TT'I` S'I'II Unit) `T` Void `T` ii
pattern Spare x = Label (T'TT'I x)

instance Mapping T'I'II T'I'II (AR) (AR) ((P'II'I i `T'TT'I` S'I'II Unit) `L` (P'II'I i `T'TT'I` S'I'II Unit) `T` Void) (S'I'II i) where
 mapping = rewrap `identity` \source (Label (T'TT'I (T'II'I (These x i)))) -> Empty `hu` Error i `la` Valid `ha` source `li` x

pattern Aloft :: forall t e .
 Component (AR) ((Scrolling List `P'T'I'TT'I` Tree) `L` (Scrolling List `P'T'I'TT'I` Tree) `T` Void) Tree =>
 (t `P'T'I'TT'I` Tree) e `AR___` (t `P'T'I'TT'I` Tree) `L` (t `P'T'I'TT'I` Tree) `T` Void `T` e
pattern Aloft x = Label x

instance Mapping T'I'II T'I'II (AR) (AR) (((Alone `P'T'I'TT'I` Shafted List) `P'T'I'TT'I` Tree) `L` ((Alone `P'T'I'TT'I` Shafted List) `P'T'I'TT'I` Tree) `T` Void) Tree where
  mapping = rewrap `identity` \source (Label (T'TT'I'TTT'I (These scrolling_list tree))) ->
   rewrap (\x -> Alone tree `lu` that @(Shafted List _) `ho'yo` intro @Tree @(AR) `hv` x) scrolling_list
    `yi` is @(Scrolling List _) `ho` to @(Nonempty List) `ho` to @List `ho'yo` unwrap @(AR)
    `yi` this @(Alone _) `ho'he` Root `hv` unwrap scrolling_list
    `yo` source

pattern Focus :: forall i . i `AR__` I `L` Along (Unit `S` Unit) `T` Void `T` i
pattern Focus x = Label (Alone x)

-- This is a special instance to be able to distinguish a focused item source other ones
instance {-# OVERLAPS #-} Mapping T'I'II T'I'II (AR) (AR) (I `P'T'I'TT'I` Shafted List) ((I `P'T'I'TT'I` Shafted List) `T'TT'I` Along (Unit `S` Unit) `L` Along (Unit `S` Unit) `T` Void) where
 mapping = rewrap `identity` \source (T'TT'I'TTT'I (These x xs)) ->
  T'TT'I (T'TT'I'TTT'I (These (x `yo` Label `ha` Along `ha` (`lu` This Unit) `ha` source) (xs `yo` Label `ha` Along `ha` (`lu` That Unit) `ha` source)))

instance
 ( Covariant Endo Semi Functor (->) t
 ) => Mapping T'I'II T'I'II (AR) (AR) (Construction t) (Construction t `T'TT'I` Construction t `L` Construction t `T` Void) where
 mapping = rewrap `hv` \source -> rewrap `ha` rewrap `ha` rewrap `ha` rewrap `hv` \(These xx x) ->
  (xx `yo` unwrap @AR `ha` unwrap @AR `ha` (map @T'I'II @T'I'II @(AR) @(AR) @(Construction t) @(Construction t `T'TT'I` Construction t `L` Construction t `T` Void) source) `ha` F'T'I'TT'I)
  `lu` Label (xx `lu` x `yo` source)

pattern Final :: forall i . i `AR__` I `L` Along (Unit `S` Unit) `T` Void `T` i
pattern Final x = Label (Alone x)

instance
 ( Covariant Endo Transformation Functor (AR) (t `T'TT'I` Maybe `L` Maybe `T` Void `L` t `T` Void) (t `TT'T'I` Maybe)
 , Covariant Lax Monoidal Functor (AR) (AR) (P) S Void t
 , Covariant Lax Monoidal Functor (AR) (AR) (P) P Void t
 ) => Mapping T'I'II T'I'II (AR) (AR) (Construction t) (Construction t `T'TT'I` Along (Unit `S` Unit) `L` Along (Unit `S` Unit) `T` Void) where
 mapping = rewrap `hv` \source x -> T'TT'I `hv___` x
  `kyo` Level @(Construction t) `ha` (\xx -> Label `ha` Along
   `ha` (is `hu` (source `ha` this `ha` top `hv` xx `lu` This Unit) `la` is `hu` (source `ha` this `ha` top `hv` xx `lu` That Unit))
   `ha` (\xxx -> this `ha` sub `hv` xxx `lu'ys` Apply `hv` intro @t Unit `yokl` Apply `ha` Check `ha__` Error `hu` Error Unit `la` Valid)
   `hv` xx)

pattern Depth :: forall i . i `AR__` I `L` Along (List Unit) `T` Void `T` i
pattern Depth x = Label (Alone x)

instance
 ( Covariant Endo Transformation Functor (AR) (t `T'TT'I` Maybe `L` Maybe `T` Void `L` t `T` Void) (t `TT'T'I` Maybe)
 , Covariant Lax Monoidal Functor (AR) (AR) (P) S Void t
 , Covariant Lax Monoidal Functor (AR) (AR) (P) P Void t
 ) => Mapping T'I'II T'I'II (AR) (AR) (Construction t)
  (Construction t `T'TT'I` Along (List Unit) `L` Along (List Unit) `T` Void) where
 mapping = rewrap `hv` \source -> T'TT'I `compose` rewrap @AR (worker `hv` source `hv` empty @List) where

  worker source depth = (rewrap @AR `ha` rewrap @AR `ha` rewrap @AR) `hv`
   (\xx -> xx
    `yoi` fo @AR @AR (worker source (that (push @List `hv` Unit `hv` depth)))
    `yio` (\xxx -> source xxx `lu` depth)
   )

pattern Alter :: forall t i .
 Component (AR) (T'I'I t `L` T'I'I t `T` Void) (T'I'I t) =>
 T'I'I t i `AR__` T'I'I t `L` T'I'I t `T` Void `T` i
pattern Alter x = Label x

instance Mapping T'I'II T'I'II (AR) (AR) (T'I'I P `L` T'I'I P `T` Void) (T'I'I P) where
 mapping = rewrap `identity` \source -> rewrap `identity` (source `ha` that `lo` source `ha` this `ha__` unwrap @(AR))

instance Mapping T'I'II T'I'II (AR) (AR) (T'I'I S `L` T'I'I S `T` Void) (T'I'I S) where
 mapping = rewrap `identity` \source -> rewrap `identity` (source `ho` That `la` source `ho` This `ha__` unwrap @(AR))
