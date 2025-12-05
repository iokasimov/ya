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

instance Mapping T'I'II T'I'II (AR) (AR) (Twice `T'TT'I` List) List where
 mapping = rewrap `identity` \source (T'TT'I (T'I'I ((These bs fs)))) -> that
  (bs `yokl` Prior `ha` New `ha` State `ha` Event `ha` push @List `he'he'hv____` fs) `yo` source

instance Mapping T'I'II T'I'II (AR) (AR) (List `P'T'I'TT'I` Twice `T'TT'I` List) List where
 mapping = rewrap `identity` \source (T'TT'I'TTT'I (These x (T'TT'I (T'I'I (These sx xs))))) ->
  sx `yokl` Forth `ha` Apply `ha` State `ha` Event `ha` push `he'he'hv___` x `yi__` that `lu__` xs `yi__` Merge `ho` to @List `yo__` source

instance Mapping T'I'II T'I'II (AR) (AR) (Construction Maybe) (Alone `P'T'I'TT'I` Maybe `T'TT'I` Construction Maybe) where
 mapping = rewrap `identity` \source -> Alone `ha` this `ha` top `lo` wrap @(AR) `ha` this `ha` sub `ho_'yo` source

instance Mapping T'I'II T'I'II (AR) (AR) (Construction List) (Construction List `P'T'I'TT'I` List `T'TT'I` Unfolding Alone Tree) where
 mapping = rewrap `identity` \source x -> x `yo` source `lu` wrap `hv` empty @List

instance Mapping T'I'II T'I'II (AR) (AR) (Construction List `P'T'I'TT'I` List `T'TT'I` Unfolding Alone Tree) (Construction List) where
 mapping = rewrap `identity` \source (T'TT'I'TTT'I (These tree unfoldings)) ->
  unwrap unfoldings `yokl` Forth `ha` Apply `ha` State `ha` Event `ha` cover `he'he'hv___` tree `yi__` that `ho'yo` source where

   cover (T'TT'I'TTT'I (These parent siblings)) tree =
    Unit `lu__` that `ha` sub @Tree
     `hv__` intro @Tree `hv'he` parent
     `hv__` Alone `hv` tree `lu` unwrap siblings
       `yi` to @List `ha` to @(Nonempty List) @(Scrolling List)

pattern Fresh :: forall t i e .
 Component (AR) (List `L` t `T` (Void)) t =>
 List i `AR__` List `L` t `T` (Void) `T` i
pattern Fresh x = Label x

instance Mapping T'I'II T'I'II (AR) (AR) (List `L` (Twice `T'TT'I` List) `T` Void) (Twice `T'TT'I` List) where
 mapping = rewrap `identity` \source x -> empty @List `lu` unwrap x `yo` source

instance Mapping T'I'II T'I'II (AR) (AR) (List `L` (List `P'T'I'TT'I` Twice `T'TT'I` List) `T` (Void)) (List `P'T'I'TT'I` Twice `T'TT'I` List) where
 mapping = rewrap `identity` \source x -> empty @List `lu` (empty @List `lu` unwrap x) `yo` source

pattern Stock :: forall i e .
 Component (AR) (List `L` (List `P'T'I'TT'I` Twice `T'TT'I` List) `T` (Void `P` Void)) (List `P'T'I'TT'I` Twice `T'TT'I` List) =>
 List i `AR__` List `L` Scrolling List `T` (Void `P` Void) `T` i
pattern Stock x = Label x

instance Mapping T'I'II T'I'II (AR) (AR) (List `L` (List `P'T'I'TT'I` Twice `T'TT'I` List) `T` (Void `P` Void)) (List `P'T'I'TT'I` Twice `T'TT'I` List) where
 mapping = rewrap `identity` \source x -> unwrap x `lu` (empty @List `lu` empty @List) `yo` source

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

pattern Merge :: forall t tt i .
 ( Stackable tt
 , Covariant Endo Semi Functor (->) tt
 , Covariant Endo Yoneda Functor (->) t
 , forall e . Mapping T'I'II T'I'II (->) (->) (t `T'TT'I` State (tt e) `L` State (tt e) `T` Void `L` t `T` (Void `P` Void)) (t `TT'T'I` State (tt e))
 ) => t `P'T'I'TT'I` tt `T'I___` i `AR_______` (t `P'T'I'TT'I` tt) `L` tt `T` Void `T` i
pattern Merge x = Label x

instance
 ( Stackable tt
 , Covariant Endo Semi Functor (->) tt
 , Covariant Yoneda Functor (->) (->) t
 , forall e . Mapping T'I'II T'I'II (->) (->) (t `T'TT'I` State (tt e) `L` State (tt e) `T` Void `L` t `T` (Void `P` Void)) (t `TT'T'I` State (tt e))
 ) => Mapping T'I'II T'I'II (AR) (AR) ((t `P'T'I'TT'I` tt) `L` tt `T` Void) tt where
 mapping = rewrap `identity` \source (Label (T'TT'I'TTT'I (These x xx))) ->
  x `yokl` Prior `ha` Apply `ha` State `ha` Event `ha` push
    `he'he'hv___` xx `yi__` that `ho'yo` source

pattern Aloft :: forall t i .
 Component (AR) ((t `P'T'I'TT'I` Tree) `L` (t `P'T'I'TT'I` Tree) `T` Void) Tree =>
 t `P'T'I'TT'I` Tree `T'I___` i `AR_____` (t `P'T'I'TT'I` Tree) `L` (t `P'T'I'TT'I` Tree) `T` Void `T` i
pattern Aloft x = Label x

instance Mapping T'I'II T'I'II (AR) (AR)
 ((Alone `P'T'I'TT'I` Twice `T'TT'I` List `P'T'I'TT'I` Tree) `L` (Alone `P'T'I'TT'I` Twice `T'TT'I` List `P'T'I'TT'I` Tree) `T` Void) Tree where
  mapping = rewrap `identity` \source (Label (T'TT'I'TTT'I (These scrolling_list tree))) ->
   rewrap (\x -> Alone tree `lu` that @(Twice `T'TT'I` List `T'I_` _) `ho'yo` intro @Tree @(AR) `hv` x) scrolling_list
    `yi` is @(Scrolling List _) `ho` to @(Nonempty List) `ho` to @List `ho'yo` unwrap @(AR)
    `yi` this @(Alone _) `ho'he` Root `hv` unwrap scrolling_list
    `yo` source

instance Mapping T'I'II T'I'II (AR) (AR)
 ((Alone `P'T'I'TT'I` Twice `T'TT'I` List `T'TT'I` Tree `P'T'I'TT'I` Tree) `L` (Alone `P'T'I'TT'I` Twice `T'TT'I` List `T'TT'I` Tree `P'T'I'TT'I` Tree) `T` Void) Tree where
  mapping = rewrap `identity` \source (Label (T'TT'I'TTT'I (These (T'TT'I'TTT'I (These root siblings)) tree))) ->
   that `ha` sub @Tree
    `hv__` intro @Tree `hv'he` root
    `hv__` Alone tree `lu` unwrap siblings `yi` to @(Nonempty List) @(Scrolling List) `ho` to @List
    `yo__` source

-- TODO: We haven't finished yet!
-- TODO: I need to heavily test it...
-- instance Mapping T'I'II T'I'II (AR) (AR)
--  ((Alone `P'T'I'TT'I` Twice `T'TT'I` List) `T'TT'I` Tree `P'T'I'TT'I` Unfoldings Alone Tree) (List `T'TT'I` Tree) where
--  mapping = rewrap `identity` \source (T'TT'I'TTT'I (These basement unfoldings)) ->
--   let result = to @List `ha` to @(Nonempty List) `hv'he` basement in
--   Empty `hu` wrap result
--   -- `la______` (\x -> x `yokl` Forth `ha` Apply `ha` State `ha` Event `ha` worker `he'he'hv___` result `yi__` that `ho` wrap @(AR))
--   `la______` proceed result
--   `hv_______` unfoldings `yo_______` source where

--    topping unfolding forest = Unit `lu_____` forest
   
--    starting :: (Alone `P'T'I'TT'I` Twice `T'TT'I` List `T'TT'I` Tree) i `AR_______` List (Tree i) `AR_____` Tree i
--    starting (T'TT'I'TTT'I (These (Identity focused) (T'TT'I (T'TT'I (T'I'I (These sx xs)))))) forest = that `ha` sub @Tree
--     `hv__` intro @Tree `hv` focused `hv__` sx `lu` (forest `lu` xs `yi` Merge @List @List `ho` to @List) `yi` to @List @(Twice `T'TT'I` List) @(Tree _)

   -- proceed forest nonempty_list =
   --  let (These x xx) = this `ha` top @(Nonempty List) `lo` this `ha` sub @(Nonempty List) `hv_` nonempty_list in
   --  xx `yokl` Forth `ha` Apply `ha` State `ha` Event `ha` topping `he'he'hv___` starting x forest `yi__` that -- `ho` wrap @(
 
  -- unwrap (unwrap unfoldings)
  --  `yokl` Forth `ha` Apply `ha` State `ha` Event `ha` worker
  --  `he'he'hv___` wrap @(AR) @(List `T'TT'I` Tree `T'I_` _) `ha` to @List `ha` to @(Nonempty List) `hv'he` basement
  --  `yi__` that `ho'yo` source where

  --  -- TODO: we haven't finished yet...
  --  worker unfolding forest =
  --   Unit `lu` (forest)

--  ((Shifting Alone List `T'TT'I` Tree `P'T'I'TT'I` Unfoldings Alone Tree) `TT'T'I` t) where
--  mapping = rewrap `identity` \source -> rewrap `identity`
--   \(T'TT'I'TTT'I (These x (T'TT'I (T'I'I (These l r))))) ->

pattern Focus :: forall i . i `AR__` I `L` Along (Unit `S` Unit) `T` Void `T` i
pattern Focus x = Label (Alone x)

instance {-# OVERLAPS #-} Mapping T'I'II T'I'II (AR) (AR) (I `P'T'I'TT'I` Twice `T'TT'I` List) ((I `P'T'I'TT'I` Twice `T'TT'I` List) `T'TT'I` Along (Unit `S` Unit) `L` Along (Unit `S` Unit) `T` Void) where
 mapping = rewrap `identity` \source (T'TT'I'TTT'I (These x xs)) ->
  T'TT'I (T'TT'I'TTT'I (These (x `yo` (`lu` This Unit) `ha` source) (xs `yo` (`lu` That Unit) `ha` source)))

instance {-# OVERLAPS #-} Mapping T'I'II T'I'II (AR) (AR) (Construction List `P'T'I'TT'I` List `T'TT'I` Unfolding I `T'I` Construction List)
 ((Construction List `P'T'I'TT'I` List `T'TT'I` Unfolding I `T'I` Construction List) `T'TT'I` Along (Unit `S` Unit) `L` Along (Unit `S` Unit) `T` Void) where
 mapping = rewrap `identity` \source (T'TT'I'TTT'I (These (F'T'I'TT'I (Recursive (T'TT'I (T'II'I (These xx x))))) xxx)) ->
  xx `yo` wrapped @(AR) @(F'T'I'TT'I Along _ _) (`yo` source `ho` (`lu` That Unit)) `lu_` source x `lu` This Unit `lu_` xxx `yo` source `ho` (`lu` That Unit)

instance
 ( Covariant Endo Semi Functor (->) t
 ) => Mapping T'I'II T'I'II (AR) (AR) (Construction t) (Construction t `T'TT'I` Construction t `L` Construction t `T` Void) where
 mapping = rewrap `hv` \source -> rewrap `ha` rewrap `ha` rewrap `ha` rewrap `hv` \(These xx x) ->
  (xx `yo` unwrap @AR `ha` unwrap @AR `ha` (map @T'I'II @T'I'II @(AR) @(AR) @(Construction t) @(Construction t `T'TT'I` Construction t `L` Construction t `T` Void) source) `ha` F'T'I'TT'I)
  `lu` Label (xx `lu` x `yo` source)

-- instance Mapping T'I'II T'I'II (AR) (AR)
--  ((Alone `P'T'I'TT'I` Twice `T'TT'I` List) `T'TT'I` Tree `P'T'I'TT'I` Unfoldings Alone Tree)
--  (((Alone `P'T'I'TT'I` Twice `T'TT'I` List) `T'TT'I` Tree `P'T'I'TT'I` Unfoldings Alone Tree) `T'TT'I` Along (Unit `S` Unit) `L` Along (Unit `S` Unit) `T` Void) where
--  mapping = rewrap `identity` \source -> rewrap `identity`
--   \(These (T'TT'I (T'TT'I'TTT'I (These (Identity (F'T'I'TT'I (Recursive (T'TT'I (T'II'I (These xx x)))))) xxx))) xxxx) ->
--    xx `yo` wrapped @(AR) @(Tree _) (fo ((`lu` That Unit) `ha` source))
--     `lu_` x `yi` (`lu` This Unit) `ha` source
--     `lu_` xxx `yo'yo` (`lu` That Unit) `ha` source
--     `lu_` xxxx `yo` (`lu` That Unit) `ha` source

pattern Start :: forall i . i `AR__` I `L` Along (Unit `S` Unit) `T` Void `T` i
pattern Start x = Label (Alone x)

instance
 ( Covariant Endo Transformation Functor (AR) (t `T'TT'I` Maybe `L` Maybe `T` Void `L` t `T` Void) (t `TT'T'I` Maybe)
 , Covariant Lax Monoidal Functor (AR) (AR) (P) S Void t
 , Covariant Lax Monoidal Functor (AR) (AR) (P) P Void t
 ) => Mapping T'I'II T'I'II (AR) (AR) (Construction t) (Construction t `T'TT'I` Along (Unit `S` Unit) `L` Along (Unit `S` Unit) `T` (Void)) where
 mapping = rewrap `hv` \source (F'T'I'TT'I (Recursive (T'TT'I (T'II'I (These xs x))))) -> 
  xs `yo` wrapped @(AR) @(F'T'I'TT'I Along t _) (`yo` source `ho` (`lu` That Unit)) `lu_` source x `lu` This Unit

pattern Final :: forall i . i `AR__` I `L` Along (Unit `S` Unit) `T` (Void `P` Void) `T` i
pattern Final x = Label (Alone x)

instance
 ( Covariant Endo Transformation Functor (AR) (t `T'TT'I` Maybe `L` Maybe `T` Void `L` t `T` Void) (t `TT'T'I` Maybe)
 , Covariant Lax Monoidal Functor (AR) (AR) (P) S Void t
 , Covariant Lax Monoidal Functor (AR) (AR) (P) P Void t
 ) => Mapping T'I'II T'I'II (AR) (AR) (Construction t) (Construction t `T'TT'I` Along (Unit `S` Unit) `L` Along (Unit `S` Unit) `T` (Void `P` Void)) where
 mapping = rewrap `hv` \source x -> T'TT'I `hv___` x
  `kyo` Level @(Construction t) `ha` (\xx -> Label `ha` Along
   `ha` (is `hu` (source `ha` this `ha` top `hv` xx `lu` That Unit) `la` is `hu` (source `ha` this `ha` top `hv` xx `lu` This Unit))
   `ha` (\xxx -> this `ha` sub `hv` xxx `lu'ys` Apply `hv` intro @t Unit `yokl` Apply `ha` Check `ha__` Error `hu` Error Unit `la` Valid)
   `hv` xx)

pattern Depth :: forall i . i `AR__` I `L` Along (List Unit) `T` Void `T` i
pattern Depth x = Label (Alone x)

instance
 ( Covariant Endo Transformation Functor (AR) (t `T'TT'I` Maybe `L` Maybe `T` Void `L` t `T` Void) (t `TT'T'I` Maybe)
 , Covariant Lax Monoidal Functor (AR) (AR) (P) S Void t
 , Covariant Lax Monoidal Functor (AR) (AR) (P) P Void t
 ) => Mapping T'I'II T'I'II (AR) (AR) (Construction t) (Construction t `T'TT'I` Along (List Unit) `L` Along (List Unit) `T` Void) where
 mapping = rewrap `hv` \source -> T'TT'I `compose` rewrap @AR (worker `hv` source `hv` empty @List) where

  worker source depth = (rewrap @AR `ha` rewrap @AR `ha` rewrap @AR) `hv`
   (\xx -> xx
    `yoi` fo @AR @AR (worker source (that (push @List `hv` Unit `hv` depth)))
    `yio` (\xxx -> source xxx `lu` depth)
   )

-- instance Mapping T'I'II T'I'II (AR) (AR)
 -- (Shifting t List `T'TT'I` Tree `P'T'I'TT'I` Unfoldings t Tree)
 -- ((Shifting t List `T'TT'I` Tree `P'T'I'TT'I` Unfoldings t Tree) `T'TT'I` Along (List Unit) `L` Along (List Unit) `T` Void) where

--  mapping = rewrap `identity` \source -> rewrap `identity`
--   \(T'TT'I'TTT'I (These x (T'TT'I (T'I'I (These l r))))) ->

pattern Alter :: forall t i .
 Component (AR) (T'I'I t `L` T'I'I t `T` Void) (T'I'I t) =>
 T'I'I t i `AR__` T'I'I t `L` T'I'I t `T` Void `T` i
pattern Alter x = Label x

instance Mapping T'I'II T'I'II (AR) (AR) (T'I'I (P) `L` T'I'I (P) `T` Void) (T'I'I (P)) where
 mapping = rewrap `identity` \source -> rewrap `identity` (source `ha` that `lo` source `ha` this `ha__` unwrap @(AR))

instance Mapping T'I'II T'I'II (AR) (AR) (T'I'I (S) `L` T'I'I (S) `T` Void) (T'I'I (S)) where
 mapping = rewrap `identity` \source -> rewrap `identity` (source `ho` That `la` source `ho` This `ha__` unwrap @(AR))

pattern Aside e = This e :: Shifter Tree
pattern Pitch e = That e :: Shifter Tree

instance Shiftable Alone (Construction List) where
 shift way x = is
  `li` is `hu` (Empty Unit `lu` x)
  `la` is `ho'he` foi @_ @(AR) Exist
  `li` (horizontally `la_` vertical_deep `la` vertical_up `hv___` way) `he'he'hv` x where

  vertical_up :: forall i . Unit `AR___` (Halts `JNT` State `T` Scrolling Tree i) `T'I_` Alone i
  vertical_up _ = intro @(Halts `JNT` State `T` Scrolling Tree i) Unit
   `yuk___` Apply `ha` State
   `hv____` Event `hv` pop
    `ha___` Scope `hv` at @(List `T'TT'I` (Alone `P'T'I'TT'I` Twice `T'TT'I` List `T'TT'I` Tree) `T'I_` i) `ho_'he` Scope `hv` it
   `yok___` Check `ha` is @(Maybe `T'I_` (Alone `P'T'I'TT'I` Twice `T'TT'I` List `T'TT'I` Tree) i)
   `yok___` Apply `ha` State
   `ha____` Event `ha` aloft
   `ho__'ha` Scope `hv` at @(Tree `T'I` i)

  aloft :: forall i . (Alone `P'T'I'TT'I` Twice `T'TT'I` List `T'TT'I` Tree) `T'I` i `AR____` Tree i `AR__` Alone i `P` Tree i
  aloft unfolding tree = Alone `ha` this `ha` top `hv` tree `lu_` unfolding `lu` tree `yi` to @Tree `ha` Aloft

  vertical_deep :: forall i . Unit `AR___` (Halts `JNT` State `T` Scrolling Tree i) `T'I_` Alone i
  vertical_deep _ = intro @(Halts `JNT` State `T` Scrolling Tree i) Unit
   `yuk____` Apply `ha` State
    `hv____` Event `hv` fetch
     `ha___` Scope `hv` at @(Tree `T'I` i)
      `ho__` Scope `hv` top @Tree
        `lo` Scope `hv` sub @Tree
   `yok____` Check `ha'yo` splash `ha` moves
   `yok____` Apply `ha` State `ha___` Event `ha` relay `ha` this
    `ho__'ha` Scope `hv` at @(Tree i)
   `lo___'yp` Apply `ha` State `ha___` Event `ha` push `ha` that
    `ho__'ha` Scope `hv` at @(List `T'TT'I` (Alone `P'T'I'TT'I` Twice `T'TT'I` List `T'TT'I` Tree) `T'I_` i)
     `ho_'he` Scope `hv` it @(List `T'I_` (Alone `P'T'I'TT'I` Twice `T'TT'I` List `T'TT'I` Tree) i)
   `ho_____'yo` Alone `ha` this `ha` top @Tree `ha` this

  moves :: forall i . i `P` List (Tree i) `AR___` Maybe (i `P` Nonempty List (Tree i))
  moves x = x `yiokl` Apply `ha` Check `ha` unwrap @(AR)

  splash :: forall i . i `P` (Nonempty List (Tree i)) `AR____` Tree i `P` (Alone `P'T'I'TT'I` Twice `T'TT'I` List `T'TT'I` Tree) i
  splash (These root descendants) = this `ha` top `hv` descendants
   `lu_` Alone `hv` root `lu` wrap @(AR) `ha` to `ha` Fresh @(Shafted List) `ha` wrap @(AR) @(List _) `ha` this `ha` sub `hv` descendants

  horizontally :: forall i . Shifter List `AR___` (Halts `JNT` State `T` Scrolling Tree i) `T'I_` Alone i
  horizontally way = intro @(Halts `JNT` State `T` Scrolling Tree i) Unit
   `yuk____` Apply `ha` State
   `hv_____` Event `hv` pop
    `ha____` Scope `hv` at @(List `T'TT'I` (Alone `P'T'I'TT'I` Twice `T'TT'I` List `T'TT'I` Tree) `T'I_` i)
    `ho__'he` Scope `hv` it @(List `T'I_` (Alone `P'T'I'TT'I` Twice `T'TT'I` List `T'TT'I` Tree) i)
   `yok____` Check
   `yok____` Apply `ha` State
     `ha___` Event `ha` (\unfolding tree -> scroll `hv` way `hv` unfolding `hv` tree `lu` tree)
    `ho__'ha` Scope `hv` at @(Tree i)
   `yok____` Apply `ha` State `ha___` Event `ha` relay `ha` this
    `ho__'ha` Scope `hv` at @(Tree i)
   `lo___'yp` Apply `ha` State `ha___` Event `ha` push `ha` that
    `ho__'ha` Scope `hv` at @(List `T'TT'I` (Alone `P'T'I'TT'I` Twice `T'TT'I` List `T'TT'I` Tree) `T'I_` i)
     `ho_'he` Scope `hv` it @(List `T'I_` (Alone `P'T'I'TT'I` Twice `T'TT'I` List `T'TT'I` Tree) i)
   `ho_____'yo` Alone `ha` this `ha` top @Tree `ha` this

  -- TODO: the problem here is that we ignore information about successfulness of horizontal shifting!
  scroll :: forall i . Shifter List
   `AR_____` (Alone `P'T'I'TT'I` Twice `T'TT'I` List `T'TT'I` Tree) `T'I` i
   `AR____` Tree i
   `AR___` (Tree i) `P` (Alone `P'T'I'TT'I` Twice `T'TT'I` List `T'TT'I` Tree `T'I___` i)
  scroll way unfolding tree = 
   let siblings = this `ha` at @(Twice `T'TT'I` List `T'TT'I` Tree `T'I_` i) `ho'he` is `hv` unfolding in
   Alone `hv` tree `lu` siblings
   `yi` shift `hv` way `ha` is @(Scrolling List `T'I` Tree i)
   `yi` (\x -> unwrap @(AR) `ha` this `ha` at @(Alone `T'I` Tree i) `hv` x `lu_` this `ha` at @(Alone i) `hv` unfolding `lu` wrap @(AR) `ha` this `ha` at @(Twice `T'TT'I` List `T'I_` Tree i) `hv` x) `ha` that