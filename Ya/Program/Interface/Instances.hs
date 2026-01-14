{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE AllowAmbiguousTypes #-}
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

-- TODO: think about labels for these two instances below!

instance Mapping T'I'II T'I'II (AT) (AT) ((Construction Maybe) `L` Alone `T` Void) Alone where
 mapping = rewrap `identity` \(T'I'TT'II'T'II'I source) ->
  T'I'TT'II'T'II'I `identity` \(Label (F'T'I'TT'I (Recursive (T'TT'I (T'II'I (These xxx x)))))) ->
   Alone `ha` this `ha` source `hc` x `hjd` (\xx -> xxx `hjd` that `ha` source `hc` x `hc` super xx)

-- TODO: refactor, pattern matching is redundant here
instance {-# OVERLAPS #-} Component (AT) ((Maybe `T'TT'I` Construction Maybe) `L` Alone `T` (Void) `L` Alone `T` (Void)) Maybe where
 component = T'I'TT'II'T'II'I `identity` \case
  Label (Label (T'TT'I (T'I'II (This _)))) -> unwrap Empty `hjd` Label `ha` Label `ha` (Empty `hu` empty `la` intro)
  Label (Label (T'TT'I (T'I'II (That (F'T'I'TT'I (Recursive (T'TT'I (T'II'I (These xxx x))))))))) ->
   Exist `hc` x `hjd` Label `ha` Label `ha` (Empty `hu_` T'TT'I `hc` (xxx `yo` F'T'I'TT'I) `la` intro @List)

instance {-# OVERLAPS #-} Component (AT) ((Maybe `T'TT'I` Construction Maybe) `L` Alone `T` (Void `P` Void) `L` Alone `T` (Void)) Maybe where
 component = T'I'TT'II'T'II'I `identity` \(Label (Label x)) ->
  unwrap Empty `hjd` Label `ha` Label `ha` (Empty `hu` x `la` (\xx -> that (push xx x)))

pattern Adapt :: forall t tt i . t `T` i `AR__` t `L` tt `T` Void `T` i
pattern Adapt x = Label @t @tt @Void x

instance Mapping T'I'II T'I'II (AR) (AR) (Construction Optional `L` List `T` (Void)) List where
 mapping = rewrap `identity` \source -> rewrap `li_` unwrap `ho` wrap @AR `ho'yo` source `ho` Exist

instance Mapping T'I'II T'I'II (AR) (AR) ((Twice `T'TT'I` List) `L` List `T` (Void)) List where
 mapping = rewrap `identity` \source (Label (T'TT'I (T'I'I ((These bs fs))))) -> that
  (bs `yokl` Prior `ha` New `ha` State `ha` Event `ha` push @List `he'he'hv____` fs) `yo` source

instance Mapping T'I'II T'I'II (AR) (AR) ((List `P'T'I'TT'I` Twice `T'TT'I` List) `L` List `T` (Void)) List where
 mapping = rewrap `identity` \source (Label (T'TT'I'TTT'I (These x (T'TT'I (T'I'I (These sx xs)))))) ->
  sx `yokl` Forth `ha` Apply `ha` State `ha` Event `ha` push `hc___` x `yi__` that `lu__` xs `yi__` Merge `ho` to @List `yo__` source

-- instance Mapping T'I'II T'I'II (AR) (AR) (Construction Maybe) (Alone `P'T'I'TT'I` Maybe `T'TT'I` Construction Maybe) where
 -- mapping = rewrap `identity` \source -> Alone `ha` this `ha` top `lo` wrap @(AR) `ha` this `ha` sub `ho_'yo` source

instance Mapping T'I'II T'I'II (AR) (AR) (Construction List `L` (Construction List `P'T'I'TT'I` List `T'TT'I` Unfolding Alone Tree) `T` Void) (Construction List `P'T'I'TT'I` List `T'TT'I` Unfolding Alone Tree) where
 mapping = rewrap `identity` \source x -> unwrap x `yo` source `hjd` wrap `hv` empty @List

instance Mapping T'I'II T'I'II (AR) (AR) ((Construction List `P'T'I'TT'I` List `T'TT'I` Unfolding Alone Tree) `L` Construction List `T` Void) (Construction List) where
 mapping = rewrap `identity` \source (Label (T'TT'I'TTT'I (These tree unfoldings))) ->
  unwrap unfoldings `yokl` Forth `ha` Apply `ha` State `ha` Event `ha` cover `hc___` tree `yi__` that `ho'yo` source where

   cover (T'TT'I'TTT'I (These parent siblings)) tree =
    Unit `hjd__` that `ha` sub @Tree
     `hc__` intro @Tree `hv'he` parent
     `hc__` Alone `hc` tree `hjd` unwrap siblings
       `yi` to @List `ha` Adapt @(Nonempty List)
       `ha` to @(Nonempty List) `ha` Adapt @(Scrolling List)

instance Mapping T'I'II T'I'II (AR) (AR) (Both (P) `L` Construction Optional `T` Void) (Construction Optional) where
 mapping = rewrap `identity` \source -> rewrap `identity` \(T'I'I (These x xx)) -> Item (source x) `ha` Next `ha` Item (source xx) `ha` Last `hc` Unit

instance Mapping T'I'II T'I'II (AR) (AR) (Both (P) `L` List `T` Void) List where
 mapping = rewrap `identity` \source -> rewrap `identity` \(T'I'I (These x xx)) -> Exist `ha` Nonempty @List `ha` Item (source x) `ha` Next `ha` Item (source xx) `ha` Last `hc` Unit

pattern Stock :: forall t i .
 List i `AR__` List `L` t `T` (Void) `T` i
pattern Stock x = Label x

instance Mapping T'I'II T'I'II (AR) (AR) (List `L` (List `P'T'I'TT'I` Twice `T'TT'I` List) `T` (Void)) (List `P'T'I'TT'I` Twice `T'TT'I` List) where
 mapping = rewrap `identity` \source x -> unwrap x `hjd` (empty @List `hjd` empty @List) `yo` source

-- TODO: generalise
pattern Fresh :: forall t i .
 List i `AR__` List `L` t `T` (Void `P` Void) `T` i
pattern Fresh x = Label x

instance Mapping T'I'II T'I'II (AR) (AR) (List `L` (Twice `T'TT'I` List) `T` (Void `P` Void)) (Twice `T'TT'I` List) where
 mapping = rewrap `identity` \source x -> empty @List `hjd` unwrap x `yo` source

instance Mapping T'I'II T'I'II (AR) (AR) (List `L` (List `P'T'I'TT'I` Twice `T'TT'I` List) `T` (Void `P` Void)) (List `P'T'I'TT'I` Twice `T'TT'I` List) where
 mapping = rewrap `identity` \source x -> empty @List `hjd` (empty @List `hjd` unwrap x) `yo` source

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
    `hc___` xx `yi__` that `ho'yo` source

pattern Aloft :: forall t i .
 Component (AR) ((t `P'T'I'TT'I` Tree) `L` Tree `T` (Void `P` Void)) Tree =>
 t `P'T'I'TT'I` Tree `T'I___` i `AR_____` (t `P'T'I'TT'I` Tree) `L` Tree `T` (Void `P` Void) `T` i
pattern Aloft x = Label x

instance Mapping T'I'II T'I'II (AR) (AR)
 ((Alone `P'T'I'TT'I` Twice `T'TT'I` List `P'T'I'TT'I` Tree) `L` Tree `T` (Void `P` Void)) Tree where
  mapping = rewrap `identity` \source (Label (T'TT'I'TTT'I (These scrolling_list tree))) ->
   rewrap (\x -> Alone tree `hjd` that @(Twice `T'TT'I` List `T'I_` _) `ho'yo` intro @Tree @(AR) `hc` x) scrolling_list
    `yi` Adapt @(Scrolling List) `ho` to @(Nonempty List) `ho` Adapt @(Nonempty List) `ho` to @List `ho'yo` unwrap @(AR)
    `yi` this @(Alone _) `ho'he` Root `hc` unwrap scrolling_list
    `yo` source

instance Mapping T'I'II T'I'II (AR) (AR)
 ((Alone `P'T'I'TT'I` Twice `T'TT'I` List `T'TT'I` Tree `P'T'I'TT'I` Tree) `L` Tree `T` (Void `P` Void)) Tree where
  mapping = rewrap `identity` \source (Label (T'TT'I'TTT'I (These (T'TT'I'TTT'I (These root siblings)) tree))) ->
   that `ha` sub @Tree
    `hv__` intro @Tree `hv'he` root
    `hv__` Alone tree `hjd` unwrap siblings `yi` Adapt @(Scrolling List) `ho` to @(Nonempty List) `ho` Adapt @(Nonempty List) `ho` to @List
    `yo__` source

-- TODO: We haven't finished yet!
-- TODO: I need to heavily test it...
-- instance Mapping T'I'II T'I'II (AR) (AR)
--  ((Alone `P'T'I'TT'I` Twice `T'TT'I` List) `T'TT'I` Tree `P'T'I'TT'I` Unfoldings Alone Tree) (List `T'TT'I` Tree) where
--  mapping = rewrap `identity` \source (T'TT'I'TTT'I (These basement unfoldings)) ->
--   let result = to @List `ha` to @(Nonempty List) `hv'he` basement in
--   Empty `hu` wrap result
--   -- `la______` (\x -> x `yokl` Forth `ha` Apply `ha` State `ha` Event `ha` worker `hc___` result `yi__` that `ho` wrap @(AR))
--   `la______` proceed result
--   `hv_______` unfoldings `yo_______` source where

--    topping unfolding forest = Unit `lu_____` forest
   
--    starting :: (Alone `P'T'I'TT'I` Twice `T'TT'I` List `T'TT'I` Tree) i `AR_______` List (Tree i) `AR_____` Tree i
--    starting (T'TT'I'TTT'I (These (Identity focused) (T'TT'I (T'TT'I (T'I'I (These sx xs)))))) forest = that `ha` sub @Tree
--     `hv__` intro @Tree `hc` focused `hv__` sx `hjd` (forest `hjd` xs `yi` Merge @List @List `ho` to @List) `yi` to @List @(Twice `T'TT'I` List) @(Tree _)

   -- proceed forest nonempty_list =
   --  let (These x xx) = this `ha` top @(Nonempty List) `lo` this `ha` sub @(Nonempty List) `hv_` nonempty_list in
   --  xx `yokl` Forth `ha` Apply `ha` State `ha` Event `ha` topping `hc___` starting x forest `yi__` that -- `ho` wrap @(
 
  -- unwrap (unwrap unfoldings)
  --  `yokl` Forth `ha` Apply `ha` State `ha` Event `ha` worker
  --  `hc___` wrap @(AR) @(List `T'TT'I` Tree `T'I_` _) `ha` to @List `ha` to @(Nonempty List) `hv'he` basement
  --  `yi__` that `ho'yo` source where

  --  -- TODO: we haven't finished yet...
  --  worker unfolding forest =
  --   Unit `hjd` (forest)

--  ((Shifting Alone List `T'TT'I` Tree `P'T'I'TT'I` Unfoldings Alone Tree) `TT'T'I` t) where
--  mapping = rewrap `identity` \source -> rewrap `identity`
--   \(T'TT'I'TTT'I (These x (T'TT'I (T'I'I (These l r))))) ->

pattern Focus :: forall i . i `AR__` I `L` Along (Unit `S` Unit) `T` Void `T` i
pattern Focus x = Label (Alone x)

instance {-# OVERLAPS #-} Mapping T'I'II T'I'II (AR) (AR)
 (I `P'T'I'TT'I` Twice `T'TT'I` List)
 ((I `P'T'I'TT'I` Twice `T'TT'I` List) `T'TT'I` Along (Unit `S` Unit) `L` Along (Unit `S` Unit) `T` Void) where
 mapping = rewrap `identity` \source (T'TT'I'TTT'I (These x xs)) ->
  T'TT'I (T'TT'I'TTT'I (These (x `yo` (`hjd` This Unit) `ha` source) (xs `yo` (`hjd` That Unit) `ha` source)))

-- instance {-# OVERLAPS #-} Mapping T'I'II T'I'II (AT) (AT) (I `P'T'I'TT'I` Twice `T'TT'I` List)
--  ((I `P'T'I'TT'I` Twice `T'TT'I` List) `T'TT'I` Along (Unit `S` Unit) `L` Along (Unit `S` Unit) `T` Void) where
  
 -- component = T'I'TT'II'T'II'I `identity` \(Label (Label x)) ->
  -- unwrap Empty `hjd` Label `ha` Label `ha` (Empty `hu` x `la` (\xx -> that (push xx x)))

instance {-# OVERLAPS #-} Mapping T'I'II T'I'II (AR) (AR) (Construction List `P'T'I'TT'I` List `T'TT'I` Unfolding I `T'I` Construction List)
 ((Construction List `P'T'I'TT'I` List `T'TT'I` Unfolding I `T'I` Construction List) `T'TT'I` Along (Unit `S` Unit) `L` Along (Unit `S` Unit) `T` Void) where
 mapping = rewrap `identity` \source (T'TT'I'TTT'I (These (F'T'I'TT'I (Recursive (T'TT'I (T'II'I (These xx x))))) xxx)) ->
  xx `yo` wrapped @(AR) @(F'T'I'TT'I Along _ _) (`yo` source `ho` (`hjd` That Unit)) `lu_` source x `hjd` This Unit `lu_` xxx `yo` source `ho` (`hjd` That Unit)

pattern Frame :: forall i . i `AR__` I `L` Along (Unit `S` Unit) `T` (Void `P` Void) `T` i
pattern Frame x = Label (Alone x)

instance {-# OVERLAPS #-} Mapping T'I'II T'I'II (AR) (AR)
 (I `P'T'I'TT'I` Twice `T'TT'I` List)
 ((I `P'T'I'TT'I` Twice `T'TT'I` List) `T'TT'I` Along (Unit `S` Unit) `L` Along (Unit `S` Unit) `T` (Void `P` Void)) where
 mapping = rewrap `identity` \source (T'TT'I'TTT'I (These x xs)) ->
  T'TT'I (T'TT'I'TTT'I (These (x `yo` (`hjd` That Unit) `ha` source) (xs `yo` (`hjd` This Unit) `ha` source)))

instance {-# OVERLAPS #-} Mapping T'I'II T'I'II (AR) (AR) (Construction List `P'T'I'TT'I` List `T'TT'I` Unfolding I `T'I` Construction List)
 ((Construction List `P'T'I'TT'I` List `T'TT'I` Unfolding I `T'I` Construction List) `T'TT'I` Along (Unit `S` Unit) `L` Along (Unit `S` Unit) `T` (Void `P` Void)) where
 mapping = rewrap `identity` \source (T'TT'I'TTT'I (These (F'T'I'TT'I (Recursive (T'TT'I (T'II'I (These xx x))))) xxx)) ->
  xx `yo` wrapped @(AR) @(F'T'I'TT'I Along _ _) (`yo` source `ho` (`hjd` This Unit)) `lu_` source x `hjd` That Unit `lu_` xxx `yo` source `ho` (`hjd` This Unit)

instance
 ( Covariant Endo Semi Functor (->) t
 ) => Mapping T'I'II T'I'II (AR) (AR) (Construction t) (Construction t `T'TT'I` Construction t `L` Construction t `T` Void) where
 mapping = rewrap `hc` \source -> rewrap `ha` rewrap `ha` rewrap `ha` rewrap `hc` \(These xx x) ->
  (xx `yo` unwrap @AR `ha` unwrap @AR `ha` (map @T'I'II @T'I'II @(AR) @(AR) @(Construction t) @(Construction t `T'TT'I` Construction t `L` Construction t `T` Void) source) `ha` F'T'I'TT'I)
  `hjd` Label (xx `hjd` x `yo` source)

-- instance Mapping T'I'II T'I'II (AR) (AR)
--  ((Alone `P'T'I'TT'I` Twice `T'TT'I` List) `T'TT'I` Tree `P'T'I'TT'I` Unfoldings Alone Tree)
--  (((Alone `P'T'I'TT'I` Twice `T'TT'I` List) `T'TT'I` Tree `P'T'I'TT'I` Unfoldings Alone Tree) `T'TT'I` Along (Unit `S` Unit) `L` Along (Unit `S` Unit) `T` Void) where
--  mapping = rewrap `identity` \source -> rewrap `identity`
--   \(These (T'TT'I (T'TT'I'TTT'I (These (Identity (F'T'I'TT'I (Recursive (T'TT'I (T'II'I (These xx x)))))) xxx))) xxxx) ->
--    xx `yo` wrapped @(AR) @(Tree _) (fo ((`hjd` That Unit) `ha` source))
--     `lu_` x `yi` (`hjd` This Unit) `ha` source
--     `lu_` xxx `yo'yo` (`hjd` That Unit) `ha` source
--     `lu_` xxxx `yo` (`hjd` That Unit) `ha` source

pattern Start :: forall i . i `AR__` I `L` Along (Unit `S` Unit) `T` Void `T` i
pattern Start x = Label (Alone x)

instance
 ( Covariant Endo Transformation Functor (AR) (t `T'TT'I` Maybe `L` Maybe `T` Void `L` t `T` Void) (t `TT'T'I` Maybe)
 , Covariant Lax Monoidal Functor (AR) (AR) (P) S Void t
 , Covariant Lax Monoidal Functor (AR) (AR) (P) P Void t
 ) => Mapping T'I'II T'I'II (AR) (AR) (Construction t) (Construction t `T'TT'I` Along (Unit `S` Unit) `L` Along (Unit `S` Unit) `T` (Void)) where
 mapping = rewrap `hc` \source (F'T'I'TT'I (Recursive (T'TT'I (T'II'I (These xs x))))) -> 
  xs `yo` wrapped @(AR) @(F'T'I'TT'I Along t _) (`yo` source `ho` (`hjd` That Unit)) `hjd_` source x `hjd` This Unit

pattern Final :: forall i . i `AR__` I `L` Along (Unit `S` Unit) `T` (Void `P` Void) `T` i
pattern Final x = Label (Alone x)

instance
 ( Covariant Endo Transformation Functor (AR) (t `T'TT'I` Maybe `L` Maybe `T` Void `L` t `T` Void) (t `TT'T'I` Maybe)
 , Covariant Lax Monoidal Functor (AR) (AR) (P) S Void t
 , Covariant Lax Monoidal Functor (AR) (AR) (P) P Void t
 ) => Mapping T'I'II T'I'II (AR) (AR) (Construction t) (Construction t `T'TT'I` Along (Unit `S` Unit) `L` Along (Unit `S` Unit) `T` (Void `P` Void)) where
 mapping = rewrap `hc` \source x -> T'TT'I `hc___` x
  `kyo` Level @(Construction t) `ha` (\xx -> Label `ha` Along
   `ha` (is `hu` (source `ha` this `ha` top `hc` xx `hjd` That Unit) `la` is `hu` (source `ha` this `ha` top `hc` xx `hjd` This Unit))
   `ha` (\xxx -> this `ha` sub `hc` xxx `lu'ys` Apply `hc` intro @t Unit `yokl` Apply `ha` Check `ha__` Error `hu` Error Unit `la` Valid)
   `hc` xx)

pattern Depth :: forall i . i `AR__` I `L` Along (List Unit) `T` Void `T` i
pattern Depth x = Label (Alone x)

instance
 ( Covariant Endo Transformation Functor (AR) (t `T'TT'I` Maybe `L` Maybe `T` Void `L` t `T` Void) (t `TT'T'I` Maybe)
 , Covariant Lax Monoidal Functor (AR) (AR) (P) S Void t
 , Covariant Lax Monoidal Functor (AR) (AR) (P) P Void t
 ) => Mapping T'I'II T'I'II (AR) (AR) (Construction t) (Construction t `T'TT'I` Along (List Unit) `L` Along (List Unit) `T` Void) where
 mapping = rewrap `hc` \source -> T'TT'I `compose` rewrap @AR (worker `hc` source `hc` empty @List) where

  worker source depth = (rewrap @AR `ha` rewrap @AR `ha` rewrap @AR) `hc`
   (\xx -> xx
    `yoi` fo @AR @AR (worker source (that (push @List `hc` Unit `hc` depth)))
    `yio` (\xxx -> source xxx `hjd` depth)
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

pattern Aback x = This x :: Shifter List
pattern Ahead x = That x :: Shifter List

pattern Above x = This x :: Shifter List
pattern Below x = That x :: Shifter List

pattern Front :: forall i tt target .
 tt i `AR__` tt `L` Alone `T` (Void) `T` i
pattern Front x = Label x

instance Shiftable Alone (Maybe `T'TT'I` Construction Maybe) where
 shift :: forall i . Shifter List `AR___` Supertype (Event `T'I` Shifting Alone List i `T'I` Maybe (Alone i))
 shift way x = is `li` Empty `hu` (Empty Unit `hjd` x) `la` is `ho'he` foi @_ @(AR) Exist `li` _shift_ `hc` x where

  _shift_ = intro @(Halts `JNT` State `T` Scrolling List i) Unit
   `yuk___` Apply `ha` State
   `hv____` Event `ha` relay `hv'he` Empty
    `ha___` Scope `hc` at @(Shafted List i)
   `ho__'he` Scope `ha` by @Twice `ha` (Back `la` Fore) `hc` way
     `ho__` Scope `hc` (as `ha` Front `ha` Stock @Alone)
   `yok___` Check
   `yok___` Apply `ha` State
   `ha____` Event `ha` relay `ha` Alone
   `ho__'ha` Scope `hc` at @(Alone i)
   `yok___` Apply `ha` State
   `ha____` Event `ha` relay `ha'he` Exist
   `ho__'ha` Scope `hc` at @(Shafted List i)
    `ho_'he` Scope `ha` by `ha` (Fore `la` Back) `hc` way
      `ho_` Scope `hc` (as `ha` Front `ha` Fresh @Alone)
   -- TODO: there it is - if I use `Lease` label instead of `Apply` state doesn't change
   `yuk___` Apply `ha` State
   `hv____` Event `hc` fetch
    `ha___` Scope `hc` at @(Alone i)

 spot :: forall i . Shifter List `P` Match (Alone i) `AR_` Supertype (Event `T'I` Shifting Alone List i `T'I` Maybe `T` Shifting Alone List i)
 spot (These way predicate) x = foi Exist `ha` fetch `la` is `ho'he` foi @_ @(AR) (Empty `hu` Empty Unit) `li` _spot_ `hc` x where

  found (These w sl) = unwrap (predicate `hc` w) `yui` sl `yiu` sl

  _spot_ = intro @(Stops `T` Scrolling List i `JNT` State `T` Scrolling List i) Unit
   `yuk____` Lease `ha` State `hv___` Event `hv__` fetch `ha__` Scope `hc` at @(Alone i) `lo` Scope `hc` it
   `yok____` Check `ha` Stops `ha___` not `ha` found
   `yuk____` Apply `ha` State `hv___` Event `hv__` shift `hc` way
   `yok____` Retry `ha` is `ha__` Break `hu` Ok Unit `la` Again `hu` Reach Unit

instance Shiftable List (Maybe `T'TT'I` Construction Maybe) where
 shift :: forall i . Shifter List `AR___` Supertype (Event `T'I` Shifting List List i `T'I` Maybe (List i))
 shift way x = is
  `li` is `hu` (Empty Unit `hjd` x)
  `la` is `ho'he` foi @_ @(AR) Exist
  `li` (slide_passed `lv` slide_future `li` way) `hc` x where

  slide_future = intro @(Halts `JNT` State `T` Sliding List i) Unit
   `yuk____` Apply `ha` State `hv___` Event `hc` pop `ha_` Scope `hc` at @(List _)
   `yok____` Check
   `yok____` Apply `ha` State `ha___` Event `ha` push `ho__'ha` Scope `hc` at @(Shafted List i) `ho_'he` Scope `ha` by `hv'he` Aback
   `yuk____` Apply `ha` State `hv___` Event `hc` pop `ha__` Scope `hc` at @(Shafted List i) `ho_'he` Scope `ha` by `hv'he` Ahead
   `yok____` Check
   `yok____` Apply `ha` State `ha____` Event `ha` window_future `ho_'ha` Scope `hc` at @(List _)

  slide_passed = intro @(Halts `JNT` State `T` Sliding List _) `hv` Unit
   `yuk____` Apply `ha` State `hv___` Event `hc` pop `ha__` Scope `hc` at @(Shafted List i) `ho_'he` Scope `ha` by `hv'he` Aback
   `yok____` Check
   `yok____` Apply `ha` State `ha___` Event `ha` window_extract_last `ho_'ha` Scope `hc` at @(List _)
   `yok____` Check
   `yok____` Apply `ha` State `ha___` Event `ha` push `ho__'ha` Scope `hc` at @(Shafted List i) `ho_'he` Scope `ha` by `hv'he` Ahead
   `yuk____` Apply `ha` State `hv___` Event `hc` fetch `ha__` Scope `hc` at @(List _)

  window_future :: i `AR_____` List i `AR___` List i `P` List i
  window_future r w = is @(List _) w `yokl` Prior `ha` Apply `ha` State `ha` Event `ha` push `hc___` List `ha` Exist `ha` Build `ha` Item r `ha` T'I'II `ha` This `hc` Unit -- `yui` r

  window_extract_last passed w =
   push @List passed w `yi` that
    `yokl` Forth `ha` Apply `ha` State `ha` Event `ha` push
    `hc___` empty @List
    `yi__` that `ho` pop @List

pattern Aside e = This e :: Shifter Tree
pattern Pitch e = That e :: Shifter Tree

instance Shiftable Alone (Construction List) where
 shift way x = is
  `li` is `hu` (Empty Unit `hjd` x)
  `la` is `ho'he` foi @_ @(AR) Exist
  `li` (horizontally `la_` vertical_deep `la` vertical_up `hv___` way) `hc` x where

  vertical_up :: forall i . Unit `AR___` (Halts `JNT` State `T` Scrolling Tree i) `T'I_` Alone i
  vertical_up _ = intro @(Halts `JNT` State `T` Scrolling Tree i) Unit
   `yuk___` Apply `ha` State
   `hv____` Event `hc` pop
    `ha___` Scope `hc` at @(List `T'TT'I` (Alone `P'T'I'TT'I` Twice `T'TT'I` List `T'TT'I` Tree) `T'I_` i) `ho_'he` Scope `hc` it
   `yok___` Check `ha` is @(Maybe `T'I_` (Alone `P'T'I'TT'I` Twice `T'TT'I` List `T'TT'I` Tree) i)
   `yok___` Apply `ha` State
   `ha____` Event `ha` aloft
   `ho__'ha` Scope `hc` at @(Tree `T'I` i)

  aloft :: forall i . (Alone `P'T'I'TT'I` Twice `T'TT'I` List `T'TT'I` Tree) `T'I` i `AR____` Tree i `AR__` Alone i `P` Tree i
  aloft unfolding tree = Alone `ha` this `ha` top `hc` tree
   `lu_` unfolding `hjd` tree `yi` to @Tree `ha` Aloft @(Alone `P'T'I'TT'I` Shafted List `T'TT'I` Tree)

   -- List `T'TT'I` (T'TT'I List (P'T'I'TT'I Alone (T'TT'I (T'TT'I Twice List) Tree)))

 -- (L (P'T'I'TT'I (P'T'I'TT'I Alone (T'TT'I (T'TT'I Twice List) Tree)) Tree) Tree Void) (F'T'I'TT'I Along List)

  vertical_deep :: forall i . Unit `AR___` (Halts `JNT` State `T` Scrolling Tree i) `T'I_` Alone i
  vertical_deep _ = intro @(Halts `JNT` State `T` Scrolling Tree i) Unit
   `yuk____` Apply `ha` State
    `hv____` Event `hc` fetch
     `ha___` Scope `hc` at @(Tree `T'I` i)
      `ho__` Scope `hc` top @Tree
        `lo` Scope `hc` sub @Tree
   `yok____` Check `ha'yo` splash `ha` moves
   `yok____` Apply `ha` State `ha___` Event `ha` relay `ha` this
    `ho__'ha` Scope `hc` at @(Tree i)
   `lo___'yp` Apply `ha` State `ha___` Event `ha` push `ha` that
    `ho__'ha` Scope `hc` at @(List `T'TT'I` (Alone `P'T'I'TT'I` Twice `T'TT'I` List `T'TT'I` Tree) `T'I_` i)
     `ho_'he` Scope `hc` it @(List `T'I_` (Alone `P'T'I'TT'I` Twice `T'TT'I` List `T'TT'I` Tree) i)
   `ho_____'yo` Alone `ha` this `ha` top @Tree `ha` this

  moves :: forall i . i `P` List (Tree i) `AR___` Maybe (i `P` Nonempty List (Tree i))
  moves x = x `yiokl` Apply `ha` Check `ha` unwrap @(AR)

  splash :: forall i . i `P` (Nonempty List (Tree i)) `AR____` Tree i `P` (Alone `P'T'I'TT'I` Twice `T'TT'I` List `T'TT'I` Tree) i
  splash (These root descendants) = this `ha` top `hc` descendants
   `lu_` Alone `hc` root `hjd` wrap @(AR) `ha` to `ha` Fresh @(Shafted List) `ha` wrap @(AR) @(List _) `ha` this `ha` sub `hc` descendants

  horizontally :: forall i . Shifter List `AR___` (Halts `JNT` State `T` Scrolling Tree i) `T'I_` Alone i
  horizontally way = intro @(Halts `JNT` State `T` Scrolling Tree i) Unit
   `yuk____` Apply `ha` State
   `hv_____` Event `hc` pop
    `ha____` Scope `hc` at @(List `T'TT'I` (Alone `P'T'I'TT'I` Twice `T'TT'I` List `T'TT'I` Tree) `T'I_` i)
    `ho__'he` Scope `hc` it @(List `T'I_` (Alone `P'T'I'TT'I` Twice `T'TT'I` List `T'TT'I` Tree) i)
   `yok____` Check
   `yok____` Apply `ha` State
     `ha___` Event `ha` (\unfolding tree -> scroll `hc` way `hc` unfolding `hc` tree `hjd` tree)
    `ho__'ha` Scope `hc` at @(Tree i)
   `yok____` Apply `ha` State `ha___` Event `ha` relay `ha` this
    `ho__'ha` Scope `hc` at @(Tree i)
   `lo___'yp` Apply `ha` State `ha___` Event `ha` push `ha` that
    `ho__'ha` Scope `hc` at @(List `T'TT'I` (Alone `P'T'I'TT'I` Twice `T'TT'I` List `T'TT'I` Tree) `T'I_` i)
     `ho_'he` Scope `hc` it @(List `T'I_` (Alone `P'T'I'TT'I` Twice `T'TT'I` List `T'TT'I` Tree) i)
   `ho_____'yo` Alone `ha` this `ha` top @Tree `ha` this

  -- TODO: the problem here is that we ignore information about successfulness of horizontal shifting!
  scroll :: forall i . Shifter List
   `AR_____` (Alone `P'T'I'TT'I` Twice `T'TT'I` List `T'TT'I` Tree) `T'I` i
   `AR____` Tree i
   `AR___` (Tree i) `P` (Alone `P'T'I'TT'I` Twice `T'TT'I` List `T'TT'I` Tree `T'I___` i)
  scroll way unfolding tree = 
   let siblings = this `ha` at @(Twice `T'TT'I` List `T'TT'I` Tree `T'I_` i) `ho'he` is `hc` unfolding in
   Alone `hc` tree `hjd` siblings
   `yi` shift `hc` way `ha` is @(Scrolling List `T'I` Tree i)
   `yi` (\x -> unwrap @(AR) `ha` this `ha` at @(Alone `T'I` Tree i) `hc` x `lu_` this `ha` at @(Alone i) `hc` unfolding `hjd` wrap @(AR) `ha` this `ha` at @(Twice `T'TT'I` List `T'I_` Tree i) `hc` x) `ha` that
