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
 mapping = rewrap `hc` \(T'I'TT'II'T'II'I source) ->
  T'I'TT'II'T'II'I `hc` \(Label (F'T'I'TT'I (Recursive (T'TT'I (T'II'I (These xxx x)))))) ->
   Alone `ha` this `ha` source `hc` x `hjd` (\xx -> xxx `hjd` that `ha` source `hc` x `hc` supertype xx)

-- TODO: refactor, pattern matching is redundant here
instance {-# OVERLAPS #-} Component (AT) ((Maybe `T'TT'I` Construction Maybe) `L` Alone `T` (Void) `L` Alone `T` (Void)) Maybe where
 component = T'I'TT'II'T'II'I `hc` \case
  Label (Label (T'TT'I (T'I'II (This _)))) -> supertype Empty `hjd` Label `ha` Label `ha` (Empty `hu` empty `has` (\x' -> x' `ryu` Enter))
  Label (Label (T'TT'I (T'I'II (That (F'T'I'TT'I (Recursive (T'TT'I (T'II'I (These xxx x))))))))) ->
   Exist `hc` x `hjd` Label `ha` Label `ha` (Empty `hu_` T'TT'I `hc` (xxx `yo` F'T'I'TT'I) `has` (\x' -> x' `ryu` Enter @List))

instance {-# OVERLAPS #-} Component (AT) ((Maybe `T'TT'I` Construction Maybe) `L` Alone `T` (Void `P` Void) `L` Alone `T` (Void)) Maybe where
 component = T'I'TT'II'T'II'I `hc` \(Label (Label x)) ->
  supertype Empty `hjd` Label `ha` Label `ha` (Empty `hu` x `has` (\xx -> that (push xx x)))

pattern Adapt :: forall t tt i . t `T` i `AR__` t `L` tt `T` Void `T` i
pattern Adapt x = Label @t @tt @Void x

instance Mapping T'I'II T'I'II (AR) (AR) (Construction Optional `L` List `T` (Void)) List where
 mapping = rewrap `hc` \source -> rewrap `hc__` supertype `ho` wrap @AR `ho'yo` source `ho` Exist

instance Mapping T'I'II T'I'II (AR) (AR) ((Twice `T'TT'I` List) `L` List `T` (Void)) List where
 mapping = rewrap `hc` \source (Label (T'TT'I (T'I'I ((These bs fs))))) -> 
  that (bs `yokl` Prior `ha` Apply `ha` State `ha` Event `ha` push @List `hc___` fs) `yo` source
  -- ((bs `yokl` Prior `ha` Apply `ha` State `ha` Event `ha` push @List `hc___` fs) `yior` source) Unit --supertype That

instance Mapping T'I'II T'I'II (AR) (AR) ((List `P'T'I'TT'I` Twice `T'TT'I` List) `L` List `T` (Void)) List where
 mapping = rewrap `hc` \source (Label (T'TT'I'TTT'I (These x (T'TT'I (T'I'I (These sx xs)))))) ->
  sx `yokl` Forth `ha` Apply `ha` State `ha` Event `ha` push `hc___` x `yi__` that `hjd__` xs `yi__` Merge `ho` to @List `yo__` source

-- instance Mapping T'I'II T'I'II (AR) (AR) (Construction Maybe) (Alone `P'T'I'TT'I` Maybe `T'TT'I` Construction Maybe) where
 -- mapping = rewrap `hc` \source -> Alone `ha` this `ha` top `hop` wrap @(AR) `ha` this `ha` sub `ho_'yo` source

instance Mapping T'I'II T'I'II (AR) (AR) (Construction List `L` (Construction List `P'T'I'TT'I` List `T'TT'I` Unfolding Alone Tree) `T` Void) (Construction List `P'T'I'TT'I` List `T'TT'I` Unfolding Alone Tree) where
 mapping = rewrap `hc` \source x -> supertype x `yo` source `hjd` wrap (empty @List)

instance Mapping T'I'II T'I'II (AR) (AR) ((Construction List `P'T'I'TT'I` List `T'TT'I` Unfolding Alone Tree) `L` Construction List `T` Void) (Construction List) where
 mapping = rewrap `hc` \source (Label (T'TT'I'TTT'I (These tree unfoldings))) ->
  supertype unfoldings `yokl` Forth `ha` Apply `ha` State `ha` Event `ha` cover `hc___` tree `yi__` that `ho'yo` source where

   cover (T'TT'I'TTT'I (These parent siblings)) tree =
    Unit `hjd___` that `ha` sub @Tree
     `hc___` supertype parent `ryu` Enter @Tree
     `hc___` Alone `hc` tree `hjd` supertype siblings
       `yi` to @List `ha` Adapt @(Nonempty List)
       `ha` to @(Nonempty List) `ha` Adapt @(Scrolling List)

instance Mapping T'I'II T'I'II (AR) (AR) (Both (P) `L` Construction Optional `T` Void) (Construction Optional) where
 mapping = rewrap `hc` \source -> rewrap `hc` \(T'I'I (These x xx)) -> Item (source x) `ha` Next `ha` Item (source xx) `ha` Last `hc` Unit

instance Mapping T'I'II T'I'II (AR) (AR) (Both (P) `L` List `T` Void) List where
 mapping = rewrap `hc` \source -> rewrap `hc` \(T'I'I (These x xx)) -> Exist `ha` Nonempty @List `ha` Item (source x) `ha` Next `ha` Item (source xx) `ha` Last `hc` Unit

pattern Stock :: forall t i .
 List i `AR__` List `L` t `T` (Void) `T` i
pattern Stock x = Label x

instance Mapping T'I'II T'I'II (AR) (AR) (List `L` (List `P'T'I'TT'I` Twice `T'TT'I` List) `T` (Void)) (List `P'T'I'TT'I` Twice `T'TT'I` List) where
 mapping = rewrap `hc` \source x -> supertype x `hjd` (empty @List `hjd` empty @List) `yo` source

-- TODO: generalise
pattern Fresh :: forall t i .
 List i `AR__` List `L` t `T` (Void `P` Void) `T` i
pattern Fresh x = Label x

instance Mapping T'I'II T'I'II (AR) (AR) (List `L` (Twice `T'TT'I` List) `T` (Void `P` Void)) (Twice `T'TT'I` List) where
 mapping = rewrap `hc` \source x -> empty @List `hjd` supertype x `yo` source

instance Mapping T'I'II T'I'II (AR) (AR) (List `L` (List `P'T'I'TT'I` Twice `T'TT'I` List) `T` (Void `P` Void)) (List `P'T'I'TT'I` Twice `T'TT'I` List) where
 mapping = rewrap `hc` \source x -> empty @List `hjd` (empty @List `hjd` supertype x) `yo` source

pattern Stump :: forall i e .
 Component (AR) (S'I'II i `L` S'I'II i `T` Void) (S'I'II Unit) =>
 S'I'II i e `AR__` S'I'II i `L` S'I'II i `T` Void `T` e
pattern Stump x = Label x

instance Mapping T'I'II T'I'II (AR) (AR) (S'I'II e `L` S'I'II e `T` Void) (S'I'II Unit) where
 mapping = rewrap `hc` \source ->
  rewrap `hc`((This `compose` constant Unit `has` That `compose` source) `compose` supertype)

pattern Spare :: forall i ii .
 Component (AR) ((P'II'I i `T'TT'I` S'I'II Unit) `L` (P'II'I i `T'TT'I` S'I'II Unit) `T` Void) (S'I'II i) =>
 P'II'I i (S'I'II Unit ii) `AR___` (P'II'I i `T'TT'I` S'I'II Unit) `L` (P'II'I i `T'TT'I` S'I'II Unit) `T` Void `T` ii
pattern Spare x = Label (T'TT'I x)

instance Mapping T'I'II T'I'II (AR) (AR) ((P'II'I i `T'TT'I` S'I'II Unit) `L` (P'II'I i `T'TT'I` S'I'II Unit) `T` Void) (S'I'II i) where
 mapping = rewrap `hc` \source (Label (T'TT'I (T'II'I (These x i)))) -> Empty `hu` Error i `has` Valid `ha` source `hc_` x

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
 mapping = rewrap `hc` \source (Label (T'TT'I'TTT'I (These x xx))) ->
  x `yokl` Prior `ha` Apply `ha` State `ha` Event `ha` push
    `hc___` xx `yi__` that `ho'yo` source

pattern Aloft :: forall t i .
 Component (AR) ((t `P'T'I'TT'I` Tree) `L` Tree `T` (Void `P` Void)) Tree =>
 t `P'T'I'TT'I` Tree `T'I___` i `AR_____` (t `P'T'I'TT'I` Tree) `L` Tree `T` (Void `P` Void) `T` i
pattern Aloft x = Label x

instance Mapping T'I'II T'I'II (AR) (AR)
 ((Alone `P'T'I'TT'I` Twice `T'TT'I` List `P'T'I'TT'I` Tree) `L` Tree `T` (Void `P` Void)) Tree where
  mapping = rewrap `hc` \source (Label (T'TT'I'TTT'I (These scrolling_list tree))) ->
   rewrap (\x -> Alone tree `hjd` that @(Twice `T'TT'I` List `T'I_` _) `ho'yo` (\x' -> x' `ryu` Enter @Tree) `hc` x) scrolling_list
    `yi` Adapt @(Scrolling List) `ho` to @(Nonempty List) `ho` Adapt @(Nonempty List) `ho` to @List `ho'yo` supertype @(AR)
    `yi` this @(Alone _) `ho'st` Root `hc` supertype scrolling_list
    `yo` source

instance Mapping T'I'II T'I'II (AR) (AR)
 ((Alone `P'T'I'TT'I` Twice `T'TT'I` List `T'TT'I` Tree `P'T'I'TT'I` Tree) `L` Tree `T` (Void `P` Void)) Tree where
  mapping = rewrap `hc` \source (Label (T'TT'I'TTT'I (These (T'TT'I'TTT'I (These root siblings)) tree))) ->
   that `ha` sub @Tree
    `hc___` supertype root `ryu` Enter @Tree
    `hc___` Adapt @(Scrolling List) `ho` to @(Nonempty List) `ho` Adapt @(Nonempty List) `ho` to @List
     `hc__` Alone tree `hjd` supertype siblings
    `yo___` source

-- TODO: We haven't finished yet!
-- TODO: I need to heavily test it...
-- instance Mapping T'I'II T'I'II (AR) (AR)
--  ((Alone `P'T'I'TT'I` Twice `T'TT'I` List) `T'TT'I` Tree `P'T'I'TT'I` Unfoldings Alone Tree) (List `T'TT'I` Tree) where
--  mapping = rewrap `hc` \source (T'TT'I'TTT'I (These basement unfoldings)) ->
--   let result = to @List `ha` to @(Nonempty List) `hc'st` basement in
--   Empty `hu` wrap result
--   -- `la______` (\x -> x `yokl` Forth `ha` Apply `ha` State `ha` Event `ha` worker `hc___` result `yi__` that `ho` wrap @(AR))
--   `la______` proceed result
--   `hc_______` unfoldings `yo_______` source where

--    topping unfolding forest = Unit `hjd_____` forest
   
--    starting :: (Alone `P'T'I'TT'I` Twice `T'TT'I` List `T'TT'I` Tree) i `AR_______` List (Tree i) `AR_____` Tree i
--    starting (T'TT'I'TTT'I (These (Identity focused) (T'TT'I (T'TT'I (T'I'I (These sx xs)))))) forest = that `ha` sub @Tree
--     `hc__` intro @Tree `hc` focused `hc__` sx `hjd` (forest `hjd` xs `yi` Merge @List @List `ho` to @List) `yi` to @List @(Twice `T'TT'I` List) @(Tree _)

   -- proceed forest nonempty_list =
   --  let (These x xx) = this `ha` top @(Nonempty List) `hop` this `ha` sub @(Nonempty List) `hc_` nonempty_list in
   --  xx `yokl` Forth `ha` Apply `ha` State `ha` Event `ha` topping `hc___` starting x forest `yi__` that -- `ho` wrap @(
 
  -- supertype (supertype unfoldings)
  --  `yokl` Forth `ha` Apply `ha` State `ha` Event `ha` worker
  --  `hc___` wrap @(AR) @(List `T'TT'I` Tree `T'I_` _) `ha` to @List `ha` to @(Nonempty List) `hc'st` basement
  --  `yi__` that `ho'yo` source where

  --  -- TODO: we haven't finished yet...
  --  worker unfolding forest =
  --   Unit `hjd` (forest)

--  ((Shifting Alone List `T'TT'I` Tree `P'T'I'TT'I` Unfoldings Alone Tree) `TT'T'I` t) where
--  mapping = rewrap `hc` \source -> rewrap `identity`
--   \(T'TT'I'TTT'I (These x (T'TT'I (T'I'I (These l r))))) ->

pattern Focus :: forall i . i `AR__` I `L` Along (Unit `S` Unit) `T` Void `T` i
pattern Focus x = Label (Alone x)

instance {-# OVERLAPS #-} Mapping T'I'II T'I'II (AR) (AR)
 (I `P'T'I'TT'I` Twice `T'TT'I` List)
 ((I `P'T'I'TT'I` Twice `T'TT'I` List) `T'TT'I` Along (Unit `S` Unit) `L` Along (Unit `S` Unit) `T` Void) where
 mapping = rewrap `hc` \source (T'TT'I'TTT'I (These x xs)) ->
  T'TT'I (T'TT'I'TTT'I (These (x `yo` (`hjd` This Unit) `ha` source) (xs `yo` (`hjd` That Unit) `ha` source)))

-- instance {-# OVERLAPS #-} Mapping T'I'II T'I'II (AT) (AT) (I `P'T'I'TT'I` Twice `T'TT'I` List)
--  ((I `P'T'I'TT'I` Twice `T'TT'I` List) `T'TT'I` Along (Unit `S` Unit) `L` Along (Unit `S` Unit) `T` Void) where
  
 -- component = T'I'TT'II'T'II'I `hc` \(Label (Label x)) ->
  -- supertype Empty `hjd` Label `ha` Label `ha` (Empty `hu` x `has` (\xx -> that (push xx x)))

instance {-# OVERLAPS #-} Mapping T'I'II T'I'II (AR) (AR) (Construction List `P'T'I'TT'I` List `T'TT'I` Unfolding I `T'I` Construction List)
 ((Construction List `P'T'I'TT'I` List `T'TT'I` Unfolding I `T'I` Construction List) `T'TT'I` Along (Unit `S` Unit) `L` Along (Unit `S` Unit) `T` Void) where
 mapping = rewrap `hc` \source (T'TT'I'TTT'I (These (F'T'I'TT'I (Recursive (T'TT'I (T'II'I (These xx x))))) xxx)) ->
  xx `yo` wrapped @(AR) @(F'T'I'TT'I Along _ _) (`yo` source `ho` (`hjd` That Unit)) `hjd_` source x `hjd` This Unit `hjd_` xxx `yo` source `ho` (`hjd` That Unit)

pattern Frame :: forall i . i `AR__` I `L` Along (Unit `S` Unit) `T` (Void `P` Void) `T` i
pattern Frame x = Label (Alone x)

instance {-# OVERLAPS #-} Mapping T'I'II T'I'II (AR) (AR)
 (I `P'T'I'TT'I` Twice `T'TT'I` List) ((I `P'T'I'TT'I` Twice `T'TT'I` List) `T'TT'I` Along (Unit `S` Unit) `L` Along (Unit `S` Unit) `T` (Void `P` Void)) where
 mapping = rewrap `hc` \source (T'TT'I'TTT'I (These x xs)) ->
  x `yo` (`hjd` That Unit) `ha` source `hjd_` xs `yo` (`hjd` This Unit) `ha` source

instance {-# OVERLAPS #-} Mapping T'I'II T'I'II (AR) (AR) (Construction List `P'T'I'TT'I` List `T'TT'I` Unfolding I `T'I` Construction List)
 ((Construction List `P'T'I'TT'I` List `T'TT'I` Unfolding I `T'I` Construction List) `T'TT'I` Along (Unit `S` Unit) `L` Along (Unit `S` Unit) `T` (Void `P` Void)) where
 mapping = rewrap `hc` \source (T'TT'I'TTT'I (These (F'T'I'TT'I (Recursive (T'TT'I (T'II'I (These xx x))))) xxx)) ->
  xx `yo` wrapped @(AR) @(F'T'I'TT'I Along _ _) (`yo` source `ho` (`hjd` This Unit)) `hjd_` source x `hjd` That Unit `hjd_` xxx `yo` source `ho` (`hjd` This Unit)

instance
 ( Covariant Endo Semi Functor (->) t
 ) => Mapping T'I'II T'I'II (AR) (AR) (Construction t) (Construction t `T'TT'I` Construction t `L` Construction t `T` Void) where
 mapping = rewrap `hc` \source -> rewrap `ha` rewrap `ha` rewrap `ha` rewrap `hc` \(These xx x) ->
  (xx `yo` supertype @AR `ha` supertype @AR `ha` (map @T'I'II @T'I'II @(AR) @(AR) @(Construction t) @(Construction t `T'TT'I` Construction t `L` Construction t `T` Void) source) `ha` F'T'I'TT'I)
  `hjd` Label (xx `hjd` x `yo` source)

-- instance Mapping T'I'II T'I'II (AR) (AR)
--  ((Alone `P'T'I'TT'I` Twice `T'TT'I` List) `T'TT'I` Tree `P'T'I'TT'I` Unfoldings Alone Tree)
--  (((Alone `P'T'I'TT'I` Twice `T'TT'I` List) `T'TT'I` Tree `P'T'I'TT'I` Unfoldings Alone Tree) `T'TT'I` Along (Unit `S` Unit) `L` Along (Unit `S` Unit) `T` Void) where
--  mapping = rewrap `hc` \source -> rewrap `identity`
--   \(These (T'TT'I (T'TT'I'TTT'I (These (Identity (F'T'I'TT'I (Recursive (T'TT'I (T'II'I (These xx x)))))) xxx))) xxxx) ->
--    xx `yo` wrapped @(AR) @(Tree _) (fo ((`hjd` That Unit) `ha` source))
--     `hjd_` x `yi` (`hjd` This Unit) `ha` source
--     `hjd_` xxx `yo'yo` (`hjd` That Unit) `ha` source
--     `hjd_` xxxx `yo` (`hjd` That Unit) `ha` source

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
   `ha` (is `hu` (source `ha` this `ha` top `hc` xx `hjd` That Unit) `has` is `hu` (source `ha` this `ha` top `hc` xx `hjd` This Unit))
   `ha` (\xxx -> this `ha` sub `hc` xxx `hjd'ys` (Unit `ryu` Apply @t) `yokl` Apply `ha` Check `ha__` Error `hu` Error Unit `has` Valid)
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

--  mapping = rewrap `hc` \source -> rewrap `identity`
--   \(T'TT'I'TTT'I (These x (T'TT'I (T'I'I (These l r))))) ->

pattern Alter :: forall t i .
 Component (AR) (T'I'I t `L` T'I'I t `T` Void) (T'I'I t) =>
 T'I'I t i `AR__` T'I'I t `L` T'I'I t `T` Void `T` i
pattern Alter x = Label x

instance Mapping T'I'II T'I'II (AR) (AR) (T'I'I (P) `L` T'I'I (P) `T` Void) (T'I'I (P)) where
 mapping = rewrap `hc` \source -> rewrap `hc`(source `ha` that `hop` source `ha` this `ha__` supertype @(AR))

instance Mapping T'I'II T'I'II (AR) (AR) (T'I'I (S) `L` T'I'I (S) `T` Void) (T'I'I (S)) where
 mapping = rewrap `hc` \source -> rewrap `hc`(source `ho` That `has` source `ho` This `ha__` supertype @(AR))

pattern Aback x = This x :: Shifter List
pattern Ahead x = That x :: Shifter List

pattern Above x = This x :: Shifter List
pattern Below x = That x :: Shifter List

pattern Front :: forall i tt target .
 tt i `AR__` tt `L` Alone `T` (Void) `T` i
pattern Front x = Label x

instance Shiftable Alone (Maybe `T'TT'I` Construction Maybe) where
 shift :: forall i . Shifter List `AR___` Supertype (Event `T'I` Shifting Alone List i `T'I` Maybe (Alone i))
 shift way x = is `hc_` Empty `hu` (Empty Unit `hjd` x) `has` is `ho'st` foi @_ @(AR) Exist `hc_` _shift_ `hc` x where

  _shift_ = Unit `ryu` Enter @(Halts `JNT` State `T` Scrolling List i)
   `yuk___` Apply `ha` State
   `hc____` Event `ha` relay `hc'st` Empty
    `ha___` Scope `hc` at @(Shafted List i)
   `ho__'st` Scope `ha` by @Twice `ha` (Back `has` Fore) `hc` way
     `ho__` Scope `hc` (as `ha` Front `ha` Stock @Alone)
   `yok___` Check
   `yok___` Apply `ha` State
   `ha____` Event `ha` relay `ha` Alone
   `ho__'ha` Scope `hc` at @(Alone i)
   `yok___` Apply `ha` State
   `ha____` Event `ha` relay `ha'st` Exist
   `ho__'ha` Scope `hc` at @(Shafted List i)
    `ho_'st` Scope `ha` by `ha` (Fore `has` Back) `hc` way
      `ho_` Scope `hc` (as `ha` Front `ha` Fresh @Alone)
   -- TODO: there it is - if I use `Lease` label instead of `Apply` state doesn't change
   `yuk___` Apply `ha` State
   `hc____` Event `hc` fetch
    `ha___` Scope `hc` at @(Alone i)

 spot :: forall i . Shifter List `P` Match (Alone i) `AR_` Supertype (Event `T'I` Shifting Alone List i `T'I` Maybe `T` Shifting Alone List i)
 spot (These way predicate) x = foi Exist `ha` fetch `has` is `ho'st` foi @_ @(AR) (Empty `hu` Empty Unit) `hc_` _spot_ `hc` x where

  found (These w sl) = supertype (predicate `hc` w) `yui` sl `yiu` sl

  _spot_ = Unit `ryu` Enter @(Stops `T` Scrolling List i `JNT` State `T` Scrolling List i)
   `yuk____` Lease `ha` State `hc___` Event `hc__` fetch `ha__` Scope `hc` at @(Alone i) `hop` Scope `hc` it
   `yok____` Check `ha` Stops `ha___` not `ha` found
   `yuk____` Apply `ha` State `hc___` Event `hc__` shift `hc` way
   `yok____` Retry `ha` is `ha__` Break `hu` Ok Unit `has` Again `hu` Reach Unit

instance Shiftable List (Maybe `T'TT'I` Construction Maybe) where
 shift :: forall i . Shifter List `AR___` Supertype (Event `T'I` Shifting List List i `T'I` Maybe (List i))
 shift way x = is
  `hc_` is `hu` (Empty Unit `hjd` x)
  `has` is `ho'st` foi @_ @(AR) Exist
  `hc_` (slide_passed `lv` slide_future `hc_` way) `hc` x where

  slide_future = Unit `ryu` Enter @(Halts `JNT` State `T` Sliding List i)
   `yuk____` Apply `ha` State `hc___` Event `hc` pop `ha_` Scope `hc` at @(List _)
   `yok____` Check
   `yok____` Apply `ha` State `ha___` Event `ha` push `ho__'ha` Scope `hc` at @(Shafted List i) `ho_'st` Scope `ha` by `hc'st` Aback
   `yuk____` Apply `ha` State `hc___` Event `hc` pop `ha__` Scope `hc` at @(Shafted List i) `ho_'st` Scope `ha` by `hc'st` Ahead
   `yok____` Check
   `yok____` Apply `ha` State `ha____` Event `ha` window_future `ho_'ha` Scope `hc` at @(List _)

  slide_passed = Unit `ryu` Enter @(Halts `JNT` State `T` Sliding List _)
   `yuk____` Apply `ha` State `hc___` Event `hc` pop `ha__` Scope `hc` at @(Shafted List i) `ho_'st` Scope `ha` by `hc'st` Aback
   `yok____` Check
   `yok____` Apply `ha` State `ha___` Event `ha` window_extract_last `ho_'ha` Scope `hc` at @(List _)
   `yok____` Check
   `yok____` Apply `ha` State `ha___` Event `ha` push `ho__'ha` Scope `hc` at @(Shafted List i) `ho_'st` Scope `ha` by `hc'st` Ahead
   `yuk____` Apply `ha` State `hc___` Event `hc` fetch `ha__` Scope `hc` at @(List _)

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
  `hc_` is `hu` (Empty Unit `hjd` x)
  `has` is `ho'st` foi @_ @(AR) Exist
  `hc_` (horizontally `has_` vertical_deep `has` vertical_up `hc___` way) `hc` x where

  vertical_up :: forall i . Unit `AR___` (Halts `JNT` State `T` Scrolling Tree i) `T'I_` Alone i
  vertical_up _ = Unit `ryu` Enter @(Halts `JNT` State `T` Scrolling Tree i)
   `yuk___` Apply `ha` State
   `hc____` Event `hc` pop
    `ha___` Scope `hc` at @(List `T'TT'I` (Alone `P'T'I'TT'I` Twice `T'TT'I` List `T'TT'I` Tree) `T'I_` i) `ho_'st` Scope `hc` it
   `yok___` Check `ha` is @(Maybe `T'I_` (Alone `P'T'I'TT'I` Twice `T'TT'I` List `T'TT'I` Tree) i)
   `yok___` Apply `ha` State
   `ha____` Event `ha` aloft
   `ho__'ha` Scope `hc` at @(Tree `T'I` i)

  aloft :: forall i . (Alone `P'T'I'TT'I` Twice `T'TT'I` List `T'TT'I` Tree) `T'I` i `AR____` Tree i `AR__` Alone i `P` Tree i
  aloft unfolding tree = Alone `ha` this `ha` top `hc` tree
   `hjd_` unfolding `hjd` tree `yi` to @Tree `ha` Aloft @(Alone `P'T'I'TT'I` Shafted List `T'TT'I` Tree)

   -- List `T'TT'I` (T'TT'I List (P'T'I'TT'I Alone (T'TT'I (T'TT'I Twice List) Tree)))

 -- (L (P'T'I'TT'I (P'T'I'TT'I Alone (T'TT'I (T'TT'I Twice List) Tree)) Tree) Tree Void) (F'T'I'TT'I Along List)

  vertical_deep :: forall i . Unit `AR___` (Halts `JNT` State `T` Scrolling Tree i) `T'I_` Alone i
  vertical_deep _ = Unit `ryu` Enter @(Halts `JNT` State `T` Scrolling Tree i)
   `yuk____` Apply `ha` State
    `hc____` Event `hc` fetch
     `ha___` Scope `hc` at @(Tree `T'I` i)
      `ho__` Scope `hc` top @Tree
        `hop` Scope `hc` sub @Tree
   `yok____` Check `ha'yo` splash `ha` moves
   `yok____` Apply `ha` State `ha___` Event `ha` relay `ha` this
    `ho__'ha` Scope `hc` at @(Tree i)
   `lo___'yp` Apply `ha` State `ha___` Event `ha` push `ha` that
    `ho__'ha` Scope `hc` at @(List `T'TT'I` (Alone `P'T'I'TT'I` Twice `T'TT'I` List `T'TT'I` Tree) `T'I_` i)
     `ho_'st` Scope `hc` it @(List `T'I_` (Alone `P'T'I'TT'I` Twice `T'TT'I` List `T'TT'I` Tree) i)
   `ho_____'yo` Alone `ha` this `ha` top @Tree `ha` this

  moves :: forall i . i `P` List (Tree i) `AR___` Maybe (i `P` Nonempty List (Tree i))
  moves x = x `yiokl` Apply `ha` Check `ha` supertype @(AR)

  splash :: forall i . i `P` (Nonempty List (Tree i)) `AR____` Tree i `P` (Alone `P'T'I'TT'I` Twice `T'TT'I` List `T'TT'I` Tree) i
  splash (These root descendants) = this `ha` top `hc` descendants
   `hjd_` Alone `hc` root `hjd` wrap @(AR) `ha` to `ha` Fresh @(Shafted List) `ha` wrap @(AR) @(List _) `ha` this `ha` sub `hc` descendants

  horizontally :: forall i . Shifter List `AR___` (Halts `JNT` State `T` Scrolling Tree i) `T'I_` Alone i
  horizontally way = Unit `ryu` Enter @(Halts `JNT` State `T` Scrolling Tree i)
   `yuk____` Apply `ha` State
   `hc_____` Event `hc` pop
    `ha____` Scope `hc` at @(List `T'TT'I` (Alone `P'T'I'TT'I` Twice `T'TT'I` List `T'TT'I` Tree) `T'I_` i)
    `ho__'st` Scope `hc` it @(List `T'I_` (Alone `P'T'I'TT'I` Twice `T'TT'I` List `T'TT'I` Tree) i)
   `yok____` Check
   `yok____` Apply `ha` State
     `ha___` Event `ha` (\unfolding tree -> scroll `hc` way `hc` unfolding `hc` tree `hjd` tree)
    `ho__'ha` Scope `hc` at @(Tree i)
   `yok____` Apply `ha` State `ha___` Event `ha` relay `ha` this
    `ho__'ha` Scope `hc` at @(Tree i)
   `lo___'yp` Apply `ha` State `ha___` Event `ha` push `ha` that
    `ho__'ha` Scope `hc` at @(List `T'TT'I` (Alone `P'T'I'TT'I` Twice `T'TT'I` List `T'TT'I` Tree) `T'I_` i)
     `ho_'st` Scope `hc` it @(List `T'I_` (Alone `P'T'I'TT'I` Twice `T'TT'I` List `T'TT'I` Tree) i)
   `ho_____'yo` Alone `ha` this `ha` top @Tree `ha` this

  -- TODO: the problem here is that we ignore information about successfulness of horizontal shifting!
  scroll :: forall i . Shifter List
   `AR_____` (Alone `P'T'I'TT'I` Twice `T'TT'I` List `T'TT'I` Tree) `T'I` i
   `AR____` Tree i
   `AR___` (Tree i) `P` (Alone `P'T'I'TT'I` Twice `T'TT'I` List `T'TT'I` Tree `T'I___` i)
  scroll way unfolding tree = 
   let siblings = this `ha` at @(Twice `T'TT'I` List `T'TT'I` Tree `T'I_` i) `ho'st` is `hc` unfolding in
   Alone `hc` tree `hjd` siblings
   `yi` shift `hc` way `ha` is @(Scrolling List `T'I` Tree i)
   `yi` (\x -> supertype @(AR) `ha` this `ha` at @(Alone `T'I` Tree i) `hc` x `hjd_` this `ha` at @(Alone i) `hc` unfolding `hjd` wrap @(AR) `ha` this `ha` at @(Twice `T'TT'I` List `T'I_` Tree i) `hc` x) `ha` that
