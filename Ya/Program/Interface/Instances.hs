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
import Ya.Program.Interface.Shiftable

-- TODO: think about labels for these two instances below!

instance Mapping T'I'II T'I'II (AT) (AT) Maybe Maybe where
 mapping = rewrap `identity` \(T'I'TT'II'T'II'I source) ->
  T'I'TT'II'T'II'I `identity` \case
   T'I'II (This _) -> T'I'II `har'st` This @Unit `hjd_` is `ho'ut'st` Empty
   T'I'II (That x) -> T'I'II `ha` That `ha` this `har` source x `hjd__` Empty `ho'ut'st` Empty `bt'has_` Exist `ha` that (source x)

instance Mapping T'I'II T'I'II (AT) (AT) (Construction Maybe) (Construction Maybe) where
 mapping = rewrap `identity` \(T'I'TT'II'T'II'I source) ->
  T'I'TT'II'T'II'I `identity` \x -> x `yo` this `ha` source
   `hjd_'tb` (\xx -> x `yo` that `ha` source `hjd_'yp` Align `har` xx `yo_` hdj @(AR))

instance Mapping T'I'II T'I'II (AT) (AT) (Maybe `T'TT'I` Construction Maybe) (Maybe `T'TT'I` Construction Maybe) where
 mapping = rewrap `identity` \(T'I'TT'II'T'II'I source) ->
  T'I'TT'II'T'II'I `identity` \x -> x `yo` this `ha` source
   `hjd_` (\xx -> x `yo` that `ha` source `hjd_'yp` Align `har` xx `yo_` hdj @(AR))

pattern Root :: forall t i .
 t i `AR__` t `L` Alone `T` (Void) `T` i
pattern Root x = Label x

instance Mapping T'I'II T'I'II (AT) (AT) ((Construction t) `L` Alone `T` Void) Alone where
 mapping = rewrap `identity` \(T'I'TT'II'T'II'I source) ->
  T'I'TT'II'T'II'I `identity` \(Label (F'T'I'TT (Recursive (T'TT'I (T'II'I (These xxx x)))))) ->
   Alone `ha` this `ha` source `har` x `hjd'tb` (\xx -> xxx `hjd_'tb` that `ha` source `har` x `har` supertype xx)

-- First

-- TODO: refactor, pattern matching is redundant here
instance {-# OVERLAPS #-} Component (AT) (List `L` Maybe `T` (Void)) Maybe where
 component = T'I'TT'II'T'II'I `identity` \case
  Label (T'TT'I (T'I'II (This _))) -> supertype Empty `hjd` Label `ha` (\_ -> Null `ho'vt` Unit `ryo` Enter)
  Label (T'TT'I (T'I'II (That (F'T'I'TT (Recursive (T'TT'I (T'II'I (These xxx x)))))))) ->
   Exist `har` x `hjd` Label `ha` (Empty `ho'ut` T'TT'I (xxx `yo` F'T'I'TT) `bt'has` (\x' -> T'TT'I (T'I'II (That (F'T'I'TT (Recursive (T'TT'I (T'II'I (These xxx x')))))))))

instance {-# OVERLAPS #-} Component (TR) (List `L` Maybe `T` (Void)) Maybe where
 component = T'I'TT'II'I `identity` \case
  Label (T'TT'I (T'I'II (This _))) -> Empty Unit `hjd` Label (T'TT'I (Empty Unit))
  Label (T'TT'I (Exist (Build (Recursive (T'TT'I (T'II'I (These xs x))))))) -> Exist x `hjd__` Label `ha` T'TT'I `har_` xs `yo` F'T'I'TT

pattern Adapt :: forall t tt i . t `T` i `AR__` t `L` tt `T` Void `T` i
pattern Adapt x = Label @t @tt @Void x

instance Mapping T'I'II T'I'II (AR) (AR) (Construction Optional `L` List `T` (Void)) List where
 mapping = rewrap `identity` \source -> rewrap `har_` supertype `ho` subtype @AR `ho'yo` source `ho` Exist

instance Mapping T'I'II T'I'II (AR) (AR)
 (Construction Maybe `L` (I `P'T'I'TT'I` Twice `T'TT'I` List) `T` (Void))
 (I `P'T'I'TT'I` Twice `T'TT'I` List) where
 mapping = rewrap `identity` \source (Label (F'T'I'TT (Recursive (T'TT'I (T'II'I (These xs x)))))) ->
  Alone `har` source x `hjd___'tb` T'TT'I (Empty Unit) `hjd_'tb` T'TT'I (xs `yo` F'T'I'TT) `yo` source

instance Mapping T'I'II T'I'II (AR) (AR) ((I `P'T'I'TT'I` Twice `T'TT'I` List) `L` Construction Maybe `T` Void) (Construction Maybe) where
 mapping = rewrap `identity` \source (Label (T'TT'I'TTT'I (These x (T'TT'I (T'I'I (These l r)))))) ->
  l `yokl_` Forth `ha` Apply `ha` State `ha___` Event `ha` Push `ho__'ha` Scope `har` within @(Nonempty List) @Maybe `ha` Fresh
   `bt'har___` derive `ha` Merge `ha` Clasp `har_` x `hjd` r
   `yi___` that `ho'yo` source

-- TODO: replace it with `Merge`
-- instance Mapping T'I'II T'I'II (AR) (AR) ((Twice `T'TT'I` List) `L` List `T` (Void)) List where
 -- mapping = rewrap `identity` \source (Label (T'TT'I (T'I'I ((These bs fs))))) -> 
  -- that (bs `yokl` Prior `ha` Apply `ha` State `ha` Event `ha` push @List `bt'har__` fs) `yo` source

-- instance Mapping T'I'II T'I'II (AR) (AR) ((List `P'T'I'TT'I` Twice `T'TT'I` List) `L` List `T` (Void)) List where
 -- mapping = rewrap `identity` \source (Label (T'TT'I'TTT'I (These x (T'TT'I (T'I'I (These sx xs)))))) ->
  -- sx `yokl` Forth `ha` Apply `ha` State `ha` Event `ha` push `bt'har__` x `yi__` that `hjd__'tb` xs `yi__` Merge `ho` derive `yo__` source

-- instance Mapping T'I'II T'I'II (AR) (AR) (Construction Maybe) (Alone `P'T'I'TT'I` Maybe `T'TT'I` Construction Maybe) where
 -- mapping = rewrap `identity` \source -> Alone `ha` this `ha` top `hop` subtype @(AR) `ha` this `ha` sub `ho_'yo` source

instance Mapping T'I'II T'I'II (AR) (AR) (Construction List `L` (Construction List `P'T'I'TT'I` List `T'TT'I` Unfolding Alone Tree) `T` Void) (Construction List `P'T'I'TT'I` List `T'TT'I` Unfolding Alone Tree) where
 mapping = rewrap `identity` \source x -> supertype x `yo` source `hjd'tb` subtype (Null `ho'vt` Unit `ryo` Enter)

instance Mapping T'I'II T'I'II (AR) (AR) ((Construction List `P'T'I'TT'I` List `T'TT'I` Unfolding Alone Tree) `L` Construction List `T` Void) (Construction List) where
 mapping = rewrap `identity` \source (Label (T'TT'I'TTT'I (These tree unfoldings))) ->
  supertype unfoldings `yokl` Forth `ha` Apply `ha` State `ha` Event `ha` cover `bt'har__` tree `yi__` that `ho'yo` source where

   cover (T'TT'I'TTT'I (These parent siblings)) tree =
    Unit `hjd___'tb` that `ha` sub @Tree
     `har__` Only `ho'ut` supertype parent `ryo` Enter @Tree
     `har__` Alone `har` tree `hjd'tb` supertype siblings
       `yi` derive `ha` Adapt @(Nonempty List)
       `ha` derive `ha` Adapt @(Scrolling List)

instance Mapping T'I'II T'I'II (AR) (AR) (T'I'I (P) `L` Construction Optional `T` Void) (Construction Optional) where
 mapping = rewrap `identity` \source -> rewrap `identity` \(T'I'I (These x xx)) -> Item (source x) `ha` Next `ha` Item (source xx) `ha` Last `har` Unit

instance Mapping T'I'II T'I'II (AR) (AR) (T'I'I (P) `L` List `T` Void) List where
 mapping = rewrap `identity` \source -> rewrap `identity` \(T'I'I (These x xx)) -> Exist `ha` Nonempty @List `ha` Item (source x) `ha` Next `ha` Item (source xx) `ha` Last `har` Unit

-- pattern Ended
-- pattern Begin

pattern Stock :: forall tt t i .
 t i `AR__` t `L` tt `T` (Void) `T` i
pattern Stock x = Label x

instance Mapping T'I'II T'I'II (AR) (AR) (List `L` (List `P'T'I'TT'I` Twice `T'TT'I` List) `T` (Void)) (List `P'T'I'TT'I` Twice `T'TT'I` List) where
 mapping = rewrap `identity` \source x -> supertype x `hjd'tb` (Null `ho'vt` Unit `ryo` Enter @List `hjd__'tb` Null `ho'vt` Unit `ryo` Enter @List) `yo` source

instance Component (AR) (List `L` Maybe `T` (Void)) Maybe where
 component = \case
  Label (T'TT'I (T'I'II (This _))) -> supertype Empty
  Label (T'TT'I (T'I'II (That (F'T'I'TT (Recursive (T'TT'I (T'II'I (These _ x)))))))) -> Exist `har` x

pattern Fresh :: forall t i ii . t ii `AR__` t `L` Stops i `T` (Void `P` Void) `T` ii
pattern Fresh x = Label x

instance {-# OVERLAPS #-}
 ( forall e . Covariant Mapping T'I'II (AR) (AR) (T'I'II (AR) Unit) t
 ) => Component (AR) (Construction t `L` Maybe `T` (Void `P` Void)) Maybe where
 component _ = supertype Empty

instance {-# OVERLAPS #-}
 Component (AR) ((Maybe `T'TT'I` Construction Maybe) `L` Maybe `T` (Void `P` Void)) Maybe where
 component _ = supertype Empty

instance {-# OVERLAPS #-}
 ( forall e . Covariant Mapping T'I'II (AR) (AR) (T'I'II (AR) Unit) t
 ) => Component (AT) (Construction t `L` Maybe `T` (Void `P` Void)) Maybe where
 component = T'I'TT'II'T'II'I `identity` \(Label x) ->
  supertype Empty `hjd` Label `ha` (Empty `ho'ut` x `bt'has` (F'T'I'TT `ha` Recursive `ha` T'TT'I `ha` T'II'I `ha` (Pass `ho'ut'st` x `ryo` Enter @t `hjd_`)))

instance {-# OVERLAPS #-}
 Component (AT) ((Maybe `T'TT'I` Construction Maybe) `L` Maybe `T` (Void `P` Void)) Maybe where
 component = T'I'TT'II'T'II'I `identity` \(Label x) ->
  supertype Empty `hjd` Label `ha` (\xx -> rewrap (`yo` (\x' -> that `ha` within @(Nonempty List) @Maybe `ha` Fresh `har` x' `har` xx)) x)

-- instance Mapping T'I'II T'I'II (AR) (AR) (List `L` (Twice `T'TT'I` List) `T` (Void)) (Twice `T'TT'I` List) where

{-
instance Mapping T'I'II T'I'II (AR) (AR) (List `L` (Twice `T'TT'I` List) `T` (Void `P` Void)) (Twice `T'TT'I` List) where
 mapping = rewrap `identity` \source x -> Null `ho'vt` Unit `ryo` Enter @List `hjd_'tb` supertype x `yo` source

instance Mapping T'I'II T'I'II (AR) (AR) (List `L` (List `P'T'I'TT'I` Twice `T'TT'I` List) `T` (Void `P` Void)) (List `P'T'I'TT'I` Twice `T'TT'I` List) where
 mapping = rewrap `identity` \source x -> Null `ho'vt` Unit `ryo` Enter @List `hjd_'tb` (Null `ho'vt` Unit `ryo` Enter @List `hjd_'tb` supertype x) `yo` source
-}

pattern Locus :: forall tt t i .
 t i `AR__` t `L` tt `T` (Void) `T` i
pattern Locus x = Label x

instance {-# OVERLAPS #-} Component (AR) ((Alone `P'T'I'TT'I` (Twice `T'TT'I` List)) `L` Alone `T` Void) Alone where
 component (Label (T'TT'I'TTT'I (These x xxx))) = x

instance {-# OVERLAPS #-} Component (AR) ((Tree `P'T'I'TT'I` List `T'TT'I` (Alone `P'T'I'TT'I` Twice `T'TT'I` List `T'TT'I` Tree)) `L` Tree `T` Void) Tree where
 component (Label (T'TT'I'TTT'I (These x xxx))) = x

instance {-# OVERLAPS #-} Component (AT) ((Alone `P'T'I'TT'I` (Twice `T'TT'I` List)) `L` Alone `T` Void) Alone where
 component = T'I'TT'II'T'II'I `identity` \(Label (T'TT'I'TTT'I (These x xxx))) -> x `hjd'tb` (`hjd'tb` xxx)

instance {-# OVERLAPS #-} Component (AT) ((Tree `P'T'I'TT'I` List `T'TT'I` (Alone `P'T'I'TT'I` Twice `T'TT'I` List `T'TT'I` Tree)) `L` Tree `T` Void) Tree where
 component = T'I'TT'II'T'II'I `identity` \(Label (T'TT'I'TTT'I (These x xxx))) -> x `hjd'tb` (`hjd'tb` xxx)

pattern Shaft :: forall t i . t i `AR____` t `L` (Twice `T'TT'I` List) `T` (Void) `T` i
pattern Shaft x = Label x

instance {-# OVERLAPS #-} Component (AR) ((Alone `P'T'I'TT'I` (Twice `T'TT'I` List)) `L` (Twice `T'TT'I` List) `T` Void) (Twice `T'TT'I` List) where
 component = \(Label (T'TT'I'TTT'I (These x xx))) -> xx

instance {-# OVERLAPS #-} Component (AT) ((Alone `P'T'I'TT'I` (Twice `T'TT'I` List)) `L` (Twice `T'TT'I` List) `T` Void) (Twice `T'TT'I` List) where
 component = T'I'TT'II'T'II'I `identity` \(Label (T'TT'I'TTT'I (These x xx))) -> xx `hjd'tb` (x `hjd'tb`)

instance {-# OVERLAPS #-} Component (AR) ((Tree `P'T'I'TT'I` (List `T'TT'I` (Alone `P'T'I'TT'I` Twice `T'TT'I` List `T'TT'I` Tree))) `L` (List `T'TT'I` (Alone `P'T'I'TT'I` Twice `T'TT'I` List `T'TT'I` Tree)) `T` Void) (List `T'TT'I` (Alone `P'T'I'TT'I` Twice `T'TT'I` List `T'TT'I` Tree)) where
 component = \(Label (T'TT'I'TTT'I (These x xx))) -> xx

instance {-# OVERLAPS #-} Component (AT) ((Tree `P'T'I'TT'I` (List `T'TT'I` (Alone `P'T'I'TT'I` Twice `T'TT'I` List `T'TT'I` Tree))) `L` (List `T'TT'I` (Alone `P'T'I'TT'I` Twice `T'TT'I` List `T'TT'I` Tree)) `T` Void) (List `T'TT'I` (Alone `P'T'I'TT'I` Twice `T'TT'I` List `T'TT'I` Tree)) where
 component = T'I'TT'II'T'II'I `identity` \(Label (T'TT'I'TTT'I (These x xx))) -> xx `hjd'tb` (x `hjd'tb`)

pattern Stump :: forall i e .
 Component (AR) (S'I'II i `L` S'I'II Unit `T` Void) (S'I'II Unit) =>
 S'I'II i e `AR__` S'I'II i `L` S'I'II Unit `T` Void `T` e
pattern Stump x = Label x

instance Mapping T'I'II T'I'II (AR) (AR) (S'I'II e `L` S'I'II Unit `T` Void) (S'I'II Unit) where
 mapping = rewrap `identity` \source ->
  rewrap `har` (This `compose` constant Unit `has` That `compose` source) `compose` supertype

pattern Spare :: forall i ii .
 Component (AR) ((P'II'I i `T'TT'I` S'I'II Unit) `L` (P'II'I i `T'TT'I` S'I'II Unit) `T` Void) (S'I'II i) =>
 P'II'I i (S'I'II Unit ii) `AR___` (P'II'I i `T'TT'I` S'I'II Unit) `L` (P'II'I i `T'TT'I` S'I'II Unit) `T` Void `T` ii
pattern Spare x = Label (T'TT'I x)

instance Mapping T'I'II T'I'II (AR) (AR) ((P'II'I i `T'TT'I` S'I'II Unit) `L` (P'II'I i `T'TT'I` S'I'II Unit) `T` Void) (S'I'II i) where
 mapping = rewrap `identity` \source (Label (T'TT'I (T'II'I (These x i)))) -> Empty `ho'ut` Error i `bt'has` Valid `ha` source `har` x

-- pattern Chary :: forall i ii .
 -- Component (AR) ((P'II'I ii `T'TT'I` S'I'II Unit) `L` (P'II'I ii `T'TT'I` S'I'II Unit) `T` Void) (S'I'II ii) =>
 -- P'II'I ii (S'I'II iii i) `AR___` (P'II'I ii `T'TT'I` S'I'II iii) `L` (P'II'I ii `T'TT'I` S'I'II iii) `T` Void `T` i
-- pattern Chary x = Label (T'TT'I x)

pattern Merge :: forall t tt ttt i .
 ( Covariant Endo Semi Functor (->) tt
 , Covariant Endo Yoneda Functor (->) t
 ) => t `P'T'I'TT'I` tt `T'I___` i `AR_______` (t `P'T'I'TT'I` tt) `L` ttt `T` (Void) `T` i
pattern Merge x = Label x

instance
 ( Covariant Endo Semi Functor (AR) t
 , forall e . Covariant Transformation Functor (AR) (AR)
  (t `T'TT'I` State (F'T'I'TT (T'II'I P) (T'I'II S Unit) `T'I_` e) `L` State (F'T'I'TT (T'II'I P) (T'I'II S Unit) `T'I_` e) `T` (Void) `L` t `T` (Void `P` Void))
  (t `TT'T'I` State (F'T'I'TT (T'II'I P) (T'I'II S Unit) `T'I_` e))
 ) => Mapping T'I'II T'I'II (AR) (AR)
  ((t `P'T'I'TT'I` F'T'I'TT (T'II'I P) (T'I'II S Unit)) `L` (F'T'I'TT (T'II'I P) (T'I'II S Unit)) `T` (Void))
  (F'T'I'TT (T'II'I P) (T'I'II S Unit)) where
 mapping = rewrap `identity` \source (Label (T'TT'I'TTT'I (These x xx))) ->
  x `yokl_` Prior `ha` Apply `ha` State `ha___` Event `ha` Push `ho__'ha` Scope `har` within `ha` Fresh
   `bt'har___` xx `yi____` that `ho'yo` source

instance
 ( Covariant Endo Semi Functor (AR) t
 , forall e . Covariant Transformation Functor (AR) (AR)
  (t `T'TT'I` State (T'I'II S Unit `T'TT'I` F'T'I'TT (T'II'I P) (T'I'II S Unit) `T'I_` e) `L` State (T'I'II S Unit `T'TT'I` F'T'I'TT (T'II'I P) (T'I'II S Unit) `T'I_` e) `T` (Void) `L` t `T` (Void `P` Void))
  (t `TT'T'I` State (T'I'II S Unit `T'TT'I` F'T'I'TT (T'II'I P) (T'I'II S Unit) `T'I_` e))
 ) => Mapping T'I'II T'I'II (AR) (AR)
  ((t `P'T'I'TT'I` T'I'II S Unit `T'TT'I` F'T'I'TT (T'II'I P) (T'I'II S Unit)) `L` (T'I'II S Unit `T'TT'I` F'T'I'TT (T'II'I P) (T'I'II S Unit)) `T` (Void))
  (T'I'II S Unit `T'TT'I` F'T'I'TT (T'II'I P) (T'I'II S Unit)) where
 mapping = rewrap `identity` \source (Label (T'TT'I'TTT'I (These x xx))) ->
  x `yokl_` Prior `ha` Apply `ha` State `ha___` Event `ha` Push `ho__'ha` Scope `har` within `ha` Fresh
   `bt'har___` xx `yi____` that `ho'yo` source

instance {-# OVERLAPS #-} Mapping T'I'II T'I'II (AR) (AR)
 ((Alone `P'T'I'TT'I` T'I'II S Unit `T'TT'I` F'T'I'TT (T'II'I P) (T'I'II S Unit)) `L` (F'T'I'TT (T'II'I P) (T'I'II S Unit)) `T` (Void))
 (F'T'I'TT (T'II'I P) (T'I'II S Unit)) where
 mapping = rewrap `identity` \source (Label (T'TT'I'TTT'I (These x xx))) ->
  Empty `ho___'ut` Only `ho'ut'st` x `ryo` Enter @(Nonempty List)
   `has___` supertype (Event `ha` Swap `ha` Exist `har'st` x `ha__` Scope `har` within `ha` Fresh) `ho` that
   `har___` basetype xx
   `yo____` source

-- TODO: `Prior` behaviour is needed here
{-
instance
 ( Covariant Endo Semi Functor (AR) t
 , forall e . Covariant Transformation Functor (AR) (AR) ((t `P'T'I'TT'I` Alone) `T'TT'I` State (List e) `L` State (List e) `T` (Void) `L` (t `P'T'I'TT'I` Alone) `T` (Void)) ((t `P'T'I'TT'I` Alone) `TT'T'I` State (List e))
 ) => Mapping T'I'II T'I'II (AR) (AR) ((t `P'T'I'TT'I` Alone) `L` List `T` (Void)) List where
 mapping = rewrap `identity` \source x -> supertype x `yokl` Forth `ha` Apply `ha` State `ha` Event `ha` push `ha` source `bt'har__` Null `ho'vt` Unit `ryo` Enter @List `yior` Unit
-}

-- instance
 -- ( Stackable tt
 -- ( Covariant Endo Semi Functor (->) tt
 -- , Covariant Yoneda Functor (->) (->) t
 -- , forall e . Mapping T'I'II T'I'II (->) (->) (t `T'TT'I` State (tt e) `L` State (tt e) `T` Void `L` t `T` (Void `P` Void)) (t `TT'T'I` State (tt e))
 -- ) => Mapping T'I'II T'I'II (AR) (AR) ((t `P'T'I'TT'I` tt) `L` tt `T` (Void `P` Void `P` Void)) tt where
 -- mapping = rewrap `identity` \source (Label (T'TT'I'TTT'I (These x xx))) ->
  -- x `yokl` Prior `ha` Apply `ha` State `ha` Event `ha` push
    -- `bt'har__` xx `yi__` that `ho'yo` source

pattern Aloft :: forall tt t i .
 -- Component (AR) ((t `P'T'I'TT'I` Tree) `L` Tree `T` (Void `P` Void)) Tree =>
 -- t `P'T'I'TT'I` Tree `T'I___` i `AR_____` (t `P'T'I'TT'I` Tree) `L` Tree `T` (Void `P` Void) `T` i
 t i `AR_____` t `L` tt `T` (Void `P` Void) `T` i
pattern Aloft x = Label x

-- instance Mapping T'I'II T'I'II (AR) (AR)
--  ((Alone `P'T'I'TT'I` Twice `T'TT'I` List `P'T'I'TT'I` Tree) `L` Tree `T` (Void `P` Void)) Tree where
--   mapping = rewrap `identity` \source (Label (T'TT'I'TTT'I (These scrolling_list tree))) ->
--    rewrap (\x -> Alone tree `hjd` that @(Twice `T'TT'I` List `T'I_` _) `ho'yo` (\x' -> x' `ryu` Enter @Tree) `hc` x) scrolling_list
--     `yi` Adapt @(Scrolling List) `ho` derive @(Nonempty List) `ho` Adapt @(Nonempty List) `ho` derive @List `ho'yo` supertype @(AR)
--     `yi` (\x' -> supertype scrolling_list `hjd` supertype (this @(Alone _) x'))
--     `yo` source

instance Mapping T'I'II T'I'II (AR) (AR)
 ((Alone `P'T'I'TT'I` Twice `T'TT'I` List `T'TT'I` Tree `P'T'I'TT'I` Tree) `L` Tree `T` (Void `P` Void)) Tree where
  mapping = rewrap `identity` \source (Label (T'TT'I'TTT'I (These (T'TT'I'TTT'I (These root siblings)) tree))) ->
   that `ha` sub @Tree
    `har__` Only `ho'ut'st` root `ryo` Enter @Tree
    `har__` Adapt @(Scrolling List) `ho` derive `ho` Adapt @(Nonempty List) `ho` derive
     `har_` Alone tree `hjd'tb` supertype siblings
    `yo___` source

-- TODO: We haven't finished yet!
-- TODO: I need to heavily test it...
-- instance Mapping T'I'II T'I'II (AR) (AR)
--  ((Alone `P'T'I'TT'I` Twice `T'TT'I` List) `T'TT'I` Tree `P'T'I'TT'I` Unfoldings Alone Tree) (List `T'TT'I` Tree) where
--  mapping = rewrap `identity` \source (T'TT'I'TTT'I (These basement unfoldings)) ->
--   let result = derive @List `ha` derive @(Nonempty List) `hc'st` basement in
--   Empty `hu` subtype result
--   -- `la______` (\x -> x `yokl` Forth `ha` Apply `ha` State `ha` Event `ha` worker `har__` result `yi__` that `ho` subtype @(AR))
--   `la______` proceed result
--   `har______` unfoldings `yo_______` source where

--    topping unfolding forest = Unit `hjd_____` forest
   
--    starting :: (Alone `P'T'I'TT'I` Twice `T'TT'I` List `T'TT'I` Tree) i `AR_______` List (Tree i) `AR_____` Tree i
--    starting (T'TT'I'TTT'I (These (Identity focused) (T'TT'I (T'TT'I (T'I'I (These sx xs)))))) forest = that `ha` sub @Tree
--     `har_` intro @Tree `hc` focused `har_` sx `hjd` (forest `hjd` xs `yi` Merge @List @List `ho` derive @List) `yi` derive @List @(Twice `T'TT'I` List) @(Tree _)

   -- proceed forest nonempty_list =
   --  let (These x xx) = this `ha` top @(Nonempty List) `hop` this `ha` sub @(Nonempty List) `har` nonempty_list in
   --  xx `yokl` Forth `ha` Apply `ha` State `ha` Event `ha` topping `har__` starting x forest `yi__` that -- `ho` subtype @(

  -- supertype (supertype unfoldings)
  --  `yokl` Forth `ha` Apply `ha` State `ha` Event `ha` worker
  --  `har__` subtype @(AR) @(List `T'TT'I` Tree `T'I_` _) `ha` derive @List `ha` derive @(Nonempty List) `hc'st` basement
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
  T'TT'I (T'TT'I'TTT'I (These (x `yo` (`hjd'tb` This Unit) `ha` source) (xs `yo` (`hjd'tb` That Unit) `ha` source)))

-- pattern Reach  :: forall ttt t tt i .
 -- Component (AT) ((t `P'T'I'TT'I` tt) `L` ttt `T` (Void)) ttt =>
 -- t `P'T'I'TT'I` tt `T'I___` i `AR______` (t `P'T'I'TT'I` tt) `L` ttt `T` (Void) `T` i
 -- Component (AR) (t `L` tt `T` (Void)) tt =>
 -- Component (AT) (t `L` tt `T` (Void)) tt =>

-- pattern Reach  :: forall tt t i .
 -- t `T'I` i `AR______` t `L` tt `T` (Recursive) `T` i
-- pattern Reach x = Label x

-- instance {-# OVERLAPS #-} Component (AR) ((t `P'T'I'TT'I` tt) `L` t `T` (Recursive)) t where
 -- component (Label (T'TT'I'TTT'I (These x xx))) = x

-- instance {-# OVERLAPS #-} Component (AR) ((t `P'T'I'TT'I` tt) `L` tt `T` (Recursive)) tt where
 -- component (Label (T'TT'I'TTT'I (These x xx))) = xx

-- instance {-# OVERLAPS #-} Component (AT) ((t `P'T'I'TT'I` tt) `L` t `T` (Recursive)) t where
 -- component = T'I'TT'II'T'II'I `identity` \(Label (T'TT'I'TTT'I (These x xs))) -> x `hjd'tb` (`hjd'tb` xs)

-- instance {-# OVERLAPS #-} Component (AT) ((t `P'T'I'TT'I` tt) `L` tt `T` (Recursive)) tt where
 -- component = T'I'TT'II'T'II'I `identity` \(Label (T'TT'I'TTT'I (These x xs))) -> xs `hjd'tb` (x `hjd'tb`)

-- instance {-# OVERLAPS #-} Mapping T'I'II T'I'II (AT) (AT) (I `P'T'I'TT'I` Twice `T'TT'I` List)
--  ((I `P'T'I'TT'I` Twice `T'TT'I` List) `T'TT'I` Along (Unit `S` Unit) `L` Along (Unit `S` Unit) `T` Void) where
  
 -- component = T'I'TT'II'T'II'I `identity` \(Label (Label x)) ->
  -- supertype Empty `hjd` Label `ha` Label `ha` (Empty `hu` x `has` (\xx -> that (push xx x)))

instance {-# OVERLAPS #-} Mapping T'I'II T'I'II (AR) (AR) (Construction List `P'T'I'TT'I` List `T'TT'I` Unfolding I `T'I` Construction List)
 ((Construction List `P'T'I'TT'I` List `T'TT'I` Unfolding I `T'I` Construction List) `T'TT'I` Along (Unit `S` Unit) `L` Along (Unit `S` Unit) `T` Void) where
 mapping = rewrap `identity` \source (T'TT'I'TTT'I (These (F'T'I'TT (Recursive (T'TT'I (T'II'I (These xx x))))) xxx)) ->
  xx `yo` wrapped @(AR) @(F'T'I'TT Along _ _) (`yo` source `ho` (`hjd'tb` That Unit)) `hjd_'tb` source x `hjd'tb` This Unit `hjd_'tb` xxx `yo` source `ho` (`hjd'tb` That Unit)

pattern Frame :: forall i . i `AR__` I `L` Along (Unit `S` Unit) `T` (Void `P` Void) `T` i
pattern Frame x = Label (Alone x)

instance {-# OVERLAPS #-} Mapping T'I'II T'I'II (AR) (AR)
 (I `P'T'I'TT'I` Twice `T'TT'I` List) ((I `P'T'I'TT'I` Twice `T'TT'I` List) `T'TT'I` Along (Unit `S` Unit) `L` Along (Unit `S` Unit) `T` (Void `P` Void)) where
 mapping = rewrap `identity` \source (T'TT'I'TTT'I (These x xs)) ->
  x `yo` (`hjd'tb` That Unit) `ha` source `hjd_'tb` xs `yo` (`hjd'tb` This Unit) `ha` source

instance {-# OVERLAPS #-} Mapping T'I'II T'I'II (AR) (AR) (Construction List `P'T'I'TT'I` List `T'TT'I` Unfolding I `T'I` Construction List)
 ((Construction List `P'T'I'TT'I` List `T'TT'I` Unfolding I `T'I` Construction List) `T'TT'I` Along (Unit `S` Unit) `L` Along (Unit `S` Unit) `T` (Void `P` Void)) where
 mapping = rewrap `identity` \source (T'TT'I'TTT'I (These (F'T'I'TT (Recursive (T'TT'I (T'II'I (These xx x))))) xxx)) ->
  xx `yo` wrapped @(AR) @(F'T'I'TT Along _ _) (`yo` source `ho` (`hjd'tb` This Unit)) `hjd_'tb` source x `hjd'tb` That Unit `hjd_'tb` xxx `yo` source `ho` (`hjd'tb` This Unit)

instance
 ( Covariant Endo Semi Functor (->) t
 ) => Mapping T'I'II T'I'II (AR) (AR) (Construction t) (Construction t `T'TT'I` Construction t `L` Construction t `T` Void) where
 mapping = rewrap `identity` \source -> rewrap `ha` rewrap `ha` rewrap `ha` rewrap `identity` \(These xx x) ->
  (xx `yo` supertype @AR `ha` supertype @AR `ha` (map @T'I'II @T'I'II @(AR) @(AR) @(Construction t) @(Construction t `T'TT'I` Construction t `L` Construction t `T` Void) source) `ha` F'T'I'TT)
  `hjd'tb` Label (xx `hjd'tb` x `yo` source)

-- instance Mapping T'I'II T'I'II (AR) (AR)
--  ((Alone `P'T'I'TT'I` Twice `T'TT'I` List) `T'TT'I` Tree `P'T'I'TT'I` Unfoldings Alone Tree)
--  (((Alone `P'T'I'TT'I` Twice `T'TT'I` List) `T'TT'I` Tree `P'T'I'TT'I` Unfoldings Alone Tree) `T'TT'I` Along (Unit `S` Unit) `L` Along (Unit `S` Unit) `T` Void) where
--  mapping = rewrap `identity` \source -> rewrap `identity`
--   \(These (T'TT'I (T'TT'I'TTT'I (These (Identity (F'T'I'TT (Recursive (T'TT'I (T'II'I (These xx x)))))) xxx))) xxxx) ->
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
 mapping = rewrap `identity` \source (F'T'I'TT (Recursive (T'TT'I (T'II'I (These xs x))))) -> 
  xs `yo` wrapped @(AR) @(F'T'I'TT Along t _) (`yo` source `ho` (`hjd'tb` That Unit)) `hjd_'tb` source x `hjd'tb` This Unit

pattern Final :: forall i . i `AR__` I `L` Along (Unit `S` Unit) `T` (Void `P` Void) `T` i
pattern Final x = Label (Alone x)

instance
 ( Covariant Endo Transformation Functor (AR) (t `T'TT'I` Maybe `L` Maybe `T` Void `L` t `T` Void) (t `TT'T'I` Maybe)
 , Covariant Lax Monoidal Functor (AR) (AR) (P) S Void t
 , Covariant Lax Monoidal Functor (AR) (AR) (P) P Void t
 ) => Mapping T'I'II T'I'II (AR) (AR) (Construction t) (Construction t `T'TT'I` Along (Unit `S` Unit) `L` Along (Unit `S` Unit) `T` (Void `P` Void)) where
 mapping = rewrap `identity` \source x -> T'TT'I `har__` x
  `kyo` Level @(Construction t) `ha` (\xx -> Label `ha` Along
   `ha` (is `ho'ut` (source `ha` this `ha` top `har` xx `hjd` That Unit) `bt'has` is `ho'ut` (source `ha` this `ha` top `har` xx `hjd` This Unit))
   `ha` (\xxx -> this `ha` sub `har` xxx `hjd'ys` (Pass `ryo` Apply @t) `yokl` Apply `ha` Check `ha__` Error `ho'ut` Error Unit `bt'has` Valid)
   `har` xx)

pattern Depth :: forall i . i `AR__` I `L` Along (List Unit) `T` Void `T` i
pattern Depth x = Label (Alone x)

instance
 ( Covariant Endo Transformation Functor (AR) (t `T'TT'I` Maybe `L` Maybe `T` Void `L` t `T` Void) (t `TT'T'I` Maybe)
 , Covariant Lax Monoidal Functor (AR) (AR) (P) S Void t
 , Covariant Lax Monoidal Functor (AR) (AR) (P) P Void t
 ) => Mapping T'I'II T'I'II (AR) (AR) (Construction t) (Construction t `T'TT'I` Along (List Unit) `L` Along (List Unit) `T` Void) where
 mapping = rewrap `identity` \source -> T'TT'I `compose` rewrap @AR (worker `har` source `har_` (T'TT'I `har'st` Empty)) where

  worker source depth = (rewrap @AR `ha` rewrap @AR `ha` rewrap @AR) `har`
   (\xx -> xx
    `yoi` fo @AR @AR (worker source (that (Event `har` Push Unit `ha__` Scope `har` within `ha` Fresh `bt'har_` depth)))
    `yio` (\xxx -> source xxx `hjd'tb` depth)
   )


-- TODO: Move all `Forth` instances to here
instance Component (AR) ((Twice `T'TT'I` List) `L` List `T` (Void)) List where
 component (Label (T'TT'I (T'I'I (These x xx)))) = xx

instance Component (AR) ((Twice `T'TT'I` List) `L` List `T` (Void `P` Void)) List where
 component (Label (T'TT'I (T'I'I (These x xx)))) = x

instance Component (AT) ((Twice `T'TT'I` List) `L` List `T` (Void)) List where
 component = T'I'TT'II'T'II'I `identity` \(Label (T'TT'I (T'I'I (These x xx)))) -> xx `hjd` (\xx' -> x `hjd'tb` xx')

instance Component (AT) ((Twice `T'TT'I` List) `L` List `T` (Void `P` Void)) List where
 component = T'I'TT'II'T'II'I `identity` \(Label (T'TT'I (T'I'I (These x xx)))) -> xx `hjd` (\x' -> x' `hjd'tb` xx)

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
 mapping = rewrap `identity` \source -> rewrap `identity` (source `ha` that `hop` source `ha` this `ha__` supertype @(AR))

instance Mapping T'I'II T'I'II (AR) (AR) (T'I'I (S) `L` T'I'I (S) `T` Void) (T'I'I (S)) where
 mapping = rewrap `identity` \source -> rewrap `identity` (source `ho` That `has` source `ho` This `ha__` supertype @(AR))

pattern Aback x = This x :: Shifter List
pattern Ahead x = That x :: Shifter List

pattern Above x = This x :: Shifter List
pattern Below x = That x :: Shifter List

pattern Forth :: forall tt t i . t i `AR____` t `L` tt `T` (Void) `T` i
pattern Forth x = Label @_ @_ @Void x

instance {-# OVERLAPS #-} Component (AT) ((Twice `T'TT'I` t) `L` t `T` (Void)) t where
 component = T'I'TT'II'T'II'I `identity` \(Label (T'TT'I (T'I'I (These x xx)))) -> xx `hjd'tb` (x `hjd'tb`)

pattern Prior :: forall tt t i . t i `AR____` t `L` tt `T` (Void `P` Void) `T` i
pattern Prior x = Label @_ @_ @(Void `P` Void) x

instance {-# OVERLAPS #-} Component (AT) ((Twice `T'TT'I` t) `L` t `T` (Void `P` Void)) t where
 component = T'I'TT'II'T'II'I `identity` \(Label (T'TT'I (T'I'I (These x xx)))) -> x `hjd'tb` (xx `hjd'tb`)

-- instance Component (TR) (t `P'T'I'TT'I` Twice `T'TT'I` List) Maybe where
 -- component = T'I'TT'II'I `identity` \case

instance Shiftable Alone (Maybe `T'TT'I` Construction Maybe) where
 shift :: forall i . Shifter List `AR___` Supertype (Event `T'I` Shifting Alone List i `T'I` Maybe (Alone i))
 shift way x = is `har` Empty `ho'ut` (Empty Unit `hjd` x) `bt'has_` is `ho'st` foi @_ @(AR) Exist `har_` _shift_ `bt'har` x where

  _shift_ = Pass `ryo` Enter @(Halts `JNT` State `T` Scrolling List i)
   `yok____'ut` Apply `ha__` State
   `har____` Event `ha__` Swap `har_'st` Empty
    `ha____` Scope `har_` field @(Shafted List i)
   `ho___'st` Scope `har_` index @Twice `ha` (Back `has` Fore) `har` way
     `ho___` Scope `har_` within `ha` Stock @Maybe
   `yok____` Check
   `yok____` Apply `ha__` State
   `ha_____` Event `ha__` Swap `ha` Alone
   `ho___'ha` Scope `har_` field @(Alone i)
   `yok____` Apply `ha__` State
   `ha_____` Event `ha__` Swap `ha'st` Exist
   `ho___'ha` Scope `har_` field @(Shafted List i)
    `ho__'st` Scope `ha_` index `ha` (Fore `has` Back) `har` way
      `ho_` (Scope `har` within @List @Maybe `ha` Fresh)
   -- TODO: there it is - if I use `Lease` label instead of `Apply` state doesn't change
   `yok____'ut` Apply `ha_` State
   `har____` Event `har` Pull
    `ha____` Scope `har` field @(Alone i)

 spot :: forall i . Shifter List `P` Match (Alone i) `AR_` Supertype (Event `T'I` Shifting Alone List i `T'I` Maybe `T` Shifting Alone List i)
 spot (These way predicate) x = foi Exist `ha` Pull `bt'has_` is `ho'st` foi @_ @(AR) (Empty `ho'ut'st` Empty) `har_` _spot_ `bt'har` x where

  found (These w sl) = supertype @(AR) @Boolean (predicate `yar` w) `yoo'ut` sl

  _spot_ = Pass `ryo` Enter @(Stops `T` Scrolling List i `JNT` State `T` Scrolling List i)
   `yok____'ut` Lease `ha` State `har___` Event `har__` Pull `ha___` Scope `har` field @(Alone i) `hop_` Scope `har` it
   `yok____` Check `ha` Stops `ha` not `ha` found
   `yok____'ut` Apply `ha` State `har___` Event `ha` shift `har` way
   `yok____` Retry `ha__` Break `ho'ut'st` Ok @Unit `bt'has` Again `ho'ut'st` Break @Unit

{-
instance Shiftable List (Maybe `T'TT'I` Construction Maybe) where
 shift :: forall i . Shifter List `AR___` Supertype (Event `T'I` Shifting List List i `T'I` Maybe (List i))
 shift way x = is
  `har_` is `ho'ut` (Empty Unit `hjd` x)
  `bt'has_` is `ho'st` foi @_ @(AR) Exist
  `har_` (is `ho'ut` slide_passed `has` is `ho'ut` slide_future `har` way) `bt'har` x where

  slide_future = Pass `ryo` Enter @(Halts `JNT` State `T` Sliding List i)
   `yok____'ut` Apply `ha` State `har__` Event `har` happen @List @Maybe `ha` First `ha__` Scope `har` field @(List _)
   `yok____` Check
   `yok____` Apply `ha` State `ha____` Event `ha` Push `ho___'ha` Scope `har` field @(Shafted List i) `ho__'st` Scope `ha` index `har'st` Aback `ho__` Scope `har` within `ha` Fresh
   `yok____'ut` Apply `ha` State `har___` Event `har` happen @List @Maybe `ha` First `ha___` Scope `har` field @(Shafted List i) `ho__'st` Scope `ha` index `har'st` Ahead
   `yok____` Check
   `yok____` Apply `ha` State `ha____` Event `ha` window_future `ho__'ha` Scope `har` field @(List _)

  slide_passed = Pass `ryo` Enter @(Halts `JNT` State `T` Sliding List _)
   `yok____'ut` Apply `ha` State `har___` Event `har` happen @List @Maybe `ha` First `ha___` Scope `har` field @(Shafted List i) `ho__'st` Scope `ha` index `har'st` Aback
   `yok____` Check
   `yok____` Apply `ha` State `ha____` Event `ha` window_extract_last `ho__'ha` Scope `har` field @(List _)
   `yok____` Check
   `yok____` Apply `ha` State `ha____` Event `ha` Push `ho___'ha` Scope `har` field @(Shafted List i) `ho__'st` Scope `ha` index `har'st` Ahead `ho__` Scope `har` within `ha` Fresh
   `yok____'ut` Apply `ha` State `har___` Event `har` Pull `ha__` Scope `har` field @(List _)

  window_future :: i `AR_____` List i `AR___` List i `P` List i
  window_future r w = is @(List _) w
   `yokl_` Prior `ha` Apply `ha` State `ha___` (Event `ha` Push) `ho__'ha` Scope `har` within @List @Maybe `ha` Fresh
   `bt'har___` Only `ho'ut'st` r `ryo` Enter @List

  window_extract_last passed w =
   -- Event `ha` Push `har` w `ha__` Scope `har` within `ha` Fresh
   push @List passed w `yi` that
    `yokl_` Prior `ha` Apply `ha` State `ha___` Event `ha` Push `ho__'ha` Scope `har` within @List @Maybe `ha` Fresh
    `bt'har___` Null `ho'vt` Unit `ryo` Enter @List
    `yi___` that `ho_` happen @List @Maybe `ha` First
-}

pattern Aside e = This e :: Shifter Tree
pattern Pitch e = That e :: Shifter Tree

instance Shiftable Alone (Construction List) where
 shift way x = is
  `har` is `ho'ut` (Empty Unit `hjd` x)
  `bt'has` is `ho'st` foi @_ @(AR) Exist
  `har_` (horizontally `has_` vertical_deep `has` vertical_up `har_` way) `bt'har` x where

  vertical_up :: forall i . Unit `AR___` (Halts `JNT` State `T` Scrolling Tree i) `T'I_` Alone i
  vertical_up _ = Pass `ryo` Enter @(Halts `JNT` State `T` Scrolling Tree i)
   `yok____'ut` Apply `ha_` State
   `har____` Event `har` happen `ha` First
    `ha____` Scope `har` field @(List `T'TT'I` (Alone `P'T'I'TT'I` Twice `T'TT'I` List `T'TT'I` Tree) `T'I_` i) `ho__'st` Scope `har` it
   `yok____` Check `ha_` is @(Maybe `T'I_` (Alone `P'T'I'TT'I` Twice `T'TT'I` List `T'TT'I` Tree) i)
   `yok____` Apply `ha_` State
   `ha_____` Event `ha_` aloft
   `ho___'ha` Scope `har` field @(Tree `T'I` i)

  aloft :: forall i . (Alone `P'T'I'TT'I` Twice `T'TT'I` List `T'TT'I` Tree) `T'I` i `AR____` Tree i `AR__` Alone i `P` Tree i
  aloft unfolding tree = Alone `ha` this `ha` top `har` tree
   `hjd_'tb` unfolding `hjd'tb` tree `yi` derive `ha` Aloft @Tree @(Alone `P'T'I'TT'I` Shafted List `T'TT'I` Tree `P'T'I'TT'I` Tree)

  vertical_deep :: forall i . Unit `AR___` (Halts `JNT` State `T` Scrolling Tree i) `T'I_` Alone i
  vertical_deep _ = Pass `ryo` Enter @(Halts `JNT` State `T` Scrolling Tree i)
   `yok_____'ut` Apply `ha_` State
    `har____` Event `har` Pull
     `ha____` Scope `har` field @(Tree `T'I` i)
      `ho___` Scope `har` top @Tree
        `hop_` Scope `har` sub @Tree
   `yok_____` Check `ha'yo` splash `ha` moves
   `yok_____` Apply `ha` State `ha____` Event `ha` Swap `ha` this
    `ho___'ha` Scope `har` field @(Tree i)
   `lo____'yp` Apply `ha_` State `ha____` Event `ha` Push `ha` that
    `ho___'ha` Scope `har` field @(List `T'TT'I` (Alone `P'T'I'TT'I` Twice `T'TT'I` List `T'TT'I` Tree) `T'I_` i)
     `ho__'st` Scope `har` it @(List `T'I_` (Alone `P'T'I'TT'I` Twice `T'TT'I` List `T'TT'I` Tree) i)
        `ho__` Scope `har` within `ha` Fresh
   `ho______'yo` Alone `ha` this `ha` top @Tree `ha` this

  moves :: forall i . i `P` List (Tree i) `AR___` Maybe (i `P` Nonempty List (Tree i))
  moves x = x `yiokl` Apply `ha` Check `ha` supertype @(AR)

  splash :: forall i . i `P` Nonempty List (Tree i) `AR____` Tree i `P` (Alone `P'T'I'TT'I` Twice `T'TT'I` List `T'TT'I` Tree) i
  splash (These root descendants) = this `ha` top `har` descendants
   `hjd__'tb` (Alone `har` root `hjd_'tb` subtype @(AR) `ha` (T'TT'I `ha` T'I'I `ha` These (Null `ho'vt` Unit `ryo` Enter @List)) `ha` subtype @(AR) @(List _) `ha` this `ha` sub `har` descendants)

  horizontally :: forall i . Shifter List `AR___` (Halts `JNT` State `T` Scrolling Tree i) `T'I_` Alone i
  horizontally way = Only `ryo` Enter @(Halts `JNT` State `T` Scrolling Tree i)
   `yok_____'ut` Apply `ha_` State
   -- `har_____` Event `har` pop
   `har_____` Event `har` happen @List @Maybe `ha` First
    `ha_____` Scope `har` field @(List `T'TT'I` (Alone `P'T'I'TT'I` Twice `T'TT'I` List `T'TT'I` Tree) `T'I_` i)
    `ho___'st` Scope `har` it @(List `T'I_` (Alone `P'T'I'TT'I` Twice `T'TT'I` List `T'TT'I` Tree) i)
   `yok_____` Check
   `yok_____` Apply `ha_` State
     `ha____` Event `ha_` (\unfolding tree -> scroll `har` way `har` unfolding `har` tree `hjd` tree)
    `ho___'ha` Scope `har` field @(Tree i)
   `yok_____` Apply `ha_` State `ha____` Event `ha` Swap `ha` this
    `ho___'ha` Scope `har` field @(Tree i)
   `lo____'yp` Apply `ha_` State `ha____` Event `ha` Push `ha` that
    `ho___'ha` Scope `har` field @(List `T'TT'I` (Alone `P'T'I'TT'I` Twice `T'TT'I` List `T'TT'I` Tree) `T'I_` i)
     `ho__'st` Scope `har` it @(List `T'I_` (Alone `P'T'I'TT'I` Twice `T'TT'I` List `T'TT'I` Tree) i)
        `ho__` Scope `har` within `ha` Fresh
   `ho______'yo` Alone `ha` this `ha` top @Tree `ha` this

  -- TODO: the problem here is that we ignore information about successfulness of horizontal shifting!
  scroll :: forall i . Shifter List
   `AR_____` (Alone `P'T'I'TT'I` Twice `T'TT'I` List `T'TT'I` Tree) `T'I` i
   `AR____` Tree i
   `AR___` Tree i `P` (Alone `P'T'I'TT'I` Twice `T'TT'I` List `T'TT'I` Tree `T'I___` i)
  scroll way unfolding tree =
   let siblings = this `ha` field @(Twice `T'TT'I` List `T'TT'I` Tree `T'I_` i) `ho'st` is `har` unfolding in
   Alone `har` tree `hjd'tb` siblings
   `yi_` shift `har` way `ha_` is @(Scrolling List `T'I` Tree i)
   `yi_` (\x -> supertype @(AR) `ha` this `ha` field @(Alone `T'I` Tree i) `har` x `hjd__'tb` this `ha` field @(Alone i) `har` unfolding `hjd_'tb` subtype @(AR) @(T'TT'I _ _ _) `ha` this `ha` field @(Twice `T'TT'I` List `T'I_` Tree i) `har` x) `ha` that

pattern Plane :: t i -> t `L` t `T` Void `T` i
pattern Plane i = Label i

pattern Whirl :: t i -> t `L` t `T` (Void `P` Void) `T` i
pattern Whirl i = Label i

pattern Align :: t i -> t `L` t `T` Void `T` i
pattern Align i = Label i

pattern Cross :: t i -> t `L` t `T` (Void `P` Void) `T` i
pattern Cross i = Label i
