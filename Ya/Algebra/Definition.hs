{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE UndecidableSuperClasses #-}
module Ya.Algebra.Definition where

import Ya.Algebra.Abstract

infixl 9 `P`, `S`, `M`
infixl 8 `P_`, `S_`, `M_`
infixl 7 `P__`, `S__`, `M__`
infixl 6 `S___`

infixl 8 `AR`, `AT`, `TR`, `C'AR`, `C'AT`, `C'TR`
infixl 7 `AR_`, `AT_`, `TR_`, `C'AR_`, `C'AT_`, `C'TR_`
infixl 6 `AR__`, `AT__`, `TR__`, `C'AR__`, `C'AT__`, `C'TR__`
infixl 5 `AR___`, `AT___`, `TR___`, `C'AR___`, `C'AT___`,`C'TR___`
infixl 4 `AR____`, `AT____`, `TR____`, `C'AR____`, `C'AT____`,`C'TR____`
infixl 3 `AR_____`, `AT_____`, `TR_____`, `C'AR_____`, `C'AT_____`,`C'TR_____`
infixl 2 `AR______`, `AT______`, `TR______`, `C'AR______`, `C'AT______`, `C'TR______`
infixl 1 `AR_______`, `AT_______`, `TR_______`, `C'AR_______`, `C'AT_______`,`C'TR_______`

infixl 5 `P'T'I'TT'I`
infixl 5 `S'T'I'TT'I`

type AR = (->)
type AR_ = (AR)
type AR__ = (AR)
type AR___ = (AR)
type AR____ = (AR)
type AR_____ = (AR)
type AR______ = (AR)
type AR_______ = (AR)

type AT = T'I'TT'II'T'II'I (AR) (P)
type AT_ = T'I'TT'II'T'II'I (AR) (P)
type AT__ = T'I'TT'II'T'II'I (AR) (P)
type AT___ = T'I'TT'II'T'II'I (AR) (P)
type AT____ = T'I'TT'II'T'II'I (AR) (P)
type AT_____ = T'I'TT'II'T'II'I (AR) (P)
type AT______ = T'I'TT'II'T'II'I (AR) (P)
type AT_______ = T'I'TT'II'T'II'I (AR) (P)

type TR = T'I'TT'II'I (AR) (P)
type TR_ = T'I'TT'II'I (AR) (P)
type TR__ = T'I'TT'II'I (AR) (P)
type TR___ = T'I'TT'II'I (AR) (P)
type TR____ = T'I'TT'II'I (AR) (P)
type TR_____ = T'I'TT'II'I (AR) (P)
type TR______ = T'I'TT'II'I (AR) (P)
type TR_______ = T'I'TT'II'I (AR) (P)

class Dumb x
instance Dumb x

class Mapping v vv source target t tt where
 mapping :: v source a o -> vv target (t a) (tt o)

instance Mapping T'I'II T'I'II source target t tt => Mapping T'II'I T'II'I source target tt t
 where mapping (T'II'I source) = T'II'I (map @T'I'II @T'I'II @source @target @t @tt source)

instance Mapping T'II'I T'I'II source target t tt => Mapping T'I'II T'II'I source target tt t
 where mapping (T'I'II source) = T'II'I (map @T'II'I @T'I'II @source @target @t @tt source)

map :: forall v vv source target t tt a o .
 Mapping v vv source target t tt =>
 Elicitable T'II'I Arrow (v source a o) =>
 Elicitable T'I'II Arrow (vv target (t a) (tt o)) =>
 Supertype (v source a o) -> Supertype (vv target (t a) (tt o))
map source = supertype @Arrow (mapping @v @vv @source @target @t @tt @a @o (subtype source))

class Component target t tt where
 component :: target (t i) (tt i)

type C'AR t tt = forall i . Component (AR) t tt => Unlabeled t i `AR` Unlabeled tt i

type C'AR_ t tt = C'AR t tt
type C'AR__ t tt = C'AR t tt
type C'AR___ t tt = C'AR t tt
type C'AR____ t tt = C'AR t tt
type C'AR_____ t tt = C'AR t tt
type C'AR______ t tt = C'AR t tt
type C'AR_______ t tt = C'AR t tt

type C'AT t tt = forall i . Component (AT) t tt => Unlabeled t i `AT` Unlabeled tt i

type C'AT_ t tt = C'AT t tt
type C'AT__ t tt = C'AT t tt
type C'AT___ t tt = C'AT t tt
type C'AT____ t tt = C'AT t tt
type C'AT_____ t tt = C'AT t tt
type C'AT______ t tt = C'AT t tt
type C'AT_______ t tt = C'AT t tt

type C'TR t tt = forall i . Component (TR) t tt => Unlabeled t i `TR` Unlabeled tt i

type C'TR_ t tt = C'TR t tt
type C'TR__ t tt = C'TR t tt
type C'TR___ t tt = C'TR t tt
type C'TR____ t tt = C'TR t tt
type C'TR_____ t tt = C'TR t tt
type C'TR______ t tt = C'TR t tt
type C'TR_______ t tt = C'TR t tt

instance {-# OVERLAPPABLE #-} (Category target, Mapping T'I'II T'I'II target target t tt) => Component target t tt where
 component = map @T'I'II @T'I'II @target @target identity

{- [LAW] Associativity: compose f (compose g) ≡ compose (compose f g) -}
class
 ( forall e . Mapping T'I'II T'I'II source Arrow (T'I'II source e) (T'I'II source e)
 , forall e . Mapping T'II'I T'I'II source Arrow (T'II'I source e) (T'II'I source e)
 ) => Precategory source where
 compose :: source a o -> source e a -> source e o
 compose post pre = let T'I'II y = map @T'I'II @T'I'II post (T'I'II pre) in y

deriving instance
 ( forall e . Mapping T'I'II T'I'II source Arrow (T'I'II source e) (T'I'II source e)
 , forall e . Mapping T'II'I T'I'II source Arrow (T'II'I source e) (T'II'I source e)
 ) => Precategory source

{- [LAW] Left identity: identity . f ≡ f -}
{- [LAW] Right identity: f . identity ≡ f -}
class Precategory source => Category source
 where identity :: source a a

{- [LAW] Identity preserving: mapping identity ≡ identity -}
{- [LAW] Composition preserving: mapping (f . g) ≡ mapping f . mapping g -}
class (Category source, Category target, Mapping v T'I'II source target t t) => Functor v source target t
deriving instance (Category source, Category target, Mapping v T'I'II source target t t) => Functor v source target t

{- [LAW] Composition preserving: mapping (f . g) ≡ mapping f . mapping g -}

class
 ( Precategory source, Precategory target
 , Mapping v T'I'II source target t t
 , Dumb (x v source target t)
 ) => Semi v x source target t

deriving instance
 ( Precategory source, Precategory target
 , Mapping v T'I'II source target t t
 , Dumb (Functor v source target t)
 ) => Semi v Functor source target t

-- TODO: Semi Transformation?
-- TODO: Semi Monoidal Functor?
-- TODO: Semi Covariant/Contravariant Transformation?

type Endo v x c target = x v c target target

{- LAW: mapping @tt @tt morphism . component @t @tt ≡ component @t @tt . mapping morphism @t @t -}
{- LAW: mapping @tt @tt morphism . component @t @tt ≡ component @t @tt . mapping morphism @t @t -}
class
 ( Mapping v T'I'II source target t tt
 , x v source target t
 , x v source target tt
 ) => Transformation v x source target t tt

deriving instance
 ( Mapping v T'I'II source target t tt
 , x v source target t
 , x v source target tt
 ) => Transformation v x source target t tt

type Dinatural = T'II'I

type Covariant t = t T'I'II

type Contravariant t = t T'II'I

type Constant t = t T''II

type Kleisli u t = T'I'TT'II u t

class 
 ( Category source
 , x v source target t
 , forall e . Mapping v T'I'II source target t (Embedding v source target t e)
 , forall e ee . Covariant Elicitable target (UU_V_T'I'II_T_II v source target t ee e)
 ) => Yoneda v x source target t where
 yoneda :: forall a o .
  Category source =>
  Precategory target =>
  (Supertype (v source a a) ~ source a a) =>
  Elicitable T'II'I (AR) (v source a a) =>
  target (t a) (target (v source a o) (t o))
 yoneda = supertype `compose` map @v @T'I'II @source @target @t @(Embedding v source target t o) identity

deriving instance
 ( Category source
 , x v source target t
 , forall e . Mapping v T'I'II source target t (Embedding v source target t e)
 , forall e ee . Covariant Elicitable target (UU_V_T'I'II_T_II v source target t ee e)
 ) => Yoneda v x source target t

type family Representation t where
 Representation I = Unit
 Representation (T'I'II AR a) = a
 Representation (T'TT'I t tt) = Representation t `P` Representation tt
 Representation (T'TTT'TT'I t ttt tt) = Representation t `P` Representation tt `P` Representation ttt
 Representation (T'I'I (P)) = Unit `S` Unit

class
  ( Mapping v T'I'II source target t (v source (Representation t))
  , Mapping v T'I'II source target (v source (Representation t)) t
  , Dumb (x v source target t)
  ) => Naperian v x source target t

deriving instance
 ( Mapping v T'I'II source target t (v source (Representation t))
 , Mapping v T'I'II source target (v source (Representation t)) t
 , Dumb (x v source target t)
 ) => Naperian v x source target t

type family Co x where Co (x T'I'II) = x T'II'I

data family Object o e ee
data instance Object Unit e ee = These e ee
data instance Object Void e ee = This e | That ee

type (P) = Object Unit

type P_ = P
type P__ = P

type (S) = Object Void

type S_ = (S)
type S__ = (S)

type family Minus r e where
 Minus (e `S` ee) e = ee
 Minus (ee `S` e) e = ee
 Minus (ee `S` eee) e = ee `M` e `S` eee
 Minus e e = Void

type M a aa = Minus a aa
type M_ a aa = Minus a aa
type M__ a aa = Minus a aa

type family Neutral p where
 Neutral (P) = Unit
 Neutral (S) = Void
 Neutral (W) = Void

type family Aught p where
 Aught T'I'II = Unit
 Aught T'II'I = Void

type P'I'II = T'I'II P
type P'II'I = T'II'I P

type S'I'II = T'I'II S
type S'II'I = T'II'I S

class
 ( forall e . Mapping v v source target (T'II'I u e) I
 , forall e . Mapping v v source target (T'I'II u e) I
 ) => Cone v source target u

deriving instance
 ( forall e . Mapping v v source target (T'II'I u e) I
 , forall e . Mapping v v source target (T'I'II u e) I
 ) => Cone v source target u

left :: forall v source target a o e .
 Cone v source target (Object (Aught v)) =>
 Elicitable T'II'I Arrow (v source a o) =>
 Elicitable T'I'II Arrow (v target ((T'II'I (Object (Aught v))) e a) (I o)) =>
 Supertype (v source a o) -> Supertype (v target (T'II'I (Object (Aught v)) e a) (I o))
left source = map @v @v @source @target @(T'II'I (Object (Aught v)) e) @I @a @o source

right :: forall v source target a o e .
 Cone v source target (Object (Aught v)) =>
 Elicitable T'II'I Arrow (v source a o) =>
 Elicitable T'I'II Arrow (v target (T'I'II (Object (Aught v)) e a) (I o)) =>
 Supertype (v source a o) -> Supertype (v target (T'I'II (Object (Aught v)) e a) (I o))
right source = map @v @v @source @target @(T'I'II (Object (Aught v)) e) @I @a @o source

type Limit v source target =
 ( Cone v source target (Object (Aught v))
 , Mapping v v source target I (Both (Object (Aught v)))
 )

type Product = Object Unit

type Sum = Object Void

-- TODO: maybe we can unify `Initial`/`Terminal` typeclasses target one `Morphism`?

class Initial target where
 initial :: target Void e

instance Initial (AR) where
 initial x = case x of {}

class Terminal target where
 terminal :: target i Unit

instance Terminal (AR) where
 terminal _ = Unit

instance Terminal (AT) where
 terminal = T'I'TT'II'T'II'I (\x -> These Unit (\_ -> x))

type Day = U_V_UU_UUU_UUUU_T'TT'I_II_III P

class
 ( Covariant x target source t
 , Covariant x source target tt
 , Covariant Transformation x target source (T'TT'I t tt) I
 , Covariant Transformation x source target I (T'TT'I tt t)
 ) => Adjoint x source target t tt | t -> tt

class
 ( forall e ee . Mapping v vv source target (Day v source u uu t (t `L` t `T` l) e ee) t
 , Mapping v vv source target (v target (Neutral uu)) t
 , x v source target t
 ) => Monoidal v vv x source target u uu l t where

deriving instance
 ( forall e ee . Mapping v vv source target (Day v source u uu t (t `L` t `T` l) e ee) t
 , Mapping v vv source target (v target (Neutral uu)) t
 , x v source target t
 ) => Monoidal v vv x source target u uu l t

class x v T'I'II xx source target u uu l t
 => Lax v x xx source target u uu l t where

deriving instance Monoidal v T'I'II Functor source target u uu l t
 => Lax v Monoidal Functor source target u uu l t

class x v T'II'I xx source target u uu l t
 => Oplax v x xx source target u uu l t where

deriving instance Monoidal v T'II'I Functor source target u uu l t
 => Oplax v Monoidal Functor source target u uu l t

-- TODO: Yoneda version?
day :: forall v source l t tt u uu a o e ee .
 Mapping v T'I'II source (AR) (Day v source u uu t (tt `L` tt `T` l) e ee) t =>
 Wrapper (AR) (v source a o) =>
 Wrapper (AR) (v source (uu e ee) a) =>
 Supertype (v source a o)
  -> Supertype (v source (uu e ee) a)
  -> u (t e) (tt `L` tt `T` l `T'I` ee) -> t o
day source t x = map @v @T'I'II @source @(AR)
 @(Day v source u uu t (tt `L` tt `T` l) e ee) @t source
 (subtype (These x (subtype @_ @(v source (uu e ee) a) t)))

instance Mapping T'I'II T'I'II (AR) (AR)
 (Day T'I'II (AR) u uu t (tt `L` tt `T` l) e ee)
 (Day T'I'II (AR) u uu t (tt `L` tt `T` l) e ee)

-- TODO: coday -- Oplax Monoidal Functor

-- TODO: generalize
empty :: forall t o . Covariant Lax Monoidal Functor (AR) (AR) (P) (S) Void t => t o
empty = component @(AR) @(T'I'II (AR) Void) @t (T'I'II initial)

outro :: forall t target e .
 Category target =>
 Component target t (T'I'II AR Unit) =>
 Wrapper target (T'I'II AR Unit e) =>
 Wrapper target (AR Unit e) =>
 target `T'I` t e `T'I` e
outro = supertype `compose` supertype `compose` component @target @t @(T'I'II (AR) Unit)

rewrap :: forall target a o .
 Precategory target =>
 Elicitable T'II'I target o =>
 Elicitable T'I'II target a =>
 target (Supertype a) (Supertype o) -> target a o
rewrap f = subtype `compose` f `compose` supertype

wrapped :: forall target a o .
 Precategory target =>
 Elicitable T'I'II target o =>
 Elicitable T'II'I target a =>
 target a o -> target (Supertype a) (Supertype o)
wrapped f = supertype `compose` f `compose` subtype

i_ :: forall target u a o e .
 Precategory target =>
 Elicitable T'II'I target (T'II'I u e a) =>
 Elicitable T'I'II target (T'II'I u e o) =>
 target (T'II'I u e a) (T'II'I u e o) -> target (u a e) (u o e)
i_ f = supertype @target @(T'II'I _ _ _) `compose` f `compose` subtype @target @(T'II'I _ _ _)

_i :: forall target u a o e .
 Precategory target =>
 Elicitable T'II'I target (T'I'II u e a) =>
 Elicitable T'I'II target (T'I'II u e o) =>
 target (T'I'II u e a) (T'I'II u e o) -> target (u e a) (u e o)
_i f = supertype @target @(T'I'II _ _ _) `compose` f `compose` subtype @target @(T'I'II _ _ _)

cata :: forall target t e .
 Covariant Endo Semi Functor target t =>
 Elicitable T'I'II target (Recursive t) =>
 target (t e) e -> target (Recursive t) e
cata target = target `compose`
 map @T'I'II @T'I'II (cata target) `compose`
 supertype

-- cata' :: forall target t e .
--  Covariant Endo Semi Functor target t =>
--  Elicitable T'I'II target (Recursive t) =>
--  target (t e) e -> target (Recursive t) e
-- cata' target = target `compose`
--  map @T'I'II @T'I'II (cata target) `compose`
--  (let T'I'II x = elicit in x)


ana :: forall target t e .
 Covariant Endo Semi Functor target t =>
 Elicitable T'II'I target (Recursive t) =>
 target e (t e) -> target e (Recursive t)
ana target = subtype `compose` map @T'I'II @T'I'II (ana target) `compose` target

this :: forall e ee . e `P` ee -> e
this (These x _) = x

that :: forall ee e . e `P` ee -> ee
that (These _ x) = x

constant :: forall source target a o .
 Category source =>
 Precategory target =>
 Component target I (T'I'II source a) =>
 Elicitable T'I'II target (T'I'II source a o) =>
 Elicitable T'II'I target (I o) =>
 target o (source a o)
constant = supertype @_ @(T'I'II source a _)
 `compose` component @target
 `compose` subtype @target @(I o)

is :: Category AR_ => e `AR_` e
is = identity

type Whether = U_T'I'II_UT'I'II Sum Product

type W = Whether

instance Wrapper (AR) x
 => Elicitable T'I'II (T'I'TT'II'T'II'I (AR) (P)) x where
 elicit = T'I'II (T'I'TT'II'T'II'I (\x -> These (supertype x) subtype))

instance Wrapper (AR) x
 => Elicitable T'II'I (T'I'TT'II'T'II'I (AR) (P)) x where
 elicit = T'II'I (T'I'TT'II'T'II'I (\x -> These (subtype x) supertype))

class Setoid target e where
 equality :: target (e `P` e) (e `P` e `S` e)

type P'T'I'TT'I = T'TT'I'TTT'I (P)

pattern LRT x xx = T'TT'I'TTT'I (These x xx)

type S'T'I'TT'I = T'TT'I'TTT'I (S)

pattern LT x = T'TT'I'TTT'I (This x)
pattern RT x = T'TT'I'TTT'I (That x)

pattern Clasp :: forall t tt ttt i . t (tt i) (ttt i) `AR___` T'TT'I'TTT'I t tt ttt i
pattern Clasp x = T'TT'I'TTT'I x

type family Basetype x where
 Basetype (i `P` ii) = i `P` ii
 Basetype (i `S` ii) = i `S` ii
 Basetype (i `AR` ii) = i `AR` ii
 Basetype i = Basetype (Supertype i)

class Objective v target a o where
 objective :: Supertype (v target a o)

instance {-# OVERLAPPABLE #-} (Category target, Wrapper target a, Objective T'I'II target (Supertype a) o)
 => Objective T'I'II target a o where objective = objective @T'I'II @target `compose` supertype @target

instance {-# OVERLAPPABLE #-} (Category target, Wrapper target a, Objective T'II'I target (Supertype a) o)
 => Objective T'II'I target a o where objective = subtype @target `compose` objective @T'II'I @target

instance (e ~ eee, ee ~ eeee, Category target) => Objective T'I'II target (e `S` ee) (eee `S` eeee) where
 objective = identity

instance (e ~ eee, ee ~ eeee, Category target) => Objective T'I'II target (e `P` ee) (eee `P` eeee) where
 objective = identity

instance (e ~ eee, ee ~ eeee, Category target) => Objective T'II'I target (e `S` ee) (eee `S` eeee) where
 objective = identity

instance (e ~ eee, ee ~ eeee, Category target) => Objective T'II'I target (e `P` ee) (eee `P` eeee) where
 objective = identity

instance (e ~ eee, ee ~ eeee, Category target) => Objective T'I'II target (e `AR` ee) (eee `AR` eeee) where
 objective = identity

instance (e ~ eee, ee ~ eeee, Category target) => Objective T'II'I target (e `AR` ee) (eee `AR` eeee) where
 objective = identity

supertype :: forall target i .
 Covariant Elicitable target i =>
 target i (Supertype i)
supertype = let T'I'II x = elicit in x

subtype :: forall target i .
 Elicitable T'II'I target i =>
 target (Supertype i) i
subtype = let T'II'I x = elicit in x

basetype :: forall target i .
 Covariant Objective target i (Basetype i) =>
 target i (Basetype i)
basetype = objective @T'I'II @target

bound :: forall target i .
 Contravariant Objective target i (Basetype i) =>
 target (Basetype i) i
bound = objective @T'II'I @target

-- TODO: generalize, move to `Abstract` module
newtype U_I_UU_M_I_II_II u uu i ii = U_I_UU_M_I_II_II (u i (uu (M i ii) ii))

type instance Supertype (U_I_UU_M_I_II_II u uu i ii) = u i (uu (M i ii) ii)

instance Elicitable T'II'I (AR) (U_I_UU_M_I_II_II u uu i ii)
 where elicit = T'II'I U_I_UU_M_I_II_II

instance Elicitable T'I'II (AR) (U_I_UU_M_I_II_II u uu i ii)
 where elicit = T'I'II (\(U_I_UU_M_I_II_II x) -> x)

type Flout = T'I'

pattern Flout x = T'I' x

type Twice = Both (P)

pattern Twice :: i `P` i `AR___` T'I'I P i
pattern Twice x = T'I'I x

type Opted = Both (S)

pattern Opted :: i `S` i `AR___` T'I'I S i
pattern Opted x = T'I'I x

-- TODO: these typeclasses are experimental
class Semigroup source e where s :: e `P` e `source` e
class Quasigroup source e where p :: e `P` e `source` e

type family Unlabeled t where
 Unlabeled (t `L` tt `T` l) = Unlabeled t
 Unlabeled t = t

class Unlabelable target t where
 unlabel :: target (t i) (Unlabeled t i)

instance {-# OVERLAPPABLE #-}
 ( Precategory target
 , forall i . Wrapper target (t `L` tt `T` l `T` i)
 , Unlabeled (t `L` tt `T` l) ~ t
 ) => Unlabelable target (t `L` tt `T` l) where
 unlabel = supertype @target

instance {-# OVERLAPPABLE #-}
 ( Precategory target
 , forall i . Wrapper target (t `L` tt `T` l `T` i)
 , forall i . Wrapper target (t `L` tt `T` l `L` ttt `T` ll `T` i)
 , Unlabeled (t `L` tt `T` l `L` ttt `T` ll) ~ t
 ) => Unlabelable target (t `L` tt `T` l `L` ttt `T` ll) where
 unlabel = supertype @target `compose` supertype @target

pattern Enter :: forall t i . t i `AR_` t i
pattern Enter x = x

pattern Null :: Void `AR_` Void
pattern Null x = x

pattern Only :: Unit `AR_` Unit
pattern Only x = x
