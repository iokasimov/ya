{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE UndecidableSuperClasses #-}
module Ya.Algebra.Definition where

import Ya.Algebra.Abstract

infixl 9 `P`, `S`, `M`
infixl 8 `P_`, `S_`, `M_`
infixl 7 `P__`, `S__`, `M__`

infixl 8 `AR`, `AT`
infixl 7 `AR_`, `AT_`
infixl 6 `AR__`, `AT__`
infixl 5 `AR___`, `AT___`
infixl 4 `AR____`, `AT____`
infixl 3 `AR_____`, `AT_____`
infixl 2 `AR______`, `AT______`
infixl 1 `AR_______`, `AT_______`

infixl 3 `P'T'I'TT'I`
infixl 3 `S'T'I'TT'I`

infixl 0 /

type AR = (->)
type AR_ = (AR)
type AR__ = (AR)
type AR___ = (AR)
type AR____ = (AR)
type AR_____ = (AR)
type AR______ = (AR)
type AR_______ = (AR)

type (AT) = U_I_UU_II_T'II'I (AR) P
type AT_ = U_I_UU_II_T'II'I (AR) P
type AT__ = U_I_UU_II_T'II'I (AR) P
type AT___ = U_I_UU_II_T'II'I (AR) P
type AT____ = U_I_UU_II_T'II'I (AR) P
type AT_____ = U_I_UU_II_T'II'I (AR) P
type AT______ = U_I_UU_II_T'II'I (AR) P
type AT_______ = U_I_UU_II_T'II'I (AR) P

class Dumb x
instance Dumb x

class Mapping v vv from into t tt where
 mapping :: v from a o -> vv into (t a) (tt o)

instance Mapping T'I'II T'I'II from into t tt => Mapping T'II'I T'II'I from into tt t
 where mapping (T'II'I from) = T'II'I (map @T'I'II @T'I'II @from @into @t @tt from)

instance Mapping T'II'I T'I'II from into t tt => Mapping T'I'II T'II'I from into tt t
 where mapping (T'I'II from) = T'II'I (map @T'II'I @T'I'II @from @into @t @tt from)

map :: forall v vv from into t tt a o .
 Mapping v vv from into t tt =>
 Elicitable T'II'I Arrow (v from a o) =>
 Elicitable T'I'II Arrow (vv into (t a) (tt o)) =>
 Supertype (v from a o) -> Supertype (vv into (t a) (tt o))
map from = unwrap @Arrow (mapping @v @vv @from @into @t @tt @a @o (wrap from))

class Component into t tt where
 component :: into (t i) (tt i)

instance {-# OVERLAPPABLE #-} (Category into, Mapping T'I'II T'I'II into into t tt) => Component into t tt where
 component = map @T'I'II @T'I'II @into @into identity

{- [LAW] Associativity: compose f (compose g) ≡ compose (compose f g) -}
class
 ( forall e . Mapping T'I'II T'I'II from Arrow (T'I'II from e) (T'I'II from e)
 , forall e . Mapping T'II'I T'I'II from Arrow (T'II'I from e) (T'II'I from e)
 ) => Precategory from where
 compose :: from a o -> from e a -> from e o
 compose post pre = let T'I'II y = map @T'I'II @T'I'II post (T'I'II pre) in y

deriving instance
 ( forall e . Mapping T'I'II T'I'II from Arrow (T'I'II from e) (T'I'II from e)
 , forall e . Mapping T'II'I T'I'II from Arrow (T'II'I from e) (T'II'I from e)
 ) => Precategory from

{- [LAW] Left identity: identity . f ≡ f -}
{- [LAW] Right identity: f . identity ≡ f -}
class Precategory from => Category from
 where identity :: from a a

{- [LAW] I preserving: mapping identity ≡ identity -}
{- [LAW] Composition preserving: mapping (f . g) ≡ mapping f . mapping g -}
class (Category from, Category into, Mapping v T'I'II from into t t) => Functor v from into t
deriving instance (Category from, Category into, Mapping v T'I'II from into t t) => Functor v from into t

{- [LAW] Composition preserving: mapping (f . g) ≡ mapping f . mapping g -}

class
 ( Precategory from, Precategory into
 , Mapping v T'I'II from into t t
 , Dumb (x v from into t)
 ) => Semi v x from into t

deriving instance
 ( Precategory from, Precategory into
 , Mapping v T'I'II from into t t
 , Dumb (Functor v from into t)
 ) => Semi v Functor from into t

-- TODO: Semi Transformation?
-- TODO: Semi Monoidal Functor?
-- TODO: Semi Covariant/Contravariant Transformation?

type Endo v x c into = x v c into into

{- LAW: mapping @tt @tt morphism . component @t @tt ≡ component @t @tt . mapping morphism @t @t -}
{- LAW: mapping @tt @tt morphism . component @t @tt ≡ component @t @tt . mapping morphism @t @t -}
class
 ( Mapping v T'I'II from into t tt
 , x v from into t
 , x v from into tt
 ) => Transformation v x from into t tt

deriving instance
 ( Mapping v T'I'II from into t tt
 , x v from into t
 , x v from into tt
 ) => Transformation v x from into t tt

type Dinatural = T'II'I

type Covariant t = t T'I'II

type Contravariant t = t T'II'I

type Constant t = t U_1_I

type Kleisli u t = U_I_T_II t u

class (Category from, x v from into t, forall o . Mapping v T'I'II from Arrow t (UU_V_T'I'II_T_II v from into t o)) =>
 Yoneda v x from into t where
 yoneda :: forall a o .
  Category from =>
  Precategory into =>
  (Supertype (v from a a) ~ from a a) =>
  Elicitable T'II'I (AR) (v from a a) =>
  t a -> into (v from a o) (t o)
 yoneda x = unwrap (map @v @T'I'II @from @Arrow @t @(UU_V_T'I'II_T_II v from into t o) identity x)

deriving instance
 (Category from, x v from into t, forall r . Mapping v T'I'II from Arrow t (UU_V_T'I'II_T_II v from into t r)) =>
 Yoneda v x from into t

type family Representation t where
 Representation I = ()
 Representation (T'I'II Arrow a) = a
 Representation (T'TT'I t tt) =
  Representation t `P` Representation tt
 Representation (T'TTT'TT'I t ttt tt) =
  Representation t `P` Representation tt `P` Representation ttt
 Representation (T'I'I (P)) = () `S` ()

class
  ( Mapping v T'I'II from into t (v hom (Representation t))
  , Mapping v T'I'II from into (v hom (Representation t)) t
  ) => Representable hom v from into t

deriving instance
 ( Mapping v T'I'II from into t (v hom (Representation t))
 , Mapping v T'I'II from into (v hom (Representation t)) t
 ) => Representable hom v from into t

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

type family (M) r a where
 (M) ((_ # a) `S` aa) a = aa
 (M) (aa `S` (_ # a)) a = aa
 (M) (aa `S` aaa) a = aa `M` a `S` aaa

type M_ a aa = (M) a aa
type M__ a aa = (M) a aa

type family Neutral p where
 Neutral (P) = Unit
 Neutral (S) = Void
 Neutral (SP) = Void

type family Aught p where
 Aught T'I'II = Unit
 Aught T'II'I = Void

class
 ( forall e . Mapping v v from into (T'II'I u e) I
 , forall e . Mapping v v from into (T'I'II u e) I
 ) => Cone v from into u

deriving instance
 ( forall e . Mapping v v from into (T'II'I u e) I
 , forall e . Mapping v v from into (T'I'II u e) I
 ) => Cone v from into u

left :: forall v from into a o e .
 Cone v from into (Object (Aught v)) =>
 Elicitable T'II'I Arrow (v from a o) =>
 Elicitable T'I'II Arrow (v into ((T'II'I (Object (Aught v))) e a) (I o)) =>
 Supertype (v from a o) -> Supertype (v into (T'II'I (Object (Aught v)) e a) (I o))
left from = map @v @v @from @into @(T'II'I (Object (Aught v)) e) @I @a @o from

right :: forall v from into a o e .
 Cone v from into (Object (Aught v)) =>
 Elicitable T'II'I Arrow (v from a o) =>
 Elicitable T'I'II Arrow (v into (T'I'II (Object (Aught v)) e a) (I o)) =>
 Supertype (v from a o) -> Supertype (v into (T'I'II (Object (Aught v)) e a) (I o))
right from = map @v @v @from @into @(T'I'II (Object (Aught v)) e) @I @a @o from

type Limit v from into =
 ( Cone v from into (Object (Aught v))
 , Mapping v v from into I (Both (Object (Aught v)))
 )

type Product = Object Unit

type Sum = Object Void

-- TODO: maybe we can unify `Initial`/`Terminal` typeclasses into one `Morphism`?

class Initial into where
 initial' :: into Void e

instance Initial (AR) where
 initial' x = case x of {}

class Terminal into where
 terminal :: into e ()

instance Terminal (AR) where
 terminal _ = ()

type Day = U_V_UU_UUU_UUUU_T'TT'I_II_III P

class
 ( Covariant x into from t
 , Covariant x from into tt
 , Covariant Transformation x into from (T'TT'I t tt) I
 , Covariant Transformation x from into I (T'TT'I tt t)
 ) => Adjoint x from into t tt

deriving instance
 ( Covariant Functor into from t
 , Covariant Functor from into tt
 , Covariant Transformation Functor into from (T'TT'I t tt) I
 , Covariant Transformation Functor from into I (T'TT'I tt t)
 ) => Adjoint Functor from into t tt

class
 ( forall e ee . Mapping v vv from into (Day v from u uu t (l `L` t) e ee) t
 , Mapping v vv from into (v into (Neutral uu)) t
 , x v from into t
 ) => Monoidal v vv x from into u uu l t where

deriving instance
 ( forall e ee . Mapping v vv from into (Day v from u uu t (l `L` t) e ee) t
 , Mapping v vv from into (v into (Neutral uu)) t
 , x v from into t
 ) => Monoidal v vv x from into u uu l t

class x v T'I'II xx from into u uu l t
 => Lax v x xx from into u uu l t where

deriving instance Monoidal v T'I'II Functor from into u uu l t
 => Lax v Monoidal Functor from into u uu l t

class x v T'II'I xx from into u uu l t
 => Oplax v x xx from into u uu l t where

deriving instance Monoidal v T'II'I Functor from into u uu l t
 => Oplax v Monoidal Functor from into u uu l t

-- TODO: Yoneda version?
day :: forall v from l t tt u uu a o e ee .
 Mapping v T'I'II from (AR) (Day v from u uu t (l `L` tt) e ee) t =>
 Wrapper (AR) (v from a o) =>
 Wrapper (AR) (v from (uu e ee) a) =>
 Supertype (v from a o)
  -> Supertype (v from (uu e ee) a)
  -> u (t e) ((l `L` tt) ee) -> t o
day from t x = map @v @T'I'II @from @(AR)
 @(Day v from u uu t (l `L` tt) e ee) @t from
 (wrap (These x (wrap @_ @(v from (uu e ee) a) t)))

-- TODO: coday -- Oplax Monoidal Functor

-- TODO: generalize
empty :: forall t o . Covariant Lax Monoidal Functor (AR) (AR) (P) (S) Void t => t o
empty = component @(AR) @(T'I'II (AR) Void) @t (T'I'II initial')

intro :: forall t into e .
 Category into =>
 Covariant Lax Monoidal Functor (AR) (AR) (P) P Void t =>
 Mapping T'I'II T'I'II into into (T'I'II AR Unit) t =>
 Component into I (T'I'II (AR) Unit) =>
 Wrapper into (T'I'II AR Unit e) =>
 Wrapper into (I e) =>
 into `T'I` e `T'I` t e
intro = component @into @(T'I'II (AR) Unit) @t `compose` wrap `compose` constant @(AR) @into

outro :: forall t into e .
 Category into =>
 Covariant Oplax Monoidal Functor (AR) (AR) (P) P Void t =>
 Mapping T'I'II T'I'II into into t (T'I'II AR Unit) =>
 Component into I (T'I'II (AR) Unit) =>
 Wrapper into (T'I'II AR Unit e) =>
 Wrapper into (AR Unit e) =>
 Wrapper into (I e) =>
 into `T'I` t e `T'I` e
outro = unwrap `compose` unwrap `compose` component @into @t @(T'I'II (AR) Unit)

rewrap :: forall o into a .
 Precategory into =>
 Elicitable T'II'I into o =>
 Elicitable T'I'II into a =>
 into (Supertype a) (Supertype o) -> into a o
rewrap f = wrap `compose` f `compose` unwrap

wrapped :: forall into a o .
 Precategory into =>
 Elicitable T'I'II into o =>
 Elicitable T'II'I into a =>
 into a o -> into (Supertype a) (Supertype o)
wrapped f = unwrap `compose` f `compose` wrap

i_ :: forall into u a o e .
 Precategory into =>
 Elicitable T'II'I into (T'II'I u e a) =>
 Elicitable T'I'II into (T'II'I u e o) =>
 into (T'II'I u e a) (T'II'I u e o) -> into (u a e) (u o e)
i_ f = unwrap @into @(T'II'I _ _ _) `compose` f `compose` wrap @into @(T'II'I _ _ _)

_i :: forall into u a o e .
 Precategory into =>
 Elicitable T'II'I into (T'I'II u e a) =>
 Elicitable T'I'II into (T'I'II u e o) =>
 into (T'I'II u e a) (T'I'II u e o) -> into (u e a) (u e o)
_i f = unwrap @into @(T'I'II _ _ _) `compose` f `compose` wrap @into @(T'I'II _ _ _)

cata :: forall into t e .
 Covariant Endo Semi Functor into t =>
 Elicitable T'I'II into (Recursive t) =>
 into (t e) e -> into (Recursive t) e
cata into = into `compose`
 map @T'I'II @T'I'II (cata into) `compose`
 (let T'I'II x = elicit in x)

ana :: forall into t e .
 Covariant Endo Semi Functor into t =>
 Elicitable T'II'I into (Recursive t) =>
 into e (t e) -> into e (Recursive t)
ana into = wrap `compose` map @T'I'II @T'I'II (ana into) `compose` into

this :: forall e ee . e `P` ee -> e
this (These x _) = x

that :: forall ee e . e `P` ee -> ee
that (These _ x) = x

swap :: e `P` ee `AR_` ee `P` e
swap (These x y) = These y x

constant :: forall from into a o .
 Category from =>
 Precategory into =>
 Component into I (T'I'II from a) =>
 Elicitable T'I'II into (T'I'II from a o) =>
 Elicitable T'II'I into (I o) =>
 into o (from a o)
constant = unwrap @_ @(T'I'II from a _)
 `compose` component @into
 `compose` wrap @into @(I o)

is :: Category AR_ => e `AR_` e
is = identity

type (SP) = U_T'I'II_UT'I'II (S) P

instance Wrapper (AR) x
 => Elicitable T'I'II (U_I_UU_II_T'II'I (AR) (P)) x where
 elicit = T'I'II (U_I_UU_II_T'II'I (\x -> These (unwrap x) wrap))

instance Wrapper (AR) x
 => Elicitable T'II'I (U_I_UU_II_T'II'I (AR) (P)) x where
 elicit = T'II'I (U_I_UU_II_T'II'I (\x -> These (wrap x) unwrap))

class Setoid into e where
 equality :: into (e `P` e) (e `P` e `S` e)

(/) :: (i -> o) -> i -> o
(/) f x = f x

type P'T'I'TT'I = U_T_I_TT_I (P)
type S'T'I'TT'I = U_T_I_TT_I (S)

class Objective into st t where
 objective :: into t st

instance {-# OVERLAPPABLE #-} (Category into, Wrapper into t, Objective into (e `S` ee) (Supertype t))
 => Objective into (e `S` ee) t where objective = objective @into `compose` unwrap @into

instance {-# OVERLAPPABLE #-} (Category into, Wrapper into t, Objective into (Supertype t) (e `P` ee))
 => Objective into t (e `P` ee) where objective = wrap @into `compose` objective @into

instance (e ~ eee, ee ~ eeee, Category into) => Objective into (e `S` ee) (eee `S` eeee) where
 objective = identity

instance (e ~ eee, ee ~ eeee, Category into) => Objective into (e `P` ee) (eee `P` eeee) where
 objective = identity

newtype U_I_UU_M_I_II_II u uu i ii = U_I_UU_M_I_II_II (u i (uu (M i ii) ii))

type instance Supertype (U_I_UU_M_I_II_II u uu i ii) = u i (uu (M i ii) ii)

instance Elicitable T'II'I (AR) (U_I_UU_M_I_II_II u uu i ii)
 where elicit = T'II'I U_I_UU_M_I_II_II

instance Elicitable T'I'II (AR) (U_I_UU_M_I_II_II u uu i ii)
 where elicit = T'I'II (\(U_I_UU_M_I_II_II x) -> x)
