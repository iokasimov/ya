{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE UndecidableSuperClasses #-}
module Ya.Algebra.Definition where

import Ya.Algebra.Abstract

infixl 9 `P`, `S`, `M`
infixl 8 `P_`, `S_`, `M_`
infixl 7 `P__`, `S__`, `M__`

infixl 8 `AR`, `AT`, `C'AR`, `C'AT`, `AL`
infixl 7 `AR_`, `AT_`, `C'AR_`, `C'AT_`, `AL_`
infixl 6 `AR__`, `AT__`, `C'AR__`, `C'AT__`, `AL__`
infixl 5 `AR___`, `AT___`, `C'AR___`, `C'AT___`, `AL___`
infixl 4 `AR____`, `AT____`, `C'AR____`, `C'AT____`, `AL____`
infixl 3 `AR_____`, `AT_____`, `C'AR_____`, `C'AT_____`, `AL_____`
infixl 2 `AR______`, `AT______`, `C'AR______`, `C'AT______`, `AL______`
infixl 1 `AR_______`, `AT_______`, `C'AR_______`, `C'AT_______`, `AL_______`

-- TODO: I think this precedence is way too low, probably 5 is better (compare with `T'TT'I)
infixl 3 `P'T'I'TT'I`
infixl 3 `S'T'I'TT'I`

type AR = (->)
type AR_ = (AR)
type AR__ = (AR)
type AR___ = (AR)
type AR____ = (AR)
type AR_____ = (AR)
type AR______ = (AR)
type AR_______ = (AR)

type AT = T'I'TT'II'T'II'I (AR) P
type AT_ = T'I'TT'II'T'II'I (AR) P
type AT__ = T'I'TT'II'T'II'I (AR) P
type AT___ = T'I'TT'II'T'II'I (AR) P
type AT____ = T'I'TT'II'T'II'I (AR) P
type AT_____ = T'I'TT'II'T'II'I (AR) P
type AT______ = T'I'TT'II'T'II'I (AR) P
type AT_______ = T'I'TT'II'T'II'I (AR) P

type AL = U_I_UU_M_I_II_II (AR) (S)
type AL_ = U_I_UU_M_I_II_II (AR) (S)
type AL__ = U_I_UU_M_I_II_II (AR) (S)
type AL___ = U_I_UU_M_I_II_II (AR) (S)
type AL____ = U_I_UU_M_I_II_II (AR) (S)
type AL_____ = U_I_UU_M_I_II_II (AR) (S)
type AL______ = U_I_UU_M_I_II_II (AR) (S)
type AL_______ = U_I_UU_M_I_II_II (AR) (S)

type AP = T'II'TT'I'III (AR) (S) Unit
type AP_ = T'II'TT'I'III (AR) (S) Unit
type AP__ = T'II'TT'I'III (AR) (S) Unit
type AP___ = T'II'TT'I'III (AR) (S) Unit
type AP____ = T'II'TT'I'III (AR) (S) Unit
type AP_____ = T'II'TT'I'III (AR) (S) Unit
type AP______ = T'II'TT'I'III (AR) (S) Unit
type AP_______ = T'II'TT'I'III (AR) (S) Unit

class Dumb x
instance Dumb x

class Mapping v vv source into t tt where
 mapping :: v source a o -> vv into (t a) (tt o)

instance Mapping T'I'II T'I'II source into t tt => Mapping T'II'I T'II'I source into tt t
 where mapping (T'II'I source) = T'II'I (map @T'I'II @T'I'II @source @into @t @tt source)

instance Mapping T'II'I T'I'II source into t tt => Mapping T'I'II T'II'I source into tt t
 where mapping (T'I'II source) = T'II'I (map @T'II'I @T'I'II @source @into @t @tt source)

map :: forall v vv source into t tt a o .
 Mapping v vv source into t tt =>
 Elicitable T'II'I Arrow (v source a o) =>
 Elicitable T'I'II Arrow (vv into (t a) (tt o)) =>
 Supertype (v source a o) -> Supertype (vv into (t a) (tt o))
map source = unwrap @Arrow (mapping @v @vv @source @into @t @tt @a @o (wrap source))

class Component into t tt where
 component :: into (t i) (tt i)

type C'AR t tt = forall i . Component (AR) t tt => t i `AR` tt i

type C'AR_ t tt = C'AR t tt
type C'AR__ t tt = C'AR t tt
type C'AR___ t tt = C'AR t tt
type C'AR____ t tt = C'AR t tt
type C'AR_____ t tt = C'AR t tt
type C'AR______ t tt = C'AR t tt
type C'AR_______ t tt = C'AR t tt

type C'AT t tt = forall i . Component (AT) t tt => t i `AT` tt i

type C'AT_ t tt = C'AT t tt
type C'AT__ t tt = C'AT t tt
type C'AT___ t tt = C'AT t tt
type C'AT____ t tt = C'AT t tt
type C'AT_____ t tt = C'AT t tt
type C'AT______ t tt = C'AT t tt
type C'AT_______ t tt = C'AT t tt

instance {-# OVERLAPPABLE #-} (Category into, Mapping T'I'II T'I'II into into t tt) => Component into t tt where
 component = map @T'I'II @T'I'II @into @into identity

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

{- [LAW] I preserving: mapping identity ≡ identity -}
{- [LAW] Composition preserving: mapping (f . g) ≡ mapping f . mapping g -}
class (Category source, Category into, Mapping v T'I'II source into t t) => Functor v source into t
deriving instance (Category source, Category into, Mapping v T'I'II source into t t) => Functor v source into t

{- [LAW] Composition preserving: mapping (f . g) ≡ mapping f . mapping g -}

class
 ( Precategory source, Precategory into
 , Mapping v T'I'II source into t t
 , Dumb (x v source into t)
 ) => Semi v x source into t

deriving instance
 ( Precategory source, Precategory into
 , Mapping v T'I'II source into t t
 , Dumb (Functor v source into t)
 ) => Semi v Functor source into t

-- TODO: Semi Transformation?
-- TODO: Semi Monoidal Functor?
-- TODO: Semi Covariant/Contravariant Transformation?

type Endo v x c into = x v c into into

{- LAW: mapping @tt @tt morphism . component @t @tt ≡ component @t @tt . mapping morphism @t @t -}
{- LAW: mapping @tt @tt morphism . component @t @tt ≡ component @t @tt . mapping morphism @t @t -}
class
 ( Mapping v T'I'II source into t tt
 , x v source into t
 , x v source into tt
 ) => Transformation v x source into t tt

deriving instance
 ( Mapping v T'I'II source into t tt
 , x v source into t
 , x v source into tt
 ) => Transformation v x source into t tt

type Dinatural = T'II'I

type Covariant t = t T'I'II

type Contravariant t = t T'II'I

type Constant t = t T''II

type Kleisli u t = T'I'TT'II u t

class (Category source, x v source into t, forall o . Mapping v T'I'II source Arrow t (Embedding v source into t o)) =>
 Yoneda v x source into t where
 yoneda :: forall a o .
  Category source =>
  Precategory into =>
  (Supertype (v source a a) ~ source a a) =>
  Elicitable T'II'I (AR) (v source a a) =>
  t a -> into (v source a o) (t o)
 yoneda x = unwrap (map @v @T'I'II @source @Arrow @t @(Embedding v source into t o) identity x)

deriving instance
 (Category source, x v source into t, forall r . Mapping v T'I'II source Arrow t (Embedding v source into t r)) =>
 Yoneda v x source into t

type family Representation t where
 Representation I = Unit
 Representation (T'I'II AR a) = a
 Representation (T'TT'I t tt) = Representation t `P` Representation tt
 Representation (T'TTT'TT'I t ttt tt) = Representation t `P` Representation tt `P` Representation ttt
 Representation (T'I'I (P)) = Unit `S` Unit

class
  ( Mapping v T'I'II source into t (v hom (Representation t))
  , Mapping v T'I'II source into (v hom (Representation t)) t
  ) => Representable hom v source into t

deriving instance
 ( Mapping v T'I'II source into t (v hom (Representation t))
 , Mapping v T'I'II source into (v hom (Representation t)) t
 ) => Representable hom v source into t

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
 Neutral (R) = Void

type family Aught p where
 Aught T'I'II = Unit
 Aught T'II'I = Void

type P'I'II = T'I'II P
type P'II'I = T'II'I P

type S'I'II = T'I'II S
type S'II'I = T'II'I S

class
 ( forall e . Mapping v v source into (T'II'I u e) I
 , forall e . Mapping v v source into (T'I'II u e) I
 ) => Cone v source into u

deriving instance
 ( forall e . Mapping v v source into (T'II'I u e) I
 , forall e . Mapping v v source into (T'I'II u e) I
 ) => Cone v source into u

left :: forall v source into a o e .
 Cone v source into (Object (Aught v)) =>
 Elicitable T'II'I Arrow (v source a o) =>
 Elicitable T'I'II Arrow (v into ((T'II'I (Object (Aught v))) e a) (I o)) =>
 Supertype (v source a o) -> Supertype (v into (T'II'I (Object (Aught v)) e a) (I o))
left source = map @v @v @source @into @(T'II'I (Object (Aught v)) e) @I @a @o source

right :: forall v source into a o e .
 Cone v source into (Object (Aught v)) =>
 Elicitable T'II'I Arrow (v source a o) =>
 Elicitable T'I'II Arrow (v into (T'I'II (Object (Aught v)) e a) (I o)) =>
 Supertype (v source a o) -> Supertype (v into (T'I'II (Object (Aught v)) e a) (I o))
right source = map @v @v @source @into @(T'I'II (Object (Aught v)) e) @I @a @o source

type Limit v source into =
 ( Cone v source into (Object (Aught v))
 , Mapping v v source into I (Both (Object (Aught v)))
 )

type Product = Object Unit

type Sum = Object Void

-- TODO: maybe we can unify `Initial`/`Terminal` typeclasses into one `Morphism`?

class Initial into where
 initial' :: into Void e

instance Initial (AR) where
 initial' x = case x of {}

class Terminal into where
 terminal :: into i Unit

instance Terminal (AR) where
 terminal _ = Unit

instance Terminal (AT) where
 terminal = T'I'TT'II'T'II'I (\x -> These Unit (\_ -> x))

type Day = U_V_UU_UUU_UUUU_T'TT'I_II_III P

class
 ( Covariant x into source t
 , Covariant x source into tt
 , Covariant Transformation x into source (T'TT'I t tt) I
 , Covariant Transformation x source into I (T'TT'I tt t)
 ) => Adjoint x source into t tt | t -> tt

class
 ( forall e ee . Mapping v vv source into (Day v source u uu t (t `L` t `T` l) e ee) t
 , Mapping v vv source into (v into (Neutral uu)) t
 , x v source into t
 ) => Monoidal v vv x source into u uu l t where

deriving instance
 ( forall e ee . Mapping v vv source into (Day v source u uu t (t `L` t `T` l) e ee) t
 , Mapping v vv source into (v into (Neutral uu)) t
 , x v source into t
 ) => Monoidal v vv x source into u uu l t

class x v T'I'II xx source into u uu l t
 => Lax v x xx source into u uu l t where

deriving instance Monoidal v T'I'II Functor source into u uu l t
 => Lax v Monoidal Functor source into u uu l t

class x v T'II'I xx source into u uu l t
 => Oplax v x xx source into u uu l t where

deriving instance Monoidal v T'II'I Functor source into u uu l t
 => Oplax v Monoidal Functor source into u uu l t

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
 (wrap (These x (wrap @_ @(v source (uu e ee) a) t)))

instance Mapping T'I'II T'I'II (AR) (AR)
 (Day T'I'II (AR) u uu t (tt `L` tt `T` l) e ee)
 (Day T'I'II (AR) u uu t (tt `L` tt `T` l) e ee)

-- TODO: coday -- Oplax Monoidal Functor

-- TODO: generalize
empty :: forall t o . Covariant Lax Monoidal Functor (AR) (AR) (P) (S) Void t => t o
empty = component @(AR) @(T'I'II (AR) Void) @t (T'I'II initial')

-- TODO: forall t e into .
intro :: forall t into e .
 Category (AR) =>
 Category into =>
 Component into (T'I'II (AR) Unit) t =>
 Component into I (T'I'II (AR) Unit) =>
 Wrapper into (T'I'II AR Unit e) =>
 Wrapper into (I e) =>
 into `T'I` e `T'I` t e
intro = component @into @(T'I'II (AR) Unit) @t `compose` wrap `compose` constant @(AR) @into

outro :: forall t into e .
 Category into =>
 Component into t (T'I'II AR Unit) =>
 Component into I (T'I'II (AR) Unit) =>
 Wrapper into (T'I'II AR Unit e) =>
 Wrapper into (AR Unit e) =>
 Wrapper into (I e) =>
 into `T'I` t e `T'I` e
outro = unwrap `compose` unwrap `compose` component @into @t @(T'I'II (AR) Unit)

rewrap :: forall into a o .
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
 unwrap

-- cata' :: forall into t e .
--  Covariant Endo Semi Functor into t =>
--  Elicitable T'I'II into (Recursive t) =>
--  into (t e) e -> into (Recursive t) e
-- cata' into = into `compose`
--  map @T'I'II @T'I'II (cata into) `compose`
--  (let T'I'II x = elicit in x)


ana :: forall into t e .
 Covariant Endo Semi Functor into t =>
 Elicitable T'II'I into (Recursive t) =>
 into e (t e) -> into e (Recursive t)
ana into = wrap `compose` map @T'I'II @T'I'II (ana into) `compose` into

this :: forall e ee . e `P` ee -> e
this (These x _) = x

that :: forall ee e . e `P` ee -> ee
that (These _ x) = x

constant :: forall source into a o .
 Category source =>
 Precategory into =>
 Component into I (T'I'II source a) =>
 Elicitable T'I'II into (T'I'II source a o) =>
 Elicitable T'II'I into (I o) =>
 into o (source a o)
constant = unwrap @_ @(T'I'II source a _)
 `compose` component @into
 `compose` wrap @into @(I o)

is :: Category AR_ => e `AR_` e
is = identity

type (R) = U_T'I'II_UT'I'II (S) P

instance Wrapper (AR) x
 => Elicitable T'I'II (T'I'TT'II'T'II'I (AR) (P)) x where
 elicit = T'I'II (T'I'TT'II'T'II'I (\x -> These (unwrap x) wrap))

instance Wrapper (AR) x
 => Elicitable T'II'I (T'I'TT'II'T'II'I (AR) (P)) x where
 elicit = T'II'I (T'I'TT'II'T'II'I (\x -> These (wrap x) unwrap))

class Setoid into e where
 equality :: into (e `P` e) (e `P` e `S` e)

type P'T'I'TT'I = T'TT'I'TTT'I (P)

pattern LRT x xx = T'TT'I'TTT'I (These x xx)

type S'T'I'TT'I = T'TT'I'TTT'I (S)

pattern LT x = T'TT'I'TTT'I (This x)
pattern RT x = T'TT'I'TTT'I (That x)

class Objective v into a o where
 objective :: Supertype (v into a o)

instance {-# OVERLAPPABLE #-} (Category into, Wrapper into a, Objective T'I'II into (Supertype a) o)
 => Objective T'I'II into a o where objective = objective @T'I'II @into `compose` unwrap @into

instance {-# OVERLAPPABLE #-} (Category into, Wrapper into a, Objective T'II'I into (Supertype a) o)
 => Objective T'II'I into a o where objective = wrap @into `compose` objective @T'II'I @into

instance (e ~ eee, ee ~ eeee, Category into) => Objective T'I'II into (e `S` ee) (eee `S` eeee) where
 objective = identity

instance (e ~ eee, ee ~ eeee, Category into) => Objective T'I'II into (e `P` ee) (eee `P` eeee) where
 objective = identity

instance (e ~ eee, ee ~ eeee, Category into) => Objective T'II'I into (e `S` ee) (eee `S` eeee) where
 objective = identity

instance (e ~ eee, ee ~ eeee, Category into) => Objective T'II'I into (e `P` ee) (eee `P` eeee) where
 objective = identity

-- TODO: generalize, move to `Abstract` module
newtype U_I_UU_M_I_II_II u uu i ii = U_I_UU_M_I_II_II (u i (uu (M i ii) ii))

type instance Supertype (U_I_UU_M_I_II_II u uu i ii) = u i (uu (M i ii) ii)

instance Elicitable T'II'I (AR) (U_I_UU_M_I_II_II u uu i ii)
 where elicit = T'II'I U_I_UU_M_I_II_II

instance Elicitable T'I'II (AR) (U_I_UU_M_I_II_II u uu i ii)
 where elicit = T'I'II (\(U_I_UU_M_I_II_II x) -> x)

type Final = T'I'

pattern Final x = T'I' x

type Twice = Both (P)

pattern Twice :: i `P` i `AR___` T'I'I P i
pattern Twice x = T'I'I x

type Opted = Both (S)

pattern Opted :: i `S` i `AR___` T'I'I S i
pattern Opted x = T'I'I x

-- TODO: these typeclasses are experimental
class Semigroup source e where s :: e `P` e `source` e
class Quasigroup source e where p :: e `P` e `source` e
