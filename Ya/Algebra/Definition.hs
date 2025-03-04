{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE UndecidableSuperClasses #-}
module Ya.Algebra.Definition where

import Ya.Algebra.Abstract

infixl 8 `LM`, `S`, `MN`
infixl 7 `LM_`, `S_`, `MN_`
infixl 6 `LM__`, `S__`, `MN__`

infixr 7 `JNT`
infixr 6 `JNT_`

infixl 8 `AR`, `AT`
infixl 7 `AR_`, `AT_`
infixl 6 `AR__`, `AT__`
infixl 5 `AR___`, `AT___`
infixl 4 `AR____`, `AT____`
infixl 3 `AR_____`, `AT_____`
infixl 2 `AR______`, `AT______`
infixl 1 `AR_______`, `AT_______`

infixl 3 `LM'T'I'TT'I`
infixl 3 `S'T'I'TT'I`

infixl 0 /

type AR = (->)
type AR_ = (->)
type AR__ = (->)
type AR___ = (->)
type AR____ = (->)
type AR_____ = (->)
type AR______ = (->)
type AR_______ = (->)

type AT = U_I_UU_II_U_II_I (->) LM
type AT_ = U_I_UU_II_U_II_I (->) LM
type AT__ = U_I_UU_II_U_II_I (->) LM
type AT___ = U_I_UU_II_U_II_I (->) LM
type AT____ = U_I_UU_II_U_II_I (->) LM
type AT_____ = U_I_UU_II_U_II_I (->) LM
type AT______ = U_I_UU_II_U_II_I (->) LM
type AT_______ = U_I_UU_II_U_II_I (->) LM

class Dumb x
instance Dumb x

class Mapping v vv from into f tt where
 mapping :: v from a o -> vv into (f a) (tt o)

instance Mapping U_I_II U_I_II from into t tt => Mapping U_II_I U_II_I from into tt t
 where mapping (U_II_I from) = U_II_I (map @U_I_II @U_I_II @from @into @t @tt from)

instance Mapping U_II_I U_I_II from into t tt => Mapping U_I_II U_II_I from into tt t
 where mapping (U_I_II from) = U_II_I (map @U_II_I @U_I_II @from @into @t @tt from)

map :: forall v vv from into t tt a o .
 Mapping v vv from into t tt =>
 Elicitable U_II_I Arrow (v from a o) =>
 Elicitable U_I_II Arrow (vv into (t a) (tt o)) =>
 Supertype (v from a o) -> Supertype (vv into (t a) (tt o))
map from = unwrap @Arrow (mapping @v @vv @from @into @t @tt @a @o (wrap from))

class Component into t tt where
 component :: into (t i) (tt i)

instance {-# OVERLAPPABLE #-} (Category into, Mapping U_I_II U_I_II into into t tt) => Component into t tt where
 component = map @U_I_II @U_I_II @into @into identity

{- [LAW] Associativity: compose f (compose g) ≡ compose (compose f g) -}
class
 ( forall e . Mapping U_I_II U_I_II from Arrow (U_I_II from e) (U_I_II from e)
 , forall e . Mapping U_II_I U_I_II from Arrow (U_II_I from e) (U_II_I from e)
 ) => Precategory from where
 compose :: from a o -> from e a -> from e o
 compose post pre = let U_I_II y = map @U_I_II @U_I_II post (U_I_II pre) in y

deriving instance
 ( forall e . Mapping U_I_II U_I_II from Arrow (U_I_II from e) (U_I_II from e)
 , forall e . Mapping U_II_I U_I_II from Arrow (U_II_I from e) (U_II_I from e)
 ) => Precategory from

{- [LAW] Left identity: identity . f ≡ f -}
{- [LAW] Right identity: f . identity ≡ f -}
class Precategory from => Category from
 where identity :: from a a

{- [LAW] I preserving: mapping identity ≡ identity -}
{- [LAW] Composition preserving: mapping (f . g) ≡ mapping f . mapping g -}
class (Category from, Category into, Mapping v U_I_II from into t t) => Functor v from into t
deriving instance (Category from, Category into, Mapping v U_I_II from into t t) => Functor v from into t

{- [LAW] Composition preserving: mapping (f . g) ≡ mapping f . mapping g -}

class
 ( Precategory from, Precategory into
 , Mapping v U_I_II from into t t
 , Dumb (x v from into t)
 ) => Semi v x from into t

deriving instance
 ( Precategory from, Precategory into
 , Mapping v U_I_II from into t t
 , Dumb (Functor v from into t)
 ) => Semi v Functor from into t

-- TODO: Semi Transformation?
-- TODO: Semi Monoidal Functor?
-- TODO: Semi Covariant/Contravariant Transformation?

type Endo v x c into = x v c into into

{- LAW: mapping @tt @tt morphism . component @t @tt ≡ component @t @tt . mapping morphism @t @t -}
{- LAW: mapping @tt @tt morphism . component @t @tt ≡ component @t @tt . mapping morphism @t @t -}
class
 ( Mapping v U_I_II from into t tt
 , x v from into t
 , x v from into tt
 ) => Transformation v x from into t tt

deriving instance
 ( Mapping v U_I_II from into t tt
 , x v from into t
 , x v from into tt
 ) => Transformation v x from into t tt

type Dinatural = U_II_I

type Covariant t = t U_I_II

type Contravariant t = t U_II_I

type Constant t = t U_1_I

type Kleisli u t = U_I_T_II t u

class (Category from, x v from into t, forall o . Mapping v U_I_II from Arrow t (UU_V_U_I_II_T_II v from into t o)) =>
 Yoneda v x from into t where
 yoneda :: forall a o .
  Category from =>
  Precategory into =>
  (Supertype (v from a a) ~ from a a) =>
  Elicitable U_II_I (->) (v from a a) =>
  t a -> into (v from a o) (t o)
 yoneda x = unwrap (map @v @U_I_II @from @Arrow @t @(UU_V_U_I_II_T_II v from into t o) identity x)

deriving instance
 (Category from, x v from into t, forall r . Mapping v U_I_II from Arrow t (UU_V_U_I_II_T_II v from into t r)) =>
 Yoneda v x from into t

type family Representation t where
 Representation I = ()
 Representation (U_I_II Arrow a) = a
 Representation (T'TT'I t tt) =
  Representation t `LM` Representation tt
 Representation (T'TTT'TT'I t ttt tt) =
  Representation t `LM` Representation tt `LM` Representation ttt
 Representation (U_I_I LM) = () `S` ()

class
  ( Mapping v U_I_II from into t (v hom (Representation t))
  , Mapping v U_I_II from into (v hom (Representation t)) t
  ) => Representable hom v from into t

deriving instance
 ( Mapping v U_I_II from into t (v hom (Representation t))
 , Mapping v U_I_II from into (v hom (Representation t)) t
 ) => Representable hom v from into t

type family Co x where Co (x U_I_II) = x U_II_I

data family Object o e ee
data instance Object Unit e ee = These e ee
data instance Object Void e ee = This e | That ee

type LM = Object Unit

type LM_ = LM
type LM__ = LM

type S = Object Void

type S_ = S
type S__ = S

type family MN r a where
 MN (_ # a `S` aa) a = aa
 MN (aa `S` _ # a) a = aa
 MN (aa `S` aaa) a = aa `MN` a `S` aaa

type MN_ a aa = MN a aa
type MN__ a aa = MN a aa

type family Neutral p where
 Neutral LM = Unit
 Neutral S = Void

type family Aught p where
 Aught U_I_II = Unit
 Aught U_II_I = Void

class
 ( forall e . Mapping v v from into (U_II_I u e) I
 , forall e . Mapping v v from into (U_I_II u e) I
 ) => Cone v from into u

deriving instance
 ( forall e . Mapping v v from into (U_II_I u e) I
 , forall e . Mapping v v from into (U_I_II u e) I
 ) => Cone v from into u

left :: forall v from into a o e .
 Cone v from into (Object (Aught v)) =>
 Elicitable U_II_I Arrow (v from a o) =>
 Elicitable U_I_II Arrow (v into ((U_II_I (Object (Aught v))) e a) (I o)) =>
 Supertype (v from a o) -> Supertype (v into (U_II_I (Object (Aught v)) e a) (I o))
left from = map @v @v @from @into @(U_II_I (Object (Aught v)) e) @I @a @o from

right :: forall v from into a o e .
 Cone v from into (Object (Aught v)) =>
 Elicitable U_II_I Arrow (v from a o) =>
 Elicitable U_I_II Arrow (v into (U_I_II (Object (Aught v)) e a) (I o)) =>
 Supertype (v from a o) -> Supertype (v into (U_I_II (Object (Aught v)) e a) (I o))
right from = map @v @v @from @into @(U_I_II (Object (Aught v)) e) @I @a @o from

type Limit v from into =
 ( Cone v from into (Object (Aught v))
 , Mapping v v from into I (Both (Object (Aught v)))
 )

type Product = Object Unit

type Sum = Object Void

-- TODO: maybe we can unify `Initial`/`Terminal` typeclasses into one `Morphism`?

class Initial into where
 initial' :: into Void e

instance Initial (->) where
 initial' x = case x of {}

class Terminal into where
 terminal :: into e ()

instance Terminal (->) where
 terminal _ = ()

type Day = U_V_UU_UUU_UUUU_T'TT'I_II_III LM

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
 ( forall e ee . Mapping v U_I_II from into (Day v from u uu t t e ee) t
 , Mapping v U_I_II from into (v into (Neutral uu)) t
 , x v from into t
 ) => Monoidal v x from into u uu t where

deriving instance
 ( forall e ee . Mapping v U_I_II from into (Day v from u uu t t e ee) t
 , Mapping v U_I_II from into (v into (Neutral uu)) t
 , x v from into t
 ) => Monoidal v x from into u uu t

-- TODO: Yoneda version?
day :: forall v from t u uu a o e ee .
 Mapping v U_I_II from (->) (Day v from u uu t t e ee) t =>
 Elicitable U_II_I Arrow (v from a o) =>
 Elicitable U_II_I Arrow (v from (uu e ee) a) =>
 Supertype (v from a o)
  -> Supertype (v from (uu e ee) a)
  -> u (t e) (t ee) -> t o
day from t x = map @v @U_I_II @from @(->)
 @(Day v from u uu t t e ee) @t from
 (wrap (These x (wrap @_ @(v from (uu e ee) a) t)))

monoidal_ :: forall v from into t u uu a o e ee .
 Adjoint Functor into into (U_I_II LM (u (t e) (t ee))) (U_I_II into (u (t e) (t ee))) =>
 Monoidal v Functor from into u uu t =>
 Wrapper Arrow (v from a o) =>
 Wrapper into (U_I_II LM (u (t e) (t ee)) (v from (uu e ee) a)) =>
 Wrapper into (U_V_UU_UUU_UUUU_T'TT'I_II_III LM v from u uu t t e ee a) =>
 Wrapper into ((U_I_II into (u (t e) (t ee)) `T'TT'I` U_I_II LM (u (t e) (t ee))) a) =>
 Wrapper into ((U_I_II into (u (t e) (t ee)) `T'TT'I` U_I_II LM (u (t e) (t ee))) (v from (uu e ee) a)) =>
 Wrapper into (U_I_II into (u (t e) (t ee)) (t o)) =>
 Wrapper into (I (v from (uu e ee) a)) =>
 Supertype (v from a o) -> into (v from (uu e ee) a) (into (u (t e) (t ee)) (t o))
monoidal_ from =
 unwrap @into @(U_I_II into _ _)
 `compose` map @U_I_II @U_I_II @into @into
  @(U_I_II into (u (t e) (t ee))) @(U_I_II into (u (t e) (t ee)))
  ((map @v @U_I_II @from @into @(Day v from u uu t t e ee) @t from `compose` wrap)
  `compose` unwrap @into @(U_I_II LM _ _))
 `compose` unwrap @into @(T'TT'I _ _ _)
 `compose` component @into @I @(U_I_II into _ `T'TT'I` U_I_II LM _)
 `compose` wrap @into

-- TODO: generalize
empty :: forall t o . Covariant Monoidal Functor (->) (->) LM S t => t o
empty = component @(->) @(U_I_II (->) Void) @t (U_I_II initial')

-- TODO: generalize so I can use Attribute here
enter :: forall t . Covariant Monoidal Functor (->) (->) LM LM t => t Unit
enter = component @(->) @(U_I_II (->) Unit) @t (U_I_II identity)

rewrap :: forall o into a .
 Precategory into =>
 Elicitable U_II_I into o =>
 Elicitable U_I_II into a =>
 into (Supertype a) (Supertype o) -> into a o
rewrap f = wrap `compose` f `compose` unwrap

wrapped :: forall into a o .
 Precategory into =>
 Elicitable U_I_II into o =>
 Elicitable U_II_I into a =>
 into a o -> into (Supertype a) (Supertype o)
wrapped f = unwrap `compose` f `compose` wrap

i_ :: forall into u a o e .
 Precategory into =>
 Elicitable U_II_I into (U_II_I u e a) =>
 Elicitable U_I_II into (U_II_I u e o) =>
 into (U_II_I u e a) (U_II_I u e o) -> into (u a e) (u o e)
i_ f = unwrap @into @(U_II_I _ _ _) `compose` f `compose` wrap @into @(U_II_I _ _ _)

_i :: forall into u a o e .
 Precategory into =>
 Elicitable U_II_I into (U_I_II u e a) =>
 Elicitable U_I_II into (U_I_II u e o) =>
 into (U_I_II u e a) (U_I_II u e o) -> into (u e a) (u e o)
_i f = unwrap @into @(U_I_II _ _ _) `compose` f `compose` wrap @into @(U_I_II _ _ _)

cata :: forall into t e .
 Covariant Endo Semi Functor into t =>
 Elicitable U_I_II into (Recursive t) =>
 into (t e) e -> into (Recursive t) e
cata into = into `compose`
 map @U_I_II @U_I_II (cata into) `compose`
 (let U_I_II x = elicit in x)

ana :: forall into t e .
 Covariant Endo Semi Functor into t =>
 Elicitable U_II_I into (Recursive t) =>
 into e (t e) -> into e (Recursive t)
ana into = wrap `compose` map @U_I_II @U_I_II (ana into) `compose` into

type family Jointable effect where
 Jointable (U_I_II AR e) = ()
 Jointable (U_I_II S e) = ()
 Jointable (U_I_II (U_I_UU_II_I AR LM) e) = ()

type family JNT effect where
 JNT (U_I_II AR e) = T'TT'I (U_I_II AR e)
 JNT (U_I_II S e) = TT'T'I (U_I_II S e)
 JNT (U_I_II (U_I_UU_II_I AR LM) e) = T'TTT'TT'I (U_I_II AR e) (U_II_I LM e)

type JNT_ effect = JNT effect

this :: forall e ee . e `LM` ee -> e
this (These x _) = x

that :: forall ee e . e `LM` ee -> ee
that (These _ x) = x

swap :: e `LM` ee `AR_` ee `LM` e
swap (These x y) = These y x

constant :: forall from into a o .
 Category from =>
 Precategory into =>
 Component into I (U_I_II from a) =>
 Elicitable U_I_II into (U_I_II from a o) =>
 Elicitable U_II_I into (I o) =>
 into o (from a o)
constant = unwrap @_ @(U_I_II from a _)
 `compose` component @into
 `compose` wrap @into @(I o)

is :: Category AR_ => e `AR_` e
is = identity

type SM = U_U_I_II_UU_I_II S LM

instance Wrapper (->) x
 => Elicitable U_I_II (U_I_UU_II_U_II_I (->) LM) x where
 elicit = U_I_II (U_I_UU_II_U_II_I (\x -> These (unwrap x) wrap))

instance Wrapper (->) x
 => Elicitable U_II_I (U_I_UU_II_U_II_I (->) LM) x where
 elicit = U_II_I (U_I_UU_II_U_II_I (\x -> These (wrap x) unwrap))

class Setoid into e where
 equality :: into (e `LM` e) (e `LM` e `S` e)

(/) :: (i -> o) -> i -> o
(/) f x = f x

type LM'T'I'TT'I = U_T_I_TT_I LM
type S'T'I'TT'I = U_T_I_TT_I S

class Objective into st t where
 objective :: into t st

instance {-# OVERLAPPABLE #-}
 ( Category into
 , Elicitable U_I_II into t
 , Objective into st (Supertype t)
 ) => Objective into st t where
 objective = objective @into `compose` unwrap @into

instance (e ~ eee, ee ~ eeee, Category into) => Objective into (e `S` ee) (eee `S` eeee) where
 objective = identity

instance (e ~ eee, ee ~ eeee, Category into) => Objective into (e `LM` ee) (eee `LM` eeee) where
 objective = identity

newtype U_I_UU_MN_I_II_II u uu i ii = U_I_UU_MN_I_II_II (u i (uu (MN i ii) ii))

type instance Supertype (U_I_UU_MN_I_II_II u uu i ii) = u i (uu (MN i ii) ii)

instance Elicitable U_II_I (->) (U_I_UU_MN_I_II_II u uu i ii)
 where elicit = U_II_I U_I_UU_MN_I_II_II

instance Elicitable U_I_II (->) (U_I_UU_MN_I_II_II u uu i ii)
 where elicit = U_I_II (\(U_I_UU_MN_I_II_II x) -> x)
