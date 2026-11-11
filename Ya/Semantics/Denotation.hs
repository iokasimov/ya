{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE UndecidableSuperClasses #-}
module Ya.Semantics.Denotation where

import Ya.Semantics.Structures

class Initial target where
 initial :: target Void i

instance Initial (AR) where
 initial x = case x of {}

class Terminal target where
 terminal :: target i Unit

instance Terminal (AR) where
 terminal _ = Unit

type Covariant t = t T'I'II

type Contravariant t = t T'II'I

type Endo v x c target = x v c target target

{- [LAW] Associativity: compose f (compose g) ≡ compose (compose f g) -}
class
 ( forall e . Covariant Mapping source (AR) (T'I'II source e)
 , forall e . Contravariant Mapping source (AR) (T'II'I source e)
 ) => Semicategory source where
 compose :: source a o -> source e a -> source e o
 compose post pre = let T'I'II y = map @T'I'II post (T'I'II pre) in y

deriving instance
 ( forall e . Covariant Mapping source (AR) (T'I'II source e)
 , forall e . Contravariant Mapping source (AR) (T'II'I source e)
 ) => Semicategory source

{- [LAW] Left identity: identity . f ≡ f -}
{- [LAW] Right identity: f . identity ≡ f -}
class Semicategory source => Category source
 where identity :: source a a

{- [LAW] Identity preserving: mapping identity ≡ identity -}
{- [LAW] Composition preserving: mapping (f . g) ≡ mapping f . mapping g -}
class (Category source, Category target, Mapping v source target t) => Functor v source target t
deriving instance (Category source, Category target, Mapping v source target t) => Functor v source target t

class Undetermined x
instance Undetermined x

{- [LAW] Composition preserving: mapping (f . g) ≡ mapping f . mapping g -}

class
 ( Semicategory source, Semicategory target
 , Mapping v source target t
 , Undetermined (x v source target t)
 ) => Semi v x source target t

deriving instance
 ( Semicategory source, Semicategory target
 , Mapping v source target t
 , Undetermined (Functor v source target t)
 ) => Semi v Functor source target t

class Mapping v source target t where
 mapping :: v source a o -> target (t a) (t o)

map :: forall v source target t a o .
 Mapping v source target t =>
 Subtyping (AR) (v source a o) =>
 Supertype (v source a o) -> target (t a) (t o)
map source = mapping @v @source @target @t @a @o (subtype source)

class Component target t tt where
 component :: target (t i) (tt i)

rewrap :: forall target a o .
 Semicategory target =>
 Supertyping target a =>
 Subtyping target o =>
 target (Supertype a) (Supertype o) -> target a o
rewrap f = subtype `compose` f `compose` supertype

wrapped :: forall target a o .
 Semicategory target =>
 Supertyping target o =>
 Subtyping target a =>
 target a o -> target (Supertype a) (Supertype o)
wrapped f = supertype `compose` f `compose` subtype

this :: forall i ii . i `P` ii -> i
this (These x _) = x

that :: forall ii i . i `P` ii -> ii
that (These _ x) = x

class
 ( forall e . Covariant Endo Semi x target (T'I'II target e)
 , forall e . Contravariant Endo Semi x target (T'II'I target e)
 ) => Hom x target

instance
 ( forall e . Covariant Endo Semi Functor target (T'I'II target e)
 , forall e . Contravariant Endo Semi Functor target (T'II'I target e)
 ) => Hom Functor target

class
 ( Category source
 , x v source target t
 , forall e . Component target t (Embedding v source target t e)
 , forall e ee . Supertyping target (Embedding v source target t ee e)
 ) => Yoneda v x source target t where
 yoneda :: forall a o .
  Category source =>
  Semicategory target =>
  (Supertype (v source a a) ~ source a a) =>
  Subtyping (AR) (v source a a) =>
  target (t a) (target (v source a o) (t o))
 yoneda = supertype `compose` component @target @t @(Embedding v source target t o)

deriving instance
 ( Category source
 , x v source target t
 , forall e . Component target t (Embedding v source target t e)
 , forall e ee . Supertyping target (Embedding v source target t ee e)
 ) => Yoneda v x source target t

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

basetype :: forall target i .
 Covariant Objective target i (Basetype i) =>
 target i (Basetype i)
basetype = objective @T'I'II @target

boundtype :: forall target i .
 Contravariant Objective target i (Basetype i) =>
 target (Basetype i) i
boundtype = objective @T'II'I @target
