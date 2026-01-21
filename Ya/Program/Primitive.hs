{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE UndecidableSuperClasses #-}
{-# LANGUAGE QuantifiedConstraints #-}
module Ya.Program.Primitive where

import Ya.Algebra
import Ya.Operators
import Ya.Program.Patterns

not :: forall e ee eee .
 Covariant Objective (AR) e (eee `S` ee) =>
 e `AR_` ee `S` eee
not = That `has` This

swap :: forall e ee eee .
 Contravariant Objective (AR) e (eee `P` ee) =>
 ee `P` eee `AR_` e
swap (These x y) = y `hjd` x

-- TODO: should be moved later
-- instance Mapping T'I'II T'I'II Attribute Attribute (Construction t) (t `T'TT'I` Construction t)
 -- where mapping = rewrap `compose` rewrap `compose` rewrap / \source (Build x xs) -> These 
  -- ((T'TT'I / wrap @Arrow @(F'T'I'TT'I _ _ _) `fo` xs) `yo` source `ho` (\(These y _) -> y))
  -- (\new -> Build x (super @Arrow @(F'T'I'TT'I _ _ _) `fo` super new) `yo` source `ho` (\(These _ y) -> y))

fetch :: e `AR__` e `P` e
fetch = is `hop` is

relay :: ee -> e `AR__` e `P` ee
relay new old = old `hjd` new

leaf :: forall t e .
 Covariant Lax Monoidal Functor (AR) (AR) (P) (S) Void t =>
 e -> Recursive (T'I'II (P) e `T'TT'I` t)
leaf x = x `hjd_` empty `yo` initial @(AR)

it :: forall e . Reference (P) e e e
it x = x `hjd` identity

be :: o `AR__` a `AR_` o
be = constant

dim :: forall a t i .
 Covariant Functor (AR) (AR) (T'II'I t i) =>
 (forall e . Wrapper (AR) (T'II'I t i e)) =>
 t a i `AR` t Unit i
dim = fui @AR @AR Unit

top :: forall tt t e .
 (tt ~ Construction t) =>
 Supertype (Construction t e `AT` e)
top (F'T'I'TT'I (Recursive (T'TT'I (T'II'I (These xs old))))) =
  old `hjd` (\new -> Root new xs)

sub :: forall tt t e .
 (tt ~ Construction t) =>
 Covariant Endo Semi Functor (AR) t =>
 Supertype (Construction t e `AT` t (Construction t e))
sub (F'T'I'TT'I (Recursive (T'TT'I (T'II'I (These xs x))))) = These
  (xs `yo` wrap @(AR) @(F'T'I'TT'I _ _ _))
  (\new -> Root x `hc__` new `yo` super @Arrow @(F'T'I'TT'I _ _ _))

embed :: forall f g e .
 Component (AR) g (f `JNT` g) =>
 g e -> (f `JNT` g) e
embed = component @(AR) @g @(f `JNT` g) @e

-- TODO: replace this expression with a label
joint :: forall f g e .
 Component (AR) (f `T'TT'I` g) (f `JNT` g) =>
 Elicitable T'II'I (AR) ((f `T'TT'I` g) e) =>
 f (g e) -> (f `JNT` g) `T'I` e
joint = wrap @(AR) @((f `T'TT'I` g) e) `ho` component @(AR) @(f `T'TT'I` g) @(f `JNT` g) @e

to :: forall tt t i l .
 Component (->) (t `L` tt `T` l) tt =>
 t `L` tt `T` l `T` i `AR____` tt `T` i
to = component

as :: forall tt ttt t i .
 Component (AT) t tt =>
 Unlabelable (AR) t =>
 (Unlabeled t ~ ttt) =>
 t i `AR____` tt i `P` (tt i `AR__` ttt i)
as = super @(AR) `hc` component @(AT) `ho'ho'ho` unlabel @(AR)

go :: forall tt t l i .
 Component (TR) (t `L` tt `T` l) tt =>
 t `L` tt `T` l `T` i `AR____` (tt `T` i) `P` (t `T` i)
go = super (component @(TR)) `ho'ho` super @(AR) @(t `L` tt `T` l `T` i)

by :: forall t r e .
 (r ~ Representation t) =>
 Setoid Arrow (Representation t) =>
 Covariant Naperian Functor (AR) (AR) t =>
 Representation t `AR_` Supertype (Attribute `T'I` t e `T'I` e)
by index origin =
 let idx = map @T'I'II @T'I'II @Arrow @Arrow @t @(T'I'II (AR) (Representation t)) identity in
 let tbt = map @T'I'II @T'I'II @Arrow @Arrow @(T'I'II (AR) (Representation t)) @t identity in
 idx origin `hc` index `hjd`
  (\x -> tbt `ha` T'I'II `hc`
   (\index' -> is `hu_` idx origin `hc` index' `has` is `hu` x `hc___` index' `hjd'q` index)
  )

exact :: forall i . Setoid (AR) i => i `AR___` i `AR__` Boolean
exact x xx = is `hu` False Unit `has` is `hu` True Unit `hc__` x `hjd'q` xx
