{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE UndecidableInstances #-}
module Ya.Program.Primitive where

import Ya.Algebra
import Ya.Program.Patterns

not :: e `ML` ee `AR_` ee `ML` e
not = That `la` This

-- TODO: generalize
row :: e `ML` (ee `ML` eee) `AR__` (e `ML` ee) `ML` eee
row (This x) = This (This x)
row (That (This x)) = This (That x)
row (That (That x)) = That x

provide :: U_I_II (->) e e
provide = U_I_II identity

adjust ::
 Elicitable U_I_II Arrow (Attribute origin target) =>
 Attribute origin target -> (target -> target) -> (origin -> origin)
adjust attr f s = let (These h x) = attr `he'hv` s in x `li`f h

-- TODO: should be moved later
-- instance Mapping U_I_II U_I_II Attribute Attribute (Construction t) (t `T'TT'I` Construction t)
 -- where mapping = rewrap `compose` rewrap `compose` rewrap / \from (Construct x xs) -> These 
  -- ((T'TT'I / wrap @Arrow @(R_U_I_T_I _ _ _) `fo` xs) `yo` from `ho` (\(These y _) -> y))
  -- (\new -> Construct x (unwrap @Arrow @(R_U_I_T_I _ _ _) `fo` unwrap new) `yo` from `ho` (\(These _ y) -> y))

auto :: Automation e e e
auto x = x `lu` x

switch :: ee -> Automation e e ee
switch new old = old `lu` new

leaf :: forall t e .
 Monoidal U_I_II Functor (->) LM ML t =>
 e -> Recursive (U_I_T_II t LM e)
leaf x = Recursive `ha` U_I_T_II `ha` These x `li_` empty `yo` initial' @(->)

self :: forall e . Reference LM e e e
self x = x `lu` identity

top :: forall tt t e .
 (tt ~ Construction t) =>
 Reference LM (Construction t e) e e
top (R_U_I_T_I (Recursive (U_I_T_II (These old xs)))) =
  old `lu` (\new -> Root new xs)

sub :: forall tt t e .
 (tt ~ Construction t) =>
 Covariant Endo Semi Functor (->) t =>
 Reference LM (Construction t e) (t (Construction t e)) (t (Construction t e))
sub (R_U_I_T_I (Recursive (U_I_T_II (These x old)))) = These
  (wrap @(->) @(R_U_I_T_I _ _ _) `fo` old)
  (\new -> Root x `li_` new `yo` unwrap @Arrow @(R_U_I_T_I _ _ _))

intro :: forall t e . Monoidal U_I_II Functor (->) LM LM t => e -> t e
intro x = enter `yu` x

layer :: forall g f e .
 Component Natural (->) (->) f (f `JNT` g) =>
 f e -> (f `JNT` g) e
layer = component @U_I_II @(->) @(->) @f @(f `JNT` g) @e

embed :: forall f g e .
 Component Natural (->) (->) g (f `JNT` g) =>
 g e -> (f `JNT` g) e
embed = component @U_I_II @(->) @(->) @g @(f `JNT` g) @e

joint :: forall f g e .
 Component Natural (->) (->) (f `T'TT'I` g) (f `JNT` g) =>
 Elicitable U_II_I (->) ((f `T'TT'I` g) e) =>
 f (g e) -> (f `JNT` g) `T'I` e
joint = wrap @(->) @((f `T'TT'I` g) e) `ho` component @U_I_II @(->) @(->) @(f `T'TT'I` g) @(f `JNT` g) @e

-- Define a special `Mapping` instance instead and use `Try` label constructor for it
try :: forall t e o .
 Covariant Endo Semi Functor (->) t =>
 Component Natural (->) (->) (t `T'TT'I` Progress e) (t `JNT` Progress e) =>
 Elicitable U_II_I (->) ((t `T'TT'I` Progress e) e) =>
 t (Progress e o) -> (t `JNT` Progress e) `T'I` o
try = wrap @(->) @((t `T'TT'I` Progress e) _) `ho` component @U_I_II @(->) @(->)

prompt ::
 Elicitable U_II_I (->) e =>
 Supertype e -> e
prompt = wrap

to :: forall tt t e .
 Component U_I_II (->) (->) t tt =>
 t e -> tt e
to = component @U_I_II @Arrow

by :: Unit `AR` a `AR_` a
by = unwrap

same :: Setoid Arrow e => e `LM` e `AR_` e `LM` e `ML`  e
same = q

rep :: forall r t e .
 (r ~ Representation t) =>
 Setoid Arrow (Representation t) =>
 Covariant (Representable (->)) (->) (->) t =>
 Representation t `AR_` Attribute `T'I` t e `T'I` e
rep index = U_I_UU_II_U_II_I `li` \origin ->
 let idx = map @U_I_II @U_I_II @Arrow @Arrow @t @(U_I_II (->) (Representation t)) identity in
 let tbt = map @U_I_II @U_I_II @Arrow @Arrow @(U_I_II (->) (Representation t)) @t identity in
 idx origin `he'hv` index `lu`
  (\x -> tbt `ha` U_I_II `hv`
   (\index' -> is `hu_` idx origin `he'hv` index' `la` is `hu` x `li` q (index' `lu` index))
  )
