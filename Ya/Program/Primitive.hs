{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE UndecidableInstances #-}
module Ya.Program.Primitive where

import Ya.Algebra
import Ya.Program.Patterns

on :: forall t e . t e `ARR` t e
on = identity

not :: e `ML` ee `ARR` ee `ML` e
not = That `la` This

provide :: U_I_II (->) e e
provide = U_I_II identity

adjust ::
 Castable Straight Arrow (Reference LM origin target target) =>
 Castable Straight Arrow (Attribute origin target) =>
 Attribute origin target -> (target -> target) -> (origin -> origin)
adjust attr f s = let (These h x) = attr `he` s in x `li`f h

-- TODO: should be moved later
-- instance Mapping Straight Straight Attribute Attribute (Construction t) (t `T_TT_I` Construction t)
 -- where mapping = rewrap `compose` rewrap `compose` rewrap / \from (Construct x xs) -> These 
  -- ((T_TT_I / wrap @Arrow @(R_U_I_T_I _ _ _) `fo` xs) `yo` from `ho` (\(These y _) -> y))
  -- (\new -> Construct x (unwrap @Arrow @(R_U_I_T_I _ _ _) `fo` unwrap new) `yo` from `ho` (\(These _ y) -> y))

auto :: Automation e e e
auto x = x `lu` x

leaf :: forall t e .
 Monoidal Straight Functor (->) LM ML t =>
 e -> Recursive (U_I_T_II t LM e)
leaf x = Recursive `ha` U_I_T_II `ha` These x `lii` empty `yo` initial @(->)

self :: Reference LM e e e
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
  (\new -> Root x `lii` new `yo` unwrap @Arrow @(R_U_I_T_I _ _ _))

intro :: forall e t . Monoidal Straight Functor (->) LM LM t => e -> t e
intro x = enter `yu` x

layer :: forall g f e .
 Component Natural (->) (->) f (f `JT` g) =>
 f e -> (f `JT` g) e
layer = component @Straight @(->) @(->) @f @(f `JT` g) @e

embed :: forall f g e .
 Component Natural (->) (->) g (f `JT` g) =>
 g e -> (f `JT` g) e
embed = component @Straight @(->) @(->) @g @(f `JT` g) @e

joint :: forall f g e .
 Component Natural (->) (->) (f `T_TT_I` g) (f `JT` g) =>
 Castable Opposite (->) ((f `T_TT_I` g) e) =>
 f (g e) -> f `JT` g `TI` e
joint = wrap @(->) @((f `T_TT_I` g) e) `ho` component @Straight @(->) @(->) @(f `T_TT_I` g) @(f `JT` g) @e

-- Define a special `Mapping` instance instead and use `Try` label constructor for it
try :: forall t e o .
 Covariant Endo Semi Functor (->) t =>
 Component Natural (->) (->) (t `T_TT_I` Progress e) (t `JT` Progress e) =>
 Castable Opposite (->) ((t `T_TT_I` Progress e) e) =>
 t (Progress e o) -> t `JT` Progress e `TI` o
try = wrap @(->) @((t `T_TT_I` Progress e) _) `ho` component @Straight @(->) @(->)

label :: forall l t e . t e -> T_'_I l t e
label = T_'_I

by :: forall label t e . t e -> Labeled label t e
by = T_'_I

frame ::
 Castable Opposite (->) e =>
 Supertype e -> e
frame = wrap

prompt ::
 Castable Opposite (->) e =>
 Supertype e -> e
prompt = wrap

-- TODO: replace with `by @Repeat`
repeat ::
 Component Natural (->) (->) (t `T_TT_I` t) t =>
 t e -> t e
repeat x = x `yuk` repeat x

transform :: forall tt t e .
 Component Straight (->) (->) t tt =>
 t e -> tt e
transform = component @Straight @Arrow

same :: Setoid e => e `ARR` e `ARR` e `LM` e `ML`  e
same = q

rep :: forall r t e .
 (r ~ Representation t) =>
 Setoid (Representation t) =>
 Covariant (Representable (->)) (->) (->) t =>
 Representation t `ARR` Attribute `TI` t e `TI` e
rep index = U_I_UU_II_U_II_I `li` \origin ->
 let idx = map @U_I_II @U_I_II @Arrow @Arrow @t @(U_I_II (->) (Representation t)) identity in
 let tbt = map @U_I_II @U_I_II @Arrow @Arrow @(U_I_II (->) (Representation t)) @t identity in
 idx origin `he` index `lu`
  (\x -> tbt `ha` U_I_II  `he`
   (\index' -> constant (idx origin `he` index') `la` constant x `li` index' `q` index)
  )
