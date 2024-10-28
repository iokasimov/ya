{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE UndecidableInstances #-}
module Ya.Program.Primitive where

import Ya.Algebra
import Ya.Program.Patterns

not :: e `ML` ee `AR_` ee `ML` e
not = That `la` This

provide :: U_I_II (->) e e
provide = U_I_II identity

adjust ::
 Castable Straight Arrow (Reference LM origin target target) =>
 Castable Straight Arrow (Attribute origin target) =>
 Attribute origin target -> (target -> target) -> (origin -> origin)
adjust attr f s = let (These h x) = attr `he` s in x `li`f h

-- TODO: should be moved later
-- instance Mapping Straight Straight Attribute Attribute (Construction t) (t `T'TT'I` Construction t)
 -- where mapping = rewrap `compose` rewrap `compose` rewrap / \from (Construct x xs) -> These 
  -- ((T'TT'I / wrap @Arrow @(R_U_I_T_I _ _ _) `fo` xs) `yo` from `ho` (\(These y _) -> y))
  -- (\new -> Construct x (unwrap @Arrow @(R_U_I_T_I _ _ _) `fo` unwrap new) `yo` from `ho` (\(These _ y) -> y))

auto :: Automation e e e
auto x = x `lu` x

switch :: ee -> Automation e e ee
switch = (auto `ho'hu`)

leaf :: forall t e .
 Monoidal Straight Functor (->) LM ML t =>
 e -> Recursive (U_I_T_II t LM e)
leaf x = Recursive `ha` U_I_T_II `ha` These x `li_` empty `yo` initial @(->)

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
  (\new -> Root x `li_` new `yo` unwrap @Arrow @(R_U_I_T_I _ _ _))

intro :: forall e t . Monoidal Straight Functor (->) LM LM t => e -> t e
intro x = enter `yu` x

layer :: forall g f e .
 Component Natural (->) (->) f (f `JNT` g) =>
 f e -> (f `JNT` g) e
layer = component @Straight @(->) @(->) @f @(f `JNT` g) @e

embed :: forall f g e .
 Component Natural (->) (->) g (f `JNT` g) =>
 g e -> (f `JNT` g) e
embed = component @Straight @(->) @(->) @g @(f `JNT` g) @e

joint :: forall f g e .
 Component Natural (->) (->) (f `T'TT'I` g) (f `JNT` g) =>
 Castable Opposite (->) ((f `T'TT'I` g) e) =>
 f (g e) -> (f `JNT` g) `T'I` e
joint = wrap @(->) @((f `T'TT'I` g) e) `ho` component @Straight @(->) @(->) @(f `T'TT'I` g) @(f `JNT` g) @e

-- Define a special `Mapping` instance instead and use `Try` label constructor for it
try :: forall t e o .
 Covariant Endo Semi Functor (->) t =>
 Component Natural (->) (->) (t `T'TT'I` Progress e) (t `JNT` Progress e) =>
 Castable Opposite (->) ((t `T'TT'I` Progress e) e) =>
 t (Progress e o) -> (t `JNT` Progress e) `T'I` o
try = wrap @(->) @((t `T'TT'I` Progress e) _) `ho` component @Straight @(->) @(->)

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
 Component Natural (->) (->) (t `T'TT'I` t) t =>
 t e -> t e
repeat x = x `yuk` repeat x

to :: forall tt t e .
 Component Straight (->) (->) t tt =>
 t e -> tt e
to = component @Straight @Arrow

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
 idx origin `he` index `lu`
  (\x -> tbt `ha` U_I_II  `he`
   (\index' -> constant (idx origin `he` index') `la` constant x `li` q (index' `lu` index))
  )
