{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE UndecidableSuperClasses #-}
{-# LANGUAGE QuantifiedConstraints #-}
module Ya.Program.Primitive where

import Ya.Algebra
import Ya.Program.Patterns

not :: e `S` ee `AR_` ee `S` e
not = That `la` This

row :: forall e ee eee ee_eee eeee .
 Objective AR (e `S` ee_eee) eeee =>
 Objective AR (ee `S` eee) ee_eee =>
 eeee `AR__` (e `S` ee) `S` eee
row = This `ha` This `la_` This `ha` That `la` That `ha_` is @ee_eee

provide :: U_I_II (->) e e
provide = U_I_II identity

-- TODO: should be moved later
-- instance Mapping U_I_II U_I_II Attribute Attribute (Construction t) (t `T'TT'I` Construction t)
 -- where mapping = rewrap `compose` rewrap `compose` rewrap / \from (Construct x xs) -> These 
  -- ((T'TT'I / wrap @Arrow @(R_U_I_T_I _ _ _) `fo` xs) `yo` from `ho` (\(These y _) -> y))
  -- (\new -> Construct x (unwrap @Arrow @(R_U_I_T_I _ _ _) `fo` unwrap new) `yo` from `ho` (\(These _ y) -> y))

auto, get :: Automation e e e
auto x = x `lu` x
get = auto

switch, put :: ee -> Automation e e ee
switch new old = old `lu` new
put = switch

leaf :: forall t e .
 Covariant Monoidal Functor (->) (->) P S Unit t =>
 e -> Recursive (U_I_T_II t P e)
leaf x = Recursive `ha` U_I_T_II `ha` These x `li_` empty `yo` initial' @(->)

it :: forall e . Reference P e e e
it x = x `lu` identity

top :: forall tt t e .
 (tt ~ Construction t) =>
 Supertype (Construction t e `AT` e)
top (R_U_I_T_I (Recursive (U_I_T_II (These old xs)))) =
  old `lu` (\new -> Root new xs)

sub :: forall tt t e .
 (tt ~ Construction t) =>
 Covariant Endo Semi Functor (->) t =>
 Supertype (Construction t e `AT` t (Construction t e))
sub (R_U_I_T_I (Recursive (U_I_T_II (These x old)))) = These
  (wrap @(->) @(R_U_I_T_I _ _ _) `fo` old)
  (\new -> Root x `li_` new `yo` unwrap @Arrow @(R_U_I_T_I _ _ _))

intro :: forall t e . Covariant Monoidal Functor (->) (->) P P Unit t => e -> t e
intro x = enter `yu` x

-- layer :: forall g f e .
 -- Component (->) f (f `JNT` g) =>
 -- f e -> (f `JNT` g) e
-- layer = component @(->) @f @(f `JNT` g) @e

embed :: forall f g e .
 Component (->) g (f `JNT` g) =>
 g e -> (f `JNT` g) e
embed = component @(->) @g @(f `JNT` g) @e

joint :: forall f g e .
 Component (->) (f `T'TT'I` g) (f `JNT` g) =>
 Elicitable U_II_I (->) ((f `T'TT'I` g) e) =>
 f (g e) -> (f `JNT` g) `T'I` e
joint = wrap @(->) @((f `T'TT'I` g) e) `ho` component @(->) @(f `T'TT'I` g) @(f `JNT` g) @e

-- Define a special `Mapping` instance instead and use `Try` label constructor for it
try :: forall t e o .
 Covariant Endo Semi Functor (->) t =>
 Component (->) (t `T'TT'I` Progress e) (t `JNT` Progress e) =>
 Elicitable U_II_I (->) ((t `T'TT'I` Progress e) e) =>
 t (Progress e o) -> (t `JNT` Progress e) `T'I` o
try = wrap @(->) @((t `T'TT'I` Progress e) _) `ho` component @(->)

-- prompt ::
 -- Elicitable U_II_I (->) e =>
 -- Supertype e -> e
-- prompt = wrap

to :: forall tt t e .
 Component AR t tt =>
 t e `AR` tt e
to = component @AR

as :: forall tt t e .
 Component AT t tt =>
 t e `AT` tt e
as = component @AT

by :: Unit `AR` a `AR_` a
by = unwrap

same :: Setoid Arrow e => e `P` e `AR_` e `P` e `S`  e
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

{-
class Choose c d where
  resolve :: (c => r) -> (d => r) -> r

-- instance -- Mapping U_I_II U_I_II AR AR t tt =>
 -- Choose (Mapping U_I_II U_I_II AR AR t tt) d
 -- where resolve r _ = r

-- instance d =>
 -- Choose (Mapping U_1_I U_I_1 P P t tt) d
 -- where resolve _ r = r

instance {-# OVERLAPPABLE #-} d => (Choose c d) where resolve _ r = r
instance {-# OVERLAPPING #-} c => (Choose c d) where resolve r _ = r

-- instance {-# OVERLAPPABLE #-} d => Choose (a ~ b) d where resolve = \_ a -> a

-- instance {-# OVERLAPPING #-} Choose (a ~ a) d where resolve = \a _ -> a

-- instance (Mapping U_II_I U_I_II AR AR t tt) => (Category P || Mapping U_II_I U_I_II AR AR t tt) where resolve = \_ r -> r

to :: forall tt t i .
 (Supertype (U_I_II AR i i) ~ AR i i) =>
 (Supertype (U_II_I AR i i) ~ AR i i) =>
 Elicitable U_II_I AR (U_II_I AR i i) =>
 Elicitable U_II_I AR (U_I_II AR i i) =>
 Choose (Mapping U_I_II U_I_II AR AR t tt) (Mapping U_II_I U_I_II AR AR t tt) =>
 t i `AR__` tt i
to = resolve @(Mapping U_I_II U_I_II AR AR t tt) @(Mapping U_II_I U_I_II AR AR t tt)
 (unwrap @AR (mapping @U_I_II @U_I_II @AR @AR @t @tt @_ @_ (wrap identity)))
 (unwrap @AR (mapping @U_II_I @U_I_II @AR @AR @t @tt @_ @_ (wrap identity)))

class Component' into t tt where
 component' :: into (t i) (tt i)

instance
 Mapping U_I_II U_I_II AR AR t tt
 => Component' AR t tt where
 component' = unwrap @AR (mapping @U_I_II @U_I_II @AR @AR @t @tt (wrap identity))

instance {-# OVERLAPS #-}
 (forall i . Setoid AR i, Mapping U_II_I U_I_II AR AR I (U_II_I AR Boolean))
 => Component' AR I (U_II_I AR Boolean) where
 component' (Identity x) = Predicate / \x' -> is `hu` by False `la` Same `hu` by True `li` x `hd'q` x'

to :: forall tt t i .
 Component' AR t tt =>
 t i -> tt i
to = component'

-- instance Component AR AR t tt => Component' AR t Predicate where
 -- component' = unwrap @AR (mapping @U_II_I @U_I_II @AR @AR @t @tt @_ @_ (wrap identity))

-- deriving instance Component' 
-}

-- instance -- {-# OVERLAPS #-}
 -- (forall i . Setoid AR i) -- , Mapping U_II_I U_I_II AR AR I (U_II_I AR Boolean))
 -- => Component' AR I (U_II_I AR Boolean) where
 -- component' (Identity x) = Predicate / \x' -> is `hu` by False `la` Same `hu` by True `li` x `hd'q` x'
