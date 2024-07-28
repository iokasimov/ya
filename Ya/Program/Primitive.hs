{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE UndecidableInstances #-}
module Ya.Program.Primitive where

import Ya.Algebra
import Ya.Program.Patterns

is :: e `ARR` e
is = identity

on :: forall t e . t e `ARR` t e
on = identity

not :: e `ML` ee `ARR` ee `ML` e
not = That `rf` This

provide :: U_I_II (->) e e
provide = U_I_II identity

adjust ::
	Castable Straight Arrow (Reference origin target target) =>
	Castable Straight Arrow (Attribute origin target) =>
	Attribute origin target -> (target -> target) -> (origin -> origin)
adjust attr f s = let (These h x) = attr `yi'_yi'` s in x `i`f h

-- TODO: should be moved later
-- instance Mapping Straight Straight Attribute Attribute (Construction t) (t `T_TT_I` Construction t)
	-- where mapping = rewrap `compose` rewrap `compose` rewrap / \from (Construct x xs) -> These 
		-- ((T_TT_I / wrap @Arrow @(R_U_I_T_I _ _ _) `fo` xs) `yo` from `ho` (\(These y _) -> y))
		-- (\new -> Construct x (unwrap @Arrow @(R_U_I_T_I _ _ _) `fo` unwrap new) `yo` from `ho` (\(These _ y) -> y))

review :: Transition state state
review = W_I_I_II `ha` U_I_UU_II_III `i` \old -> These `i` old `i` old

switch :: (e -> ee) -> Automation e ee e
switch f = U_I_UU_II_III `i` \x -> f x `lm` x

put :: state -> Transition state state
put new = W_I_I_II `ha` U_I_UU_II_III `i` \old -> These `i` new `i` old

change :: (state -> state) -> Transition state state
change f = W_I_I_II `ha` U_I_UU_II_III `i` \old -> These `i` f old `i` old

modify :: (state -> state) -> Transition state state
modify f = W_I_I_II `ha` U_I_UU_II_III `i` \old -> These `i` f old `i` f old

auto :: Automation e e e
auto = U_I_UU_II_III `i` \e -> e `lm` e

leaf :: forall t e .
	Monoidal Straight Functor (->) LM ML t =>
	e -> Recursive (U_I_T_II t LM e)
leaf x = Recursive `ha` U_I_T_II `ha` These x `yii` empty `yo` absurd

top :: forall tt t e .
 (tt ~ Construction t) =>
 Reference (Construction t e) e e
top = U_I_UU_III_U_II_I /
 \(R_U_I_T_I (Recursive (U_I_T_II (These old xs))))
  -> old `lm` (\new -> Root new xs)

sub :: forall tt t e .
 (tt ~ Construction t) =>
 Covariant Endo Semi Functor (->) t =>
 Reference (Construction t e) (t (Construction t e)) (t (Construction t e))
sub = U_I_UU_III_U_II_I /
 \(R_U_I_T_I (Recursive (U_I_T_II (These x old)))) -> These
  (wrap @(R_U_I_T_I _ _ _) `fo` old)
  (\new -> Root x `yii` new `yo` unwrap @Arrow @(R_U_I_T_I _ _ _))

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
joint = wrap @((f `T_TT_I` g) e) `ho` component @Straight @(->) @(->) @(f `T_TT_I` g) @(f `JT` g) @e

try :: forall t e o .
 Covariant Endo Semi Functor (->) t =>
 Component Natural (->) (->) (t `T_TT_I` Progress e) (t `JT` Progress e) =>
 Castable Opposite (->) ((t `T_TT_I` Progress e) e) =>
 t (Progress e o) -> t `JT` Progress e `TI` o
try = wrap @((t `T_TT_I` Progress e) _) `ho` component @Straight @(->) @(->)

label :: forall l t e . t e -> T_'_I l t e
label = T_'_I

forever ::
 Component Natural (->) (->) (t `T_TT_I` t) t =>
 t e -> t e
forever x = x `yukl` forever x

until ::
 Component Natural (->) (->) (t `T_TT_I` t) t =>
 Monoidal Straight Functor (->) LM LM t =>
 t (U_I_II ML e ee) -> t ee
until x = x `yokl` until x `u` but `rf'`yu enter

transform :: forall tt t e .
 Component Straight (->) (->) t tt =>
 t e -> tt e
transform = component @Straight @Arrow

pass ::
 Covariant Endo Semi Functor (->) t =>
 t e -> t ()
pass x = x `yu` ()

same :: Setoid e => e `ARR` e `ARR` e `LM` e `ML`  e
same = e

rep :: forall t e .
 Setoid (Representation t) =>
 Covariant (Representable (->)) (->) (->) t =>
 Representation t `ARR` Attribute `TI` t e `TI` e
rep index = W_I_II_II `ha` U_I_UU_III_U_II_I `yi` \origin ->
 let idx = map @U_I_II @U_I_II @Arrow @Arrow @t @(U_I_II (->) (Representation t)) identity in
 let tbt = map @U_I_II @U_I_II @Arrow @Arrow @(U_I_II (->) (Representation t)) @t identity in
 (idx origin `yi'` index) `yi_lm` (\x -> tbt (U_I_II / \index' -> (but `yii` idx origin `yi'` index') `rf` but x `yi` (index' `e` index)))
