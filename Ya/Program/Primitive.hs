{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE UndecidableInstances #-}
module Ya.Program.Primitive where

import Ya.Algebra

this :: e `LM` ee -> e
this (These x _) = x

that :: e `LM` ee -> ee
that (These _ x) = x

constant :: e -> ee -> e
constant x _ = x

type Only = I
pattern Only :: e -> Only e
pattern Only e <- I e where Only e = I e

type Singular = I
pattern Singular :: e -> Singular e
pattern Singular e <- I e where Singular e = I e

type Focused = I
pattern Focused :: e -> Focused e
pattern Focused e <- I e where Focused e = I e

type Boolean = Straight ML Unit Unit
pattern False, True :: Boolean
pattern False <- Straight (This Unit) where False = Straight (This Unit)
pattern True <- Straight (That Unit) where True = Straight (That Unit)

type Provided = Straight (->)

provide :: Straight (->) e e
provide = Straight identity

type Optional = Straight ML Unit

pattern Some :: e -> Optional e
pattern Some e <- Straight (That e) where Some e = Straight (That e)

pattern None :: Optional e
pattern None <- Straight (This Unit) where None = Straight (This Unit)

pattern Optionally :: Unit `ML` e -> Optional e
pattern Optionally e <- Straight e where Optionally e = Straight e

type Halting = Straight ML Unit

type Haltable t = JT t Halting

type Progress = Straight ML

pattern Interrupt :: e -> Progress e ee
pattern Interrupt e <- Straight (This e) where Interrupt e = Straight (This e)

pattern Continue :: ee -> Progress e ee
pattern Continue ee <- Straight (That ee) where Continue ee = Straight (That ee)

type Errorful = Straight ML

pattern Error :: e -> Errorful e ee
pattern Error e <- Straight (This e) where Error e = Straight (This e)

pattern Ok :: ee -> Errorful e ee
pattern Ok ee <- Straight (That ee) where Ok ee = Straight (That ee)

type Reference = U_I_UU_III_U_II_I (->) LM

type Attribute = W_I_II_II Reference

inspect ::
	Castable Straight Arrow (Reference origin target target) =>
	Castable Straight Arrow (Attribute origin target) =>
	Attribute origin target -> (origin -> target)
inspect r s = let (These qt _) = r `rw_rw` s in qt

adjust ::
	Castable Straight Arrow (Reference origin target target) =>
	Castable Straight Arrow (Attribute origin target) =>
	Attribute origin target -> (target -> target) -> (origin -> origin)
adjust attr f s = let (These h x) = attr `rw_rw` s in x `i`f h

-- TODO: should be moved later
-- instance Mapping Straight Straight Attribute Attribute (Construction t) (t `T_TT_I` Construction t)
	-- where mapping = rewrap `compose` rewrap `compose` rewrap / \from (Construct x xs) -> These 
		-- ((T_TT_I / wrap @Arrow @(R_U_I_T_I _ _ _) `fo` xs) `yo` from `o` (\(These y _) -> y))
		-- (\new -> Construct x (unwrap @Arrow @(R_U_I_T_I _ _ _) `fo` unwrap new) `yo` from `o` (\(These _ y) -> y))

instance Covariant Endo Semi Functor (->) t =>
	Mapping Straight Straight (->) (->) (Construction t) (t `T_TT_I` Construction t) where
	mapping = rewrap / \ from (Construct _ xs) ->
		(T_TT_I / xs `yo` wrap @Arrow @(R_U_I_T_I _ _ _)) `yo` from

type Transition = W_I_I_II (U_I_UU_II_III (->) LM)

observe :: Transition state state
observe = W_I_I_II `i_i` U_I_UU_II_III `i` \old -> These `i` old `i_i` old

replace :: state -> Transition state state
replace new = W_I_I_II `i_i` U_I_UU_II_III `i` \old -> These new old

transit :: (state -> state) -> Transition state state
transit f = W_I_I_II `i_i` U_I_UU_II_III `i` \s -> These `i` f s `i_i` s

start :: state -> Transition state result -> state `LM` result
start state stateful = stateful `rw_rw` state

instant :: Transition state result -> state -> state
instant state x = wrapped (left @Straight @Arrow identity) / state `rw_rw` x

type Stateful = Straight Transition

type Statefully state = JT (Stateful state)

pattern Stateful :: Transition state result -> Stateful state result
pattern Stateful x <- Straight x where Stateful x = Straight x

statefully ::
	Covariant Endo Semi Functor (->) t =>
	e -> JT (Stateful e) t o -> t (e `LM` o)
statefully state x = unwrap (unwrap x) state `yo` unwrap

type Scenario = Opposite Transition

pattern Scenario :: Transition state result -> Scenario result state
pattern Scenario x <- Opposite x where Scenario x = Opposite x

type Construction = R_U_I_T_I LM

pattern Construct :: i -> t (Recursive (U_I_T_II t LM i)) -> Construction t i
pattern Construct x xs <- R_U_I_T_I (Recursive (U_I_T_II (These x xs))) where Construct x xs = R_U_I_T_I (Recursive (U_I_T_II (These x xs)))

pattern Yet :: i -> t (Recursive (U_I_T_II t LM i)) -> Recursive (U_I_T_II t LM i)
pattern Yet x xs <- Recursive (U_I_T_II (These x xs)) where Yet x xs = Recursive (U_I_T_II (These x xs))

type Instruction = R_U_I_T_I ML

pattern Instruct :: t (Recursive (U_I_T_II t ML i)) -> Instruction t i
pattern Instruct xs <- R_U_I_T_I (Recursive (U_I_T_II (That xs))) where Instruct xs = R_U_I_T_I (Recursive (U_I_T_II (That xs)))

pattern Load :: item -> Instruction f item
pattern Load x <- R_U_I_T_I (Recursive (U_I_T_II (This x)))

type List = Optional `T_TT_I` Construction Optional

pattern List :: Recursive (U_I_T_II Optional LM i) -> List i
pattern List xs <- T_TT_I (Some (R_U_I_T_I xs)) where List xs = T_TT_I (Some (R_U_I_T_I xs))

pattern Next :: i -> Recursive (U_I_T_II Optional LM i) -> Recursive (U_I_T_II Optional LM i)
pattern Next x xs <- Yet x (Some xs) where Next x xs = Yet x (Some xs)

pattern Last :: i -> Recursive (U_I_T_II Optional LM i)
pattern Last x <- Yet x None where Last x = Yet x None

type family Brancher datastructure where
	Brancher (T_TT_I t (Construction t)) = t

type family Nonempty datastructure where
	Nonempty (T_TT_I Optional (Construction Optional)) = Construction Optional

pattern Nonempty :: forall t i . Recursive (U_I_T_II (Brancher t) LM i) -> Construction (Brancher t) i
pattern Nonempty xs <- R_U_I_T_I xs where Nonempty xs = R_U_I_T_I xs

pattern Empty :: forall t i . (Brancher t ~ Optional)
	=> T_TT_I Optional (Construction Optional) i
pattern Empty <- T_TT_I None where Empty = T_TT_I None

type Tree = Construction

type family Binary tree where
	Binary Tree = Tree (U_I_I LM `T_TT_I` Optional)

engage :: forall t e . Monoidal Straight Functor (->) LM LM t => e -> t e
engage x = enter `yu` x

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
	f (g e) -> (f `JT` g) e
joint = wrap @(->) @((f `T_TT_I` g) e)
	`o` component @Straight @(->) @(->) @(f `T_TT_I` g) @(f `JT` g) @e

try :: forall t e o .
	Covariant Endo Semi Functor (->) t =>
	Component Natural (->) (->) (t `T_TT_I` Progress e) (t `JT` Progress e) =>
	Castable Opposite (->) ((t `T_TT_I` Progress e) e) =>
	t (Progress e o) -> (t `JT` Progress e) o
try = wrap @(->) @((t `T_TT_I` Progress e) _)
	`o` component @Straight @(->) @(->) @(t `T_TT_I` Progress e) @(t `JT` Progress e)

type Horizontal = ML Unit Unit
pattern Back, Forth :: Horizontal
pattern Back <- This Unit where Back = This Unit
pattern Forth <- That Unit where Forth = That Unit

label :: forall l t e . t e -> T_'_I l t e
label = T_'_I

type Decision = ML Unit Unit
pattern No, Yes :: Decision
pattern No <- This Unit where No = This Unit
pattern Yes <- That Unit where Yes = That Unit

type Side = ML Unit Unit
pattern Left, Right :: Side
pattern Left <- This Unit where Left = This Unit
pattern Right <- That Unit where Right = That Unit

type Vertical = ML Unit Unit
pattern Down, Up :: Vertical
pattern Down <- This Unit where Down = This Unit
pattern Up <- That Unit where Up = That Unit

forever ::
	Component Natural (->) (->) (t `T_TT_I` t) t =>
	t e -> t e
forever x = x `yukl` forever x

until ::
	Component Natural (->) (->) (t `T_TT_I` t) t =>
	Monoidal Straight Functor (->) LM LM t =>
	t (That ML e ee) -> t ee
until x = x `yokl` \case
	Straight (This _) -> until x
	Straight (That e) -> enter `yu` e
