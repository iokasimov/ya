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
pattern Only e <- I e
	where Only e = I e

type Singular = I

pattern Singular :: e -> Singular e
pattern Singular e <- I e
	where Singular e = I e

type Boolean = U_I_II ML Unit Unit

pattern False :: Boolean
pattern False <- U_I_II (This Unit)
	where False = U_I_II (This Unit)

pattern True :: Boolean
pattern True <- U_I_II (That Unit)
	where True = U_I_II (That Unit)

type Provided = U_I_II (->)

provide :: Straight (->) e e
provide = U_I_II identity

type Optional = U_I_II ML Unit

pattern Some :: e -> Optional e
pattern Some e <- U_I_II (That e)
	where Some e = U_I_II (That e)

pattern None :: Optional e
pattern None <- U_I_II (This Unit)
	where None = U_I_II (This Unit)

pattern Optionally :: Unit `ML` e -> Optional e
pattern Optionally e <- U_I_II e
	where Optionally e = U_I_II e

type Progress = U_I_II ML

pattern Interrupt :: e -> Progress e ee
pattern Interrupt e <- U_I_II (This e)
	where Interrupt e = U_I_II (This e)

pattern Continue :: ee -> Progress e ee
pattern Continue ee <- U_I_II (That ee)
	where Continue ee = U_I_II (That ee)

type Reference = U_I_UU_III_U_II_I (->) LM

type Attribute = W_I_II_II Reference

inspect ::
	Castable Straight Arrow (Reference origin target target) =>
	Castable Straight Arrow (Attribute origin target) =>
	Attribute origin target -> (origin -> target)
inspect r s = let (These qt _) = r `uw'uw` s in qt

adjust ::
	Castable Straight Arrow (Reference origin target target) =>
	Castable Straight Arrow (Attribute origin target) =>
	Attribute origin target -> (target -> target) -> (origin -> origin)
adjust attr f s = let (These h x) = attr `uw'uw` s in x `i`f h

-- TODO: should be moved later
-- instance Mapping Straight Straight Attribute Attribute (Construction t) (t `T'TT'I` Construction t)
	-- where mapping = rewrap `compose` rewrap `compose` rewrap / \from (Construct x xs) -> These 
		-- ((T'TT'I / wrap @Arrow @(R_U_I_T_I _ _ _) `fo` xs) `yo` from `o` (\(These y _) -> y))
		-- (\new -> Construct x (unwrap @Arrow @(R_U_I_T_I _ _ _) `fo` unwrap new) `yo` from `o` (\(These _ y) -> y))

instance Covariant Endo Semi Functor (->) t =>
	Mapping Straight Straight (->) (->) (Construction t) (t `T'TT'I` Construction t) where
	mapping = rewrap / \ from (Construct _ xs) ->
		(T'TT'I / xs `yo` wrap @Arrow @(R_U_I_T_I _ _ _)) `yo` from

type Transition = W_I_I_II (U_I_UU_II_III (->) LM)

observe :: Transition state state
observe = W_I_I_II `i'i` U_I_UU_II_III `i` \old -> These `i` old `i'i` old

replace :: state -> Transition state state
replace new = W_I_I_II `i'i` U_I_UU_II_III `i` \old -> These new old

transit :: (state -> state) -> Transition state state
transit f = W_I_I_II `i'i` U_I_UU_II_III `i` \s -> These `i` f s `i'i` s

start :: state -> Transition state result -> state `LM` result
start state stateful = stateful `uw'uw` state

instant :: Transition state result -> state -> state
instant state x = wrapped (left @Straight @Arrow identity) / state `uw'uw` x

type Stateful = U_I_II Transition

pattern Statefully :: Transition state result -> Stateful state result
pattern Statefully x <- U_I_II x
	where Statefully x = U_I_II x

statefully ::
	Covariant Endo Semi Functor (->) t =>
	e -> J (Stateful e) t o -> t (e `LM` o)
statefully state x = unwrap (unwrap x) state `yo` unwrap

type Scenario = U_II_I Transition

pattern Scenario :: Transition state result -> Scenario result state
pattern Scenario x <- U_II_I x
	where Scenario x = U_II_I x

type Construction = R_U_I_T_I LM

pattern Construct :: i -> t (Recursive (U_I_T_II t LM i)) -> Construction t i
pattern Construct x xs <- R_U_I_T_I (Recursive (U_I_T_II (These x xs)))
	where Construct x xs = R_U_I_T_I (Recursive (U_I_T_II (These x xs)))

pattern Yet :: i -> t (Recursive (U_I_T_II t LM i)) -> Recursive (U_I_T_II t LM i)
pattern Yet x xs <- Recursive (U_I_T_II (These x xs))
	where Yet x xs = Recursive (U_I_T_II (These x xs))

type Instruction = R_U_I_T_I ML

pattern Instruct :: t (Recursive (U_I_T_II t ML i)) -> Instruction t i
pattern Instruct xs <- R_U_I_T_I (Recursive (U_I_T_II (That xs)))
	where Instruct xs = R_U_I_T_I (Recursive (U_I_T_II (That xs)))

pattern Load :: item -> Instruction f item
pattern Load x <- R_U_I_T_I (Recursive (U_I_T_II (This x)))

type List = Optional `T'TT'I` Construction Optional

pattern List :: Recursive (U_I_T_II Optional LM i) -> List i
pattern List xs <- T'TT'I (Some (R_U_I_T_I xs))
	where List xs = T'TT'I (Some (R_U_I_T_I xs))

pattern Next :: i -> Recursive (U_I_T_II Optional LM i) -> Recursive (U_I_T_II Optional LM i)
pattern Next x xs <- Yet x (Some xs)
	where Next x xs = Yet x (Some xs)

pattern Last :: i -> Recursive (U_I_T_II Optional LM i)
pattern Last x <- Yet x None
	where Last x = Yet x None

type family Brancher datastructure where
	Brancher (T'TT'I t (Construction t)) = t

type family Nonempty datastructure where
	Nonempty (T'TT'I Optional (Construction Optional)) = Construction Optional

pattern Nonempty :: forall t i . Recursive (U_I_T_II (Brancher t) LM i) -> Construction (Brancher t) i
pattern Nonempty xs <- R_U_I_T_I xs
	where Nonempty xs = R_U_I_T_I xs

pattern Empty :: forall t i . (Brancher t ~ Optional)
	=> T'TT'I Optional (Construction Optional) i
pattern Empty <- T'TT'I None
	where Empty = T'TT'I None

type Tree = Construction

type family Binary tree where
	Binary Tree = Tree (U_I_I LM `T'TT'I` Optional)

layer :: forall g f e .
	Component Natural (->) (->) f (f `J` g) =>
	f e -> (f `J` g) e
layer = component @Straight @(->) @(->) @f @(f `J` g) @e

embed :: forall f g e .
	Component Natural (->) (->) g (f `J` g) =>
	g e -> (f `J` g) e
embed = component @Straight @(->) @(->) @g @(f `J` g) @e

joint :: forall f g e .
	Component Natural (->) (->) (f `T'TT'I` g) (f `J` g) =>
	Castable Opposite (->) ((f `T'TT'I` g) e) =>
	f (g e) -> (f `J` g) e
joint = wrap @(->) @((f `T'TT'I` g) e)
	`o` component @Straight @(->) @(->) @(f `T'TT'I` g) @(f `J` g) @e

try :: forall t e ee o .
	Covariant Endo Semi Functor (->) t =>
	Component Natural (->) (->) (t `T'TT'I` Progress ee) (t `J` Progress ee) =>
	Castable Opposite (->) ((t `T'TT'I` Progress ee) ee) =>
	(e -> ee) -> t (Progress e o) -> (t `J` Progress ee) o
try f = (`yo` rewrap @(Progress ee _) (`yo_` f))
	`o` wrap @(->) @((t `T'TT'I` Progress ee) _)
	`o` component @Straight @(->) @(->) @(t `T'TT'I` Progress ee) @(t `J` Progress ee)

type Horizontal = ML Unit Unit

pattern Backward :: Horizontal
pattern Backward <- This Unit
	where Backward = This Unit

pattern Forward :: Horizontal
pattern Forward <- That Unit
	where Forward = That Unit

label :: forall l t e . t e -> T'_'I l t e
label = T'_'I

type Side = ML Unit Unit

pattern Left :: Side
pattern Left <- This Unit
	where Left = This Unit

pattern Right :: Side
pattern Right <- That Unit
	where Right = That Unit

type Vertical = ML Unit Unit

pattern Down :: Vertical
pattern Down <- This Unit
	where Down = This Unit

pattern Up :: Vertical
pattern Up <- That Unit
	where Up = That Unit

forever ::
	Component Natural (->) (->) (t `T'TT'I` t) t =>
	t e -> t e
forever x = x `yukl` forever x

until ::
	Component Natural (->) (->) (t `T'TT'I` t) t =>
	Monoidal Straight Functor (->) LM LM t =>
	t (That ML e ee) -> t ee
until x = x `yokl` \case
	U_I_II (This _) -> until x
	U_I_II (That e) -> enter `yu` e
