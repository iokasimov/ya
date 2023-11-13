{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE UndecidableInstances #-}
module Ya.Program.Primitive where

import Ya.Algebra

type Only = I

pattern Only :: i -> Only i
pattern Only i <- I i
	where Only i = I i

type Boolean = U_I_II (\/) Unit Unit

pattern False :: Boolean
pattern False <- U_I_II (This Unit)
	where False = U_I_II (This Unit)

pattern True :: Boolean
pattern True <- U_I_II (That Unit)
	where True = U_I_II (That Unit)

type Optional = U_I_II (\/) Unit

pattern Some :: e -> Optional e
pattern Some e <- U_I_II (That e)
	where Some e = U_I_II (That e)

pattern None :: Optional e
pattern None <- U_I_II (This Unit)
	where None = U_I_II (This Unit)

pattern Optionally :: Unit \/ e -> Optional e
pattern Optionally e <- U_I_II e
	where Optionally e = U_I_II e

type Progress = U_I_II (\/)

pattern Interrupt :: e -> Progress e ee
pattern Interrupt e <- U_I_II (This e)
	where Interrupt e = U_I_II (This e)

pattern Continue :: ee -> Progress e ee
pattern Continue ee <- U_I_II (That ee)
	where Continue ee = U_I_II (That ee)

type Reference = U_I_UU_III_U_II_I (->) (/\)

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
-- instance Mapping Straight Straight Attribute Attribute (Construction t) (t `T_TT_I` Construction t)
	-- where mapping = rewrap `compose` rewrap `compose` rewrap / \from (Construct x xs) -> These 
		-- ((T_TT_I / wrap @Arrow @(R_U_I_T_I _ _ _) `fo` xs) `yo` from `o` (\(These y _) -> y))
		-- (\new -> Construct x (unwrap @Arrow @(R_U_I_T_I _ _ _) `fo` unwrap new) `yo` from `o` (\(These _ y) -> y))

instance Covariant Endo Semi Functor (->) t =>
	Mapping Straight Straight (->) (->) (Construction t) (t `T_TT_I` Construction t) where
	mapping = rewrap / \ from (Construct x xs) ->
		(T_TT_I / xs `yo` wrap @Arrow @(R_U_I_T_I _ _ _)) `yo` from

type Transition = W_I_I_II (U_I_UU_II_III (->) (/\))

observe :: Transition state state
observe = W_I_I_II `i'i` U_I_UU_II_III `i` \old -> These `i` old `i'i` old

replace :: state -> Transition state state
replace new = W_I_I_II `i'i` U_I_UU_II_III `i` \old -> These new old

transit :: (state -> state) -> Transition state state
transit f = W_I_I_II `i'i` U_I_UU_II_III `i` \s -> These `i` f s `i'i` s

start :: state -> Transition state result -> state /\ result
start state stateful = stateful `uw'uw` state

instant :: Transition state result -> state -> state
instant state x = wrapped (this @Straight @Arrow identity) / state `uw'uw` x

type Stateful = U_I_II Transition

pattern Statefully :: Transition state result -> Stateful state result
pattern Statefully x <- U_I_II x
	where Statefully x = U_I_II x

statefully ::
	Covariant Endo Semi Functor (->) t =>
	e -> J (Stateful e) t o -> t (e /\ o)
statefully state x = unwrap (unwrap x) state `yo` unwrap

type Scenario = U_II_I Transition

pattern Scenario :: Transition state result -> Scenario result state
pattern Scenario x <- U_II_I x
	where Scenario x = U_II_I x

type Construction = R_U_I_T_I (/\)

pattern Construct :: i -> t (Recursive (U_I_T_II t (/\) i)) -> Construction t i
pattern Construct x xs <- R_U_I_T_I (Recursive (U_I_T_II (These x xs)))
	where Construct x xs = R_U_I_T_I (Recursive (U_I_T_II (These x xs)))

pattern Yet :: i -> t (Recursive (U_I_T_II t (/\) i)) -> Recursive (U_I_T_II t (/\) i)
pattern Yet x xs <- Recursive (U_I_T_II (These x xs))
	where Yet x xs = Recursive (U_I_T_II (These x xs))

type Instruction = R_U_I_T_I (\/)

pattern Instruct :: t (Recursive (U_I_T_II t (\/) i)) -> Instruction t i
pattern Instruct xs <- R_U_I_T_I (Recursive (U_I_T_II (That xs)))
	where Instruct xs = R_U_I_T_I (Recursive (U_I_T_II (That xs)))

pattern Load :: item -> Instruction f item
pattern Load x <- R_U_I_T_I (Recursive (U_I_T_II (This x)))

type List = Optional `T_TT_I` Construction Optional

pattern List :: Recursive (U_I_T_II Optional (/\) i) -> List i
pattern List xs <- T_TT_I (Some (R_U_I_T_I xs))
	where List xs = T_TT_I (Some (R_U_I_T_I xs))

pattern Next :: i -> Recursive (U_I_T_II Optional (/\) i) -> Recursive (U_I_T_II Optional (/\) i)
pattern Next x xs <- Yet x (Some xs)
	where Next x xs = Yet x (Some xs)

pattern Last :: i -> Recursive (U_I_T_II Optional (/\) i)
pattern Last x <- Yet x None
	where Last x = Yet x None

type family Brancher datastructure where
	Brancher (T_TT_I t (Construction t)) = t

type family Nonempty datastructure where
	Nonempty (T_TT_I Optional (Construction Optional)) = Construction Optional

pattern Nonempty :: forall t i . Recursive (U_I_T_II (Brancher t) (/\) i) -> Construction (Brancher t) i
pattern Nonempty xs <- R_U_I_T_I xs
	where Nonempty xs = R_U_I_T_I xs

pattern Empty :: forall t i . (Brancher t ~ Optional)
	=> T_TT_I Optional (Construction Optional) i
pattern Empty <- T_TT_I None
	where Empty = T_TT_I None

type Tree = Construction

type family Binary tree where
	Binary Tree = Tree (U_I_I (/\) `T_TT_I` Optional)

type family J known unknown where
	J (Straight Arrow input) unknown = Straight Arrow input `T_TT_I` unknown
	J (Straight Transition state) unknown = T_TT_TTT_I (Straight Arrow state) unknown (Straight (/\) state)
	-- TODO: is there a loop if we cannot find such an instance?
	-- J unknown known = J known unknown

layer :: forall g f e .
	Component Natural (->) (->) f (f `J` g) =>
	f e -> (f `J` g) e
layer = component @Straight @(->) @(->) @f @(f `J` g) @e

embed :: forall f g e .
	Component Natural (->) (->) g (f `J` g) =>
	g e -> (f `J` g) e
embed = component @Straight @(->) @(->) @g @(f `J` g) @e

joint :: forall f g e .
	Component Natural (->) (->) (f `T_TT_I` g) (f `J` g) =>
	Castable Opposite (->) ((f `T_TT_I` g) e) =>
	f (g e) -> (f `J` g) e
joint = component @Straight @(->) @(->) @(f `T_TT_I` g) @(f `J` g) @e
	`compose` wrap @(->) @((f `T_TT_I` g) e)

try :: forall f ee e .
	Component Natural (->) (->) (f `T_TT_I` Progress ee) (f `J` Progress ee) =>
	Castable Opposite (->) ((f `T_TT_I` Progress ee) e) =>
	(->) (f (Progress ee e)) ((f `J` Progress ee) e)
try = component @Straight @(->) @(->) @(f `T_TT_I` Progress ee) @(f `J` Progress ee) @e
	`compose` wrap @(->) @((f `T_TT_I` (Progress ee)) e)

type Horizontal = U_I_II (\/) Unit Unit

pattern Backward :: Horizontal
pattern Backward <- U_I_II (This Unit)
	where Backward = U_I_II (This Unit)

pattern Forward :: Horizontal
pattern Forward <- U_I_II (That Unit)
	where Forward = U_I_II (That Unit)

type Side = (\/) Unit Unit

pattern Left :: Side
pattern Left <- This Unit
	where Left = This Unit

pattern Right :: Side
pattern Right <- That Unit
	where Right = That Unit