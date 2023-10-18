{-# LANGUAGE AllowAmbiguousTypes #-}
module Ya.Program.Primitive where

import Ya.Algebra

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
	Castable Flat Arrow (Reference origin target target) =>
	Castable Flat Arrow (Attribute origin target) =>
	Attribute origin target -> (origin -> target)
inspect r s = let (These qt _) = r `u'u` s in qt

adjust ::
	Castable Flat Arrow (Reference origin target target) =>
	Castable Flat Arrow (Attribute origin target) =>
	Attribute origin target -> (target -> target) -> (origin -> origin)
adjust attr f s = let (These h x) = attr `u'u` s in x `i`f h

type Transition = U_I_UU_II_III (->) (/\)

type State = W_I_I_II Transition

observe :: State state state
observe = W_I_I_II `ii` U_I_UU_II_III `i` \old -> These `i` old `ii` old

replace :: state -> State state state
replace new = W_I_I_II `ii` U_I_UU_II_III `i` \old -> These new old

transit :: (state -> state) -> State state state
transit f = W_I_I_II `ii` U_I_UU_II_III `i` \s -> These `i` f s `ii` s

start :: state -> State state result -> state /\ result
start state stateful = stateful `u'u` state

type Stateful = U_I_II State

pattern Statefully :: State state result -> Stateful state result
pattern Statefully x <- U_I_II x
	where Statefully x = U_I_II x

type Scenario = U_II_I State

pattern Scenario :: State state result -> Scenario result state
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

type List = T_TT_I Optional (Construction Optional)

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
	Binary Tree = Tree (U_T_I_TT_I (/\) Optional Optional)

type family Layered known unknown where
	Layered (U_I_II Arrow input) unknown =
		T_TT_I (U_I_II Arrow input) unknown
	Layered (U_I_II State state) unknown =
		T_TT_TTT_I (U_I_II Arrow state) unknown (U_I_II (/\) state)

layer :: forall g f into e .
	Component Natural Arrow into f (Layered f g) =>
	into (f e) (Layered f g e)
layer = component @Flat @Arrow @into @f @(Layered f g) @e

embed :: forall f g into e .
	Component Natural Arrow into g (Layered f g) =>
	into (g e) (Layered f g e)
embed = component @Flat @Arrow @into @g @(Layered f g) @e

joint :: forall f g into e .
	Component Natural Arrow into (f `T_TT_I` g) (Layered f g) =>
	Castable Dual into (T_TT_I f g e) =>
	into (f (g e)) (Layered f g e)
joint = component @Flat @Arrow @into @(f `T_TT_I` g) @(Layered f g) @e
	`compose` wrap @into @((f `T_TT_I` g) e)

try :: forall f into ee e .
	Component Natural Arrow into (f `T_TT_I` (Progress ee)) (Layered f (Progress ee)) =>
	Castable Dual into (T_TT_I f (Progress ee) e) =>
	into (f (Progress ee e)) (Layered f (Progress ee) e)
try = component @Flat @Arrow @into @(f `T_TT_I` Progress ee) @(Layered f (Progress ee)) @e
	`compose` wrap @into @((f `T_TT_I` (Progress ee)) e)
