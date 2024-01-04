{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE UndecidableInstances #-}
module Ya.Program.Primitive where

import Ya.Algebra

type Only = I

pattern Only :: e -> Only e
pattern Only e <- I e
	where Only e = I e

{-# COMPLETE Only #-}

type Singular = I

pattern Singular :: e -> Singular e
pattern Singular e <- I e
	where Singular e = I e

{-# COMPLETE Singular #-}

type Focused = I

pattern Focused :: e -> Focused e
pattern Focused e <- I e
	where Focused e = I e

{-# COMPLETE Focused #-}

type Boolean = Straight ML () ()

pattern False :: Boolean
pattern False <- Straight (This ())
	where False = Straight (This ())

pattern True :: Boolean
pattern True <- Straight (That ())
	where True = Straight (That ())

{-# COMPLETE False, True #-}

type Provided = Straight (->)

provide :: Straight (->) e e
provide = Straight identity

type Optional = Straight ML ()

pattern None :: Optional e
pattern None <- Straight (This ()) where None = Straight (This ())

pattern Some :: e -> Optional e
pattern Some e <- Straight (That e) where Some e = Straight (That e)

{-# COMPLETE Some, None #-}

pattern Optionally :: () `ML` e -> Optional e
pattern Optionally e <- Straight e where Optionally e = Straight e

{-# COMPLETE Optionally #-}

type Halting = Straight ML ()

type Haltable t = JT t Halting

type Progress = Straight ML

pattern Interrupt :: e -> Progress e ee
pattern Interrupt e <- Straight (This e) where Interrupt e = Straight (This e)

pattern Continue :: ee -> Progress e ee
pattern Continue ee <- Straight (That ee) where Continue ee = Straight (That ee)

{-# COMPLETE Interrupt, Continue #-}

type Errorful = Straight ML

pattern Error :: e -> Errorful e ee
pattern Error e <- Straight (This e) where Error e = Straight (This e)

pattern Ok :: ee -> Errorful e ee
pattern Ok ee <- Straight (That ee) where Ok ee = Straight (That ee)

{-# COMPLETE Error, Ok #-}

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

type Automata = W_I_I_II (U_I_UU_II_III (->) LM)

observe :: Automata state state
observe = W_I_I_II `i_i` U_I_UU_II_III `i` \old -> These `i` old `i_i` old

replace :: state -> Automata state state
replace new = W_I_I_II `i_i` U_I_UU_II_III `i` \old -> These new old

transit :: (state -> state) -> Automata state state
transit f = W_I_I_II `i_i` U_I_UU_II_III `i` \s -> These `i` f s `i_i` s

start :: state -> Automata state result -> state `LM` result
start state stateful = stateful `rw_rw` state

instant :: Automata state result -> state -> state
instant state x = wrapped (left @Straight @Arrow identity) / state `rw_rw` x

type Stateful = Straight Automata

type Statefully t state = JT (Stateful state) t

pattern Statefully :: Automata state result -> Stateful state result
pattern Statefully x <- Straight x where Statefully x = Straight x

{-# COMPLETE Statefully #-}

statefully ::
	Covariant Endo Semi Functor (->) t =>
	e -> JT (Stateful e) t o -> t (e `LM` o)
statefully state x = unwrap (unwrap x) state `yo` unwrap

type Transition = Opposite Automata

pattern Transition :: Automata state result -> Transition result state
pattern Transition x <- Opposite x where Transition x = Opposite x

{-# COMPLETE Transition #-}

type Construction = R_U_I_T_I LM

pattern Construct :: i -> t (Recursive (U_I_T_II t LM i)) -> Construction t i
pattern Construct x xs <- R_U_I_T_I (Recursive (U_I_T_II (These x xs)))
	where Construct x xs = R_U_I_T_I (Recursive (U_I_T_II (These x xs)))

{-# COMPLETE Construct #-}

-- TODO: maybe it should be a Reference, not an Attribute?
top :: forall tt t e .
	(tt ~ Construction t) =>
	Attribute (Construction t e) e
top = W_I_II_II `compose` U_I_UU_III_U_II_I /
	\(Construct old xs) -> These / old / \new -> Construct new xs

-- TODO: maybe it should be a Reference, not an Attribute?
sub :: forall tt t e .
	(tt ~ Construction t) =>
	Covariant Endo Semi Functor (->) t =>
	Attribute (Construction t e) (t (Construction t e))
sub = W_I_II_II `compose` U_I_UU_III_U_II_I /
	\(Construct x old) -> These
		(wrap @Arrow @(R_U_I_T_I _ _ _) `fo` old)
		(\new -> Construct x / rw @Arrow @(R_U_I_T_I _ _ _) `fo` new)

pattern Yet :: i -> t (Recursive (U_I_T_II t LM i)) -> Recursive (U_I_T_II t LM i)
pattern Yet x xs <- Recursive (U_I_T_II (These x xs))
	where Yet x xs = Recursive (U_I_T_II (These x xs))

{-# COMPLETE Yet #-}

type Instruction = R_U_I_T_I ML

pattern Instruct :: t (Recursive (U_I_T_II t ML i)) -> Instruction t i
pattern Instruct xs <- R_U_I_T_I (Recursive (U_I_T_II (That xs)))
	where Instruct xs = R_U_I_T_I (Recursive (U_I_T_II (That xs)))

pattern Load :: item -> Instruction f item
pattern Load x <- R_U_I_T_I (Recursive (U_I_T_II (This x)))

{-# COMPLETE Instruct, Load #-}

type List = Optional `T_TT_I` Construction Optional

pattern List :: Recursive (U_I_T_II Optional LM i) -> List i
pattern List xs <- T_TT_I (Some (R_U_I_T_I xs)) where List xs = T_TT_I (Some (R_U_I_T_I xs))

{-# COMPLETE List #-}

pattern Next :: i -> Recursive (U_I_T_II Optional LM i) -> Recursive (U_I_T_II Optional LM i)
pattern Next x xs <- Yet x (Some xs) where Next x xs = Yet x (Some xs)

pattern Last :: i -> Recursive (U_I_T_II Optional LM i)
pattern Last x <- Yet x None where Last x = Yet x None

{-# COMPLETE Next, Last #-}

type family Brancher datastructure where
	Brancher (T_TT_I t (Construction t)) = t

type family Nonempty datastructure where
	Nonempty (T_TT_I Optional (Construction Optional)) = Construction Optional

pattern Nonempty :: forall t i . Recursive (U_I_T_II (Brancher t) LM i) -> Construction (Brancher t) i
pattern Nonempty xs <- R_U_I_T_I xs where Nonempty xs = R_U_I_T_I xs

{-# COMPLETE Nonempty #-}

pattern Empty :: forall t i . (Brancher t ~ Optional)
	=> T_TT_I Optional (Construction Optional) i
pattern Empty <- T_TT_I None where Empty = T_TT_I None

type Tree = Construction

type Twice = T_TT_I (U_I_I LM)

type family Binary tree where
	Binary Tree = Tree (Twice Optional)

type family Forest tree where
	Forest (Construction t) = t `T_TT_I` Construction t

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

type Horizontal = ML () ()

pattern Back :: Horizontal
pattern Back <- This () 
	where Back = This ()

pattern Forth :: Horizontal
pattern Forth <- That ()
	where Forth = That ()

{-# COMPLETE Nonempty #-}

label :: forall l t e . t e -> T_'_I l t e
label = T_'_I

type Decision = ML () ()

pattern No :: Decision
pattern No <- This ()
	where No = This ()

pattern Yes :: Decision
pattern Yes <- That ()
	where Yes = That ()

type Side = ML () ()

pattern Left :: Side
pattern Left <- This ()
	where Left = This ()

pattern Right :: Side
pattern Right <- That ()
	where Right = That ()

type Vertical = ML () ()

pattern Down :: Vertical
pattern Down <- This ()
	where Down = This ()

pattern Up :: Vertical
pattern Up <- That ()
	where Up = That ()

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
