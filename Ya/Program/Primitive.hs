{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE UndecidableInstances #-}
module Ya.Program.Primitive where

import Ya.Algebra

is :: e `ARR` e
is = identity

on :: forall t e . t e `ARR` t e
on = identity

type Same e = e

pattern Same :: e -> Same e
pattern Same e = e

type Only = Identity

pattern Only :: e -> Only e
pattern Only e <- Identity e
	where Only e = Identity e

{-# COMPLETE Only #-}

type Singular = Identity

pattern Singular :: e -> Singular e
pattern Singular e <- Identity e
	where Singular e = Identity e

{-# COMPLETE Singular #-}

type Focused = Identity

pattern Focused :: e -> Focused e
pattern Focused e <- Identity e
	where Focused e = Identity e

{-# COMPLETE Focused #-}

type Boolean = Straight ML () ()

pattern False :: () -> Boolean
pattern False e = Straight (This e)

pattern True :: () -> Boolean
pattern True e = Straight (That e)

not :: e `ML` ee `ARR` ee `ML` e
not = That `rf` This

{-# COMPLETE False, True #-}

pattern Selfsame :: e `ARR` Error (ee `LM` ee) e
pattern Selfsame e = U_I_II (That e)

type Provided = Straight (->)

provide :: Straight (->) e e
provide = Straight identity

type Optional = Straight ML ()

pattern None :: () -> Optional e
pattern None e = Straight (This e)

pattern Some :: e -> Optional e
pattern Some e = Straight (That e)

{-# COMPLETE Some, None #-}

pattern Optionally :: () `ML` e -> Optional e
pattern Optionally e <- Straight e where Optionally e = Straight e

{-# COMPLETE Optionally #-}

type Halts = Straight ML ()

type Haltable t = JT t Halts

type Progress = Straight ML

pattern Interrupt :: e -> Progress e ee
pattern Interrupt e <- Straight (This e) where Interrupt e = Straight (This e)

pattern Continue :: ee -> Progress e ee
pattern Continue ee <- Straight (That ee) where Continue ee = Straight (That ee)

{-# COMPLETE Interrupt, Continue #-}

type Error = Straight ML

pattern Error :: e -> Error e ee
pattern Error e <- Straight (This e) where Error e = Straight (This e)

pattern Valid :: ee -> Error e ee
pattern Valid ee <- Straight (That ee) where Valid ee = Straight (That ee)

pattern Ok :: ee -> Error e ee
pattern Ok ee <- Straight (That ee) where Ok ee = Straight (That ee)

{-# COMPLETE Error, Ok #-}

type Probably = Straight ML

type Reference = U_I_UU_III_U_II_I (->) LM

type Attribute = W_I_II_II Reference

inspect ::
	Castable Straight Arrow (Reference origin target target) =>
	Castable Straight Arrow (Attribute origin target) =>
	Attribute origin target -> (origin -> target)
inspect r s = let (These qt _) = r `yi'_yi'` s in qt

adjust ::
	Castable Straight Arrow (Reference origin target target) =>
	Castable Straight Arrow (Attribute origin target) =>
	Attribute origin target -> (target -> target) -> (origin -> origin)
adjust attr f s = let (These h x) = attr `yi'_yi'` s in x `i`f h

-- TODO: should be moved later
-- instance Mapping Straight Straight Attribute Attribute (Construction t) (t `T_TT_I` Construction t)
	-- where mapping = rewrap `compose` rewrap `compose` rewrap / \from (Construct x xs) -> These 
		-- ((T_TT_I / wrap @Arrow @(R_U_I_T_I _ _ _) `fo` xs) `yo` from `o` (\(These y _) -> y))
		-- (\new -> Construct x (unwrap @Arrow @(R_U_I_T_I _ _ _) `fo` unwrap new) `yo` from `o` (\(These _ y) -> y))

type Automation = U_I_UU_II_III (->) LM

type Transition = W_I_I_II Automation

pattern Transition :: Automation state state result -> Transition state result
pattern Transition x = W_I_I_II x

review :: Transition state state
review = W_I_I_II `a` U_I_UU_II_III `i` \old -> These `i` old `i` old

switch :: state -> Transition state state
switch new = W_I_I_II `a` U_I_UU_II_III `i` \old -> These `i` new `i` old

put :: state -> Transition state state
put new = W_I_I_II `a` U_I_UU_II_III `i` \old -> These `i` new `i` old

change :: (state -> state) -> Transition state state
change f = W_I_I_II `a` U_I_UU_II_III `i` \old -> These `i` f old `i` old

modify :: (state -> state) -> Transition state state
modify f = W_I_I_II `a` U_I_UU_II_III `i` \old -> These `i` f old `i` f old

type State = Straight Transition

pattern State :: Transition state result -> State state result
pattern State x = U_I_II x

statefully ::
	Covariant Endo Semi Functor (->) t =>
	e -> JT (State e) t o -> t (e `LM` o)
statefully state x = unwrap @Arrow (unwrap @Arrow x) state `yo` unwrap @Arrow

type Construction = R_U_I_T_I LM

pattern Construct :: Recursive (U_I_T_II t LM i) -> Construction t i
pattern Construct xs = R_U_I_T_I xs

pattern Root :: i -> t (Recursive (U_I_T_II t LM i)) -> Construction t i
pattern Root x xs <- R_U_I_T_I (Recursive (U_I_T_II (These x xs)))
	where Root x xs = R_U_I_T_I (Recursive (U_I_T_II (These x xs)))

{-# COMPLETE Root #-}

pattern Node :: i -> t (Recursive (U_I_T_II t LM i)) -> Recursive (U_I_T_II t LM i)
pattern Node x xs <- Recursive (U_I_T_II (These x xs))
	where Node x xs = Recursive (U_I_T_II (These x xs))

{-# COMPLETE Node #-}

leaf :: forall t e .
	Monoidal Straight Functor (->) LM ML t =>
	e -> Recursive (U_I_T_II t LM e)
leaf x = Recursive `a` U_I_T_II `a` These x `yii` empty `yo` absurd

-- TODO: maybe it should be a Reference, not an Attribute?
top :: forall tt t e .
	(tt ~ Construction t) =>
	Attribute (Construction t e) e
top = W_I_II_II `compose` U_I_UU_III_U_II_I /
	\(Root old xs) -> These / old / \new -> Root new xs

-- TODO: maybe it should be a Reference, not an Attribute?
subs :: forall tt t e .
	(tt ~ Construction t) =>
	Covariant Endo Semi Functor (->) t =>
	Attribute (Construction t e) (t (Construction t e))
subs = W_I_II_II `compose` U_I_UU_III_U_II_I /
	\(Root x old) -> These
		(wrap @(R_U_I_T_I _ _ _) `fo` old)
		(\new -> Root x / unwrap @Arrow @(R_U_I_T_I _ _ _) `fo` new)

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

pattern List :: Optional (Construction Optional i) -> List i
pattern List xs = T_TT_I xs

{-# COMPLETE List #-}

pattern Next :: i -> Recursive (U_I_T_II Optional LM i) -> Recursive (U_I_T_II Optional LM i)
pattern Next x xs <- Yet x (Some xs) where Next x xs = Yet x (Some xs)

pattern Last :: i -> Recursive (U_I_T_II Optional LM i)
pattern Last x <- Yet x (None ()) where Last x = Yet x (None ())

{-# COMPLETE Next, Last #-}

type family Brancher datastructure where
 Brancher (T_TT_I t (Construction t)) = t

type family Nonempty datastructure where
 Nonempty (T_TT_I Optional (Construction Optional)) = Construction Optional

pattern Nonempty :: forall t i . Construction (Brancher t) i -> Construction (Brancher t) i
pattern Nonempty xs = xs

pattern Empty :: forall t i . (Brancher t ~ Optional)
 => () -> T_TT_I Optional (Construction Optional) i
pattern Empty e <- T_TT_I (None e) where Empty e = T_TT_I (None e)

type Tree = Construction

type family Binary t where
 Binary t = t (U_I_I LM `T_TT_I` Optional)

pattern Binary xs = T_TT_I (U_I_I xs)

type family Forest tree where
	Forest (Construction t) = t `T_TT_I` Construction t

type Stream = Construction Only

pattern Stream :: Stream i -> Stream i
pattern Stream xs = xs

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
	f (g e) -> (f `JT` g) e
joint = wrap @((f `T_TT_I` g) e)
	`o` component @Straight @(->) @(->) @(f `T_TT_I` g) @(f `JT` g) @e

try :: forall t e o .
	Covariant Endo Semi Functor (->) t =>
	Component Natural (->) (->) (t `T_TT_I` Progress e) (t `JT` Progress e) =>
	Castable Opposite (->) ((t `T_TT_I` Progress e) e) =>
	t (Progress e o) -> (t `JT` Progress e) o
try = wrap @((t `T_TT_I` Progress e) _)
	`o` component @Straight @(->) @(->) @(t `T_TT_I` Progress e) @(t `JT` Progress e)

type Way = ML () ()

pattern Backwards :: Way
pattern Backwards <- This ()
	where Backwards = This ()

pattern Forwards :: Way
pattern Forwards <- That ()
	where Forwards = That ()

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

transform :: forall tt t e .
	Component Straight (->) (->) t tt =>
	t e -> tt e
transform = component @Straight @Arrow

pass ::
	Covariant Endo Semi Functor (->) t =>
	t e -> t ()
pass x = x `yu` ()

same :: Setoid e => e `ARR` e `ARR` U_I_II ML (e `LM` e) e
same = e

type Cascading = Labeled (Straight LM () ())

pattern Cascading :: t e -> Cascading t e
pattern Cascading e = T_'_I e

rep :: forall t e .
 Setoid (Representation t) =>
 Covariant (Representable (->)) (->) (->) t =>
 Representation t `ARR` Attribute `TI` t e `TI` e
rep index = W_I_II_II `a` U_I_UU_III_U_II_I `yi` \origin ->
 let idx = map @U_I_II @U_I_II @Arrow @Arrow @t @(U_I_II (->) (Representation t)) identity in
 let tbt = map @U_I_II @U_I_II @Arrow @Arrow @(U_I_II (->) (Representation t)) @t identity in
 These (idx origin `yi'` index) (\x -> tbt (U_I_II / \index' -> (but `yii` idx origin `yi'` index') `rf` but x `yi` index' `e` index))
