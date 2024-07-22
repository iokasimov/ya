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

pattern Only e = Identity e

type Singular = Identity

pattern Singular e = Identity e

type Focused = Identity

pattern Focused e = Identity e

type Boolean = Straight ML () ()

pattern Boolean e = U_I_II e

pattern False x = U_I_II (This x)
pattern True x = U_I_II (That x)

not :: e `ML` ee `ARR` ee `ML` e
not = That `rf` This

pattern Selfsame x = U_I_II (That x)

type Provided = U_I_II (->)

provide :: U_I_II (->) e e
provide = U_I_II identity

type Optional = U_I_II ML ()

pattern None x = U_I_II (This x)
pattern Some x = U_I_II (That x)

{-# COMPLETE Some, None #-}

pattern Optionally x = U_I_II x

{-# COMPLETE Optionally #-}

type Halts = U_I_II ML ()

type Maybe = U_I_II ML ()

pattern Maybe x = U_I_II @ML @() x

type Haltable t = JT t Halts

type Progress = U_I_II ML

pattern Progress x = U_I_II @ML x
pattern Interrupt x = U_I_II @ML (This x)
pattern Continue x = U_I_II @ML (That x)

type Error = U_I_II ML

pattern Error x = U_I_II (This x)
pattern Valid x = U_I_II (That x)
pattern Ok x = U_I_II (That x)

type Probably = U_I_II ML

pattern Probably x = U_I_II @ML x

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

type State = U_I_II Transition

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
pattern Yet x xs = Recursive (U_I_T_II (These x xs))

type Instruction = R_U_I_T_I ML

pattern Instruct xs = R_U_I_T_I (Recursive (U_I_T_II (That xs)))

pattern Load x = R_U_I_T_I (Recursive (U_I_T_II (This x)))

type List = Optional `T_TT_I` Construction Optional

pattern List xs = T_TT_I @Optional @(Construction Optional) xs

pattern Last x    = Recursive (U_I_T_II (These x (None ())))
pattern Next x xs = Recursive (U_I_T_II (These x (Some xs)))

type family Brancher datastructure where
 Brancher (T_TT_I t (Construction t)) = t

type family Nonempty datastructure where
 Nonempty (T_TT_I Optional (Construction Optional)) = Construction Optional

pattern Nonempty :: forall t i . Construction (Brancher t) i -> Construction (Brancher t) i
pattern Nonempty xs = xs

pattern Empty :: forall t e . (Brancher t ~ Optional)
 => () -> T_TT_I Optional (Construction Optional) e
pattern Empty x = T_TT_I (None x)

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
 f (g e) -> f `JT` g `TI` e
joint = wrap @((f `T_TT_I` g) e) `o` component @Straight @(->) @(->) @(f `T_TT_I` g) @(f `JT` g) @e

try :: forall t e o .
 Covariant Endo Semi Functor (->) t =>
 Component Natural (->) (->) (t `T_TT_I` Progress e) (t `JT` Progress e) =>
 Castable Opposite (->) ((t `T_TT_I` Progress e) e) =>
 t (Progress e o) -> t `JT` Progress e `TI` o
try = wrap @((t `T_TT_I` Progress e) _) `o` component @Straight @(->) @(->)

type Way = ML () ()

pattern Backwards x = This x
pattern Forwards x = That x

pattern Passed x = This x
pattern Future x = That x

type Decision = ML () ()

pattern No x = This x
pattern Yes x = That x

type Side = ML () ()

pattern Left x = This x
pattern Right x = That x

type Vertical = ML () ()

pattern Down x = This x
pattern Up x = That x

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
 These
  (idx origin `yi'` index)
  (\x -> tbt (U_I_II / \index' ->
    (but `yii` idx origin `yi'` index')
    `rf` but x
    `yi` (index' `e` index)))
