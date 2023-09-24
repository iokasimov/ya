{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE UndecidableInstances #-}
module Ya.Program where

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

type Stateful = W_I_I_II Transition

current :: Stateful state state
current = W_I_I_II `ii` U_I_UU_II_III `i` \old -> These `i` old `i` old

replace :: state -> Stateful state state
replace new = W_I_I_II `ii` U_I_UU_II_III `i` \old -> These new old

transit :: (state -> state) -> Stateful state state
transit f = W_I_I_II `ii` U_I_UU_II_III `i` \s -> These `i` f s `i` s

start :: state -> Stateful state result -> state /\ result
start state stateful = stateful `u'u` state

class Field x record where
	field :: Attribute record x

instance Field x x
	where field = identity

instance Field x (x /\ xs)
	where field = W_I_II_II `ii` U_I_UU_III_U_II_I
		`i` (\(These f fs) -> These `i` f `i` (\f' -> These f' fs))

instance {-# OVERLAPS #-} Field x xs => Field x (y /\ xs) where
	field = W_I_II_II `ii` U_I_UU_III_U_II_I `i` \(These old fs) -> These
		`i` inspect (field @x @xs) fs
		`i` \new -> These old `i`adjust (field @x @xs) (\_ -> new) fs

type family Record r where
	Record (x /\ xs) = (Different x xs, Field x (x /\ xs), Record xs)
	Record x = Field x x 

type family Vector x xs where
	Vector x (y /\ xs) = (Matching x y, Vector x xs)
	Vector x y = Matching x y

type Construction = R_U_I_T_I (/\)

pattern Construct :: i -> t (Recursive (U_I_T_II t (/\) i)) -> Construction t i
pattern Construct x xs <- R_U_I_T_I (Recursive (U_I_T_II (These x xs)))
	where Construct x xs = R_U_I_T_I (Recursive (U_I_T_II (These x xs)))

type Instruction = R_U_I_T_I (\/)

pattern Instruct :: t (Recursive (U_I_T_II t (\/) i)) -> Instruction t i
pattern Instruct xs <- R_U_I_T_I (Recursive (U_I_T_II (That xs)))
	where Instruct xs = R_U_I_T_I (Recursive (U_I_T_II (That xs)))

pattern Load :: item -> Instruction f item
pattern Load x <- R_U_I_T_I (Recursive (U_I_T_II (This x)))
