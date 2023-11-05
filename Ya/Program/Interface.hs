{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE UndecidableSuperClasses #-}
module Ya.Program.Interface where

import Ya.Algebra
import Ya.Program.Primitive

type family Record record where
	Record (x /\ (xx /\ (xxx /\ (xxxx /\ xs)))) = (Different x xx, Different x xxx, Different x xxxx, Different xx xxx, Different xx xxxx, Different xxx xxxx, Different x xs, Different xx xs, Different xxx xs, Different xxxx xs, Record xs)
	Record (x /\ (xx /\ (xxx /\ xs))) = (Different x xx, Different x xxx, Different xx xxx, Different x xs, Different xx xs, Different xxx xs, Record xs)
	Record (x /\ (xx /\ xs)) = (Different x xx, Different x xs, Different xx xs, Record xs)
	Record (x /\ xs) = (Different x xs, Record xs)
	Record x = ()

class Record r => Field x r where
	field :: Attribute r x

instance Record x => Field x x
	where field = identity

instance Record (x /\ xs) => Field x (x /\ xs)
	where field = W_I_II_II `i'i` U_I_UU_III_U_II_I
		`i` (\(These f fs) -> These `i` f `i` (\f' -> These f' fs))

instance {-# OVERLAPS #-} (Record (y /\ xs), Field x xs) => Field x (y /\ xs) where
	field = W_I_II_II `i'i` U_I_UU_III_U_II_I `i` \(These old fs) -> These
		/ inspect (field @x @xs) fs
		/ \new -> These old `i` adjust (field @x @xs) (\_ -> new) fs

type family Vector x xs where
	Vector x (y /\ xs) = (Matching x y, Vector x xs)
	Vector x y = Matching x y

class Stack datastructure where
	pop :: Transition / datastructure item / Optional item
	push :: item -> Transition / datastructure item / item

instance Stack List where
	pop = W_I_I_II `a` U_I_UU_II_III `yi` \case
		Empty @List -> These `i` Empty @List `i'i` None
		List (Yet x xs) -> These `i` (T_TT_I / xs `yo`R_U_I_T_I) `i'i` Some x
	push x = W_I_I_II `a` U_I_UU_II_III `yi` \s -> These
		`i`rewrap (Some `compose` R_U_I_T_I `compose` Yet x `compose` (`yo`unwrap @Arrow @(R_U_I_T_I _ _ _))) s
		`i'i`x

instance Stack (Construction Optional) where
	pop = W_I_I_II `a` U_I_UU_II_III `yi` \case
		Nonempty @List (Yet x (Some xs)) -> These `i` Nonempty @List xs `i'i` Some x
		Nonempty @List (Yet x None) -> These `i` Nonempty @List (Yet x None) `i'i` None
	push x = W_I_I_II `a` U_I_UU_II_III `yi` \s -> These `i` rewrap (Next x) s `i'i` x

type family Scrolling datastructure where
	Scrolling List = U_T_I_TT_I (/\) I (U_T_I_TT_I (/\) List List)

type family Orientation datastructure where
	Orientation List = Horizontal

class Scrollable datastructure where
	scroll :: Orientation datastructure -> Transition
		/ Scrolling datastructure item
		/ Optional (Scrolling datastructure item)

-- TODO: try use the fact that `Horizontal` ~ `Boolean`
-- `Boolean` is `Representative` for `U_I_I (/\)`
instance Scrollable List where
	scroll Forward = W_I_I_II `a` U_I_UU_II_III `yi` \case
		previous@(U_T_I_TT_I (These (I x) (U_T_I_TT_I (These (List bs) (List (Yet f fs)))))) -> These
			(U_T_I_TT_I (These (I f) (U_T_I_TT_I (These (List (Yet x (Some bs))) (T_TT_I / R_U_I_T_I `fo` fs)))))
			(Some previous)
		previous@(_) -> These previous None
	scroll Backward = W_I_I_II `a` U_I_UU_II_III `yi` \case
		previous@(U_T_I_TT_I (These (I x) (U_T_I_TT_I (These (List (Yet b bs)) (List fs))))) -> These
			(U_T_I_TT_I (These (I b) (U_T_I_TT_I (These (T_TT_I / R_U_I_T_I `fo` bs) (List (Yet x (Some fs)))))))
			(Some previous)
		previous@(_) -> These previous None

type family Substructure datastructure where
	Substructure (Construction t) = t `T_TT_I` Construction t

class Hierarchial datastructure where
	top :: Attribute (datastructure item) item
	sub :: Attribute (datastructure item) (Substructure datastructure item)

instance Covariant Endo Semi Functor (->) t
	=> Hierarchial (Construction t) where
	top = W_I_II_II `compose` U_I_UU_III_U_II_I /
		\(Construct old xs) -> These / old / \new -> Construct new xs
	sub = W_I_II_II `compose` U_I_UU_III_U_II_I /
		\(Construct x old) -> These
			(T_TT_I / wrap @Arrow @(R_U_I_T_I _ _ _) `fo` old)
			(\new -> Construct x / unwrap @Arrow @(R_U_I_T_I _ _ _) `fo` unwrap new)

type family Ramification datastructure where
	Ramification (Tree (U_I_I (/\) `T_TT_I` Optional)) = Unit \/ Unit

type family Branching datastructure where
	Branching (Tree (U_I_I (/\) `T_TT_I` Optional)) = Optional `T_TT_I` Binary Tree

class Hierarchial datastructure => Brancheable datastructure where
	branch :: Ramification datastructure ->
		Attribute (datastructure item) (Branching datastructure item)

-- TODO: refactor using limits
instance Brancheable (Tree (U_I_I (/\) `T_TT_I` Optional)) where
	branch p = W_I_II_II `compose` U_I_UU_III_U_II_I /
		\(Construct x (T_TT_I (U_I_I (These lb rb)))) -> These
			/ case p of
				This _ -> T_TT_I @Optional (wrap @(->) `fo` lb)
				That _ -> T_TT_I @Optional (wrap @(->) `fo` rb)
			/ \new -> case p of
				This _ -> Construct x (T_TT_I (U_I_I (These (unwrap @(->) `fo` unwrap new) rb)))
				That _ -> Construct x (T_TT_I (U_I_I (These lb (unwrap @(->) `fo` unwrap new))))