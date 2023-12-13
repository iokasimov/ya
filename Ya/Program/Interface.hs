{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE UndecidableSuperClasses #-}
module Ya.Program.Interface where

import Ya.Algebra
import Ya.Program.Primitive

class Field e r where
	field :: Attribute r e

instance Field e e
	where field = identity

instance Field e (e `LM` ee)
	where field = W_I_II_II `a` U_I_UU_III_U_II_I
		`i` \(These f fs) -> These `i` f `i` \f' -> These f' fs

instance {-# OVERLAPS #-} Field e ee =>
	Field e (eee `LM` ee) where
	field = W_I_II_II `a` U_I_UU_III_U_II_I `i` \(These old fs) ->These
		`i` inspect (field @e @ee) fs
		`i` \new -> These old `i` adjust (field @e @ee) (\_ -> new) fs

instance Field (t e) (U_T_I_TT_I LM t tt e)
	where field = W_I_II_II `a` U_I_UU_III_U_II_I `i`
		\(U_T_I_TT_I (These f fs)) -> These `i` f `i` \f' -> U_T_I_TT_I (These f' fs)

instance {-# OVERLAPS #-} Field e (tt ee) =>
	Field e (U_T_I_TT_I LM t tt ee) where
	field = W_I_II_II `a` U_I_UU_III_U_II_I `i` \(U_T_I_TT_I (These old fs)) -> These
		`i` inspect (field @e @(tt ee)) fs
		`i` \new -> U_T_I_TT_I (These old `i` adjust (field @e @(tt ee)) (\_ -> new) fs)

substructure :: forall t tt e .
	Field (t e) (tt e) => Attribute (tt e) (t e)
substructure = field @(t e) @(tt e)

type family Vector x xs where
	Vector x (y `LM` xs) = (Same x y, Vector x xs)
	Vector x y = Same x y

class Stack datastructure where
	pop :: Transition / datastructure item / Optional item
	push :: item -> Transition / datastructure item / item

instance Stack List where
	pop = W_I_I_II `a` U_I_UU_II_III `i` \case
		Empty @List -> These `i` Empty @List `i` None
		List (Yet x xs) -> These `i` (T'TT'I / xs `yo` R_U_I_T_I) `i` Some x
	push x = W_I_I_II `a` U_I_UU_II_III `yi` \s -> These
		`i` rewrap (Some `a` R_U_I_T_I `a` Yet x `a` (`yo` rw @Arrow @(R_U_I_T_I _ _ _))) s
		`i` x

instance Stack (Construction Optional) where
	pop = W_I_I_II `a` U_I_UU_II_III `yi` \case
		Nonempty @List (Yet x (Some xs)) -> These `i` Nonempty @List xs `i` Some x
		Nonempty @List (Yet x None) -> These `i'i` Nonempty @List `i` Yet x None `i'i` None
	push x = W_I_I_II `a` U_I_UU_II_III `yi` \s -> These `i` rewrap (Next x) s `i` x

type family Scrolling datastructure where
	Scrolling List = U_T_I_TT_I LM I (U_T_I_TT_I LM (Backward List) List)

type family Orientation datastructure where
	Orientation List = Horizontal

class Scrollable datastructure where
	scroll :: Orientation datastructure -> Transition
		/ Scrolling datastructure item
		/ Optional (Scrolling datastructure item)

-- TODO: try use the fact that `Horizontal` ~ `Boolean`
-- `Boolean` is `Representative` for `U_I_I LM`
instance Scrollable List where
	scroll Forward = W_I_I_II `a` U_I_UU_II_III `yi` \case
		previous@(U_T_I_TT_I (These (I x) (U_T_I_TT_I (These (T'_'I (T'TT'I bs)) (List (Yet f fs)))))) -> These
			(U_T_I_TT_I (These (I f) (U_T_I_TT_I (These (T'_'I (List (Yet x (bs `yo` unwrap)))) (T'TT'I / fs `yo` wrap @(->))))))
			(Some previous)
		previous@(_) -> These previous None
	scroll Backward = W_I_I_II `a` U_I_UU_II_III `yi` \case
		previous@(U_T_I_TT_I (These (I x) (U_T_I_TT_I (These (T'_'I (List (Yet b bs))) (T'TT'I fs))))) -> These
			(U_T_I_TT_I (These (I b) (U_T_I_TT_I (These (T'_'I (T'TT'I / bs `yo` R_U_I_T_I)) (List (Yet x (fs `yo` unwrap)))))))
			(Some previous)
		previous@(_) -> These previous None

type family Fastening datastructure where
	Fastening List = Nonempty List

class Fastenable datastructure where
	fasten :: Fastening datastructure e -> Scrolling datastructure e

instance Fastenable List
	where fasten (Construct x xs) =
		U_T_I_TT_I / These (I x)
		(U_T_I_TT_I (These
			(label (Empty @List))
			(T'TT'I / xs `yo` R_U_I_T_I)
			)
		)

type family Substructure datastructure where
	Substructure (Construction t) = t `T'TT'I` Construction t
	Substructure (U_T_I_TT_I LM I (U_T_I_TT_I LM List List)) = U_T_I_TT_I LM List List

class Hierarchial datastructure where
	root :: Attribute (datastructure item) item
	subs :: Attribute (datastructure item) (Substructure datastructure item)

instance Covariant Endo Semi Functor (->) t
	=> Hierarchial (Construction t) where
	root = W_I_II_II `compose` U_I_UU_III_U_II_I /
		\(Construct old xs) -> These / old / \new -> Construct new xs
	subs = W_I_II_II `compose` U_I_UU_III_U_II_I /
		\(Construct x old) -> These
			(T'TT'I / wrap @Arrow @(R_U_I_T_I _ _ _) `fo` old)
			(\new -> Construct x / rw @Arrow @(R_U_I_T_I _ _ _) `fo` rw new)

instance Hierarchial (U_T_I_TT_I LM I (U_T_I_TT_I LM List List)) where
	root = W_I_II_II `compose` U_I_UU_III_U_II_I /
		\(U_T_I_TT_I (These (I old) xs)) -> These old (\new -> U_T_I_TT_I (These (I new) xs))
	subs = W_I_II_II `compose` U_I_UU_III_U_II_I /
		\(U_T_I_TT_I (These (I x) old)) -> These old (\new -> U_T_I_TT_I (These (I x) new))

type family Ramification datastructure where
	Ramification (Tree (U_I_I LM `T'TT'I` Optional)) = Unit `ML` Unit
	-- Ramification (U_T_I_TT_I LM I (U_T_I_TT_I LM List List)) = Unit `ML` Unit

type family Branching datastructure where
	Branching (Tree (U_I_I LM `T'TT'I` Optional)) = Optional `T'TT'I` Binary Tree
	-- Branching (U_T_I_TT_I LM I (U_T_I_TT_I LM List List)) = List

class Hierarchial datastructure => Brancheable datastructure where
	branch :: Ramification datastructure -> Attribute (datastructure item) (Branching datastructure item)

-- TODO: refactor using limits/colimits
instance Brancheable (Tree (U_I_I LM `T'TT'I` Optional)) where
	branch p = W_I_II_II `compose` U_I_UU_III_U_II_I /
		\(Construct x (T'TT'I (U_I_I (These lb rb)))) -> These
			/ case p of
				This _ -> T'TT'I @Optional (wrap @(->) `fo` lb)
				That _ -> T'TT'I @Optional (wrap @(->) `fo` rb)
			/ \new -> case p of
				This _ -> Construct x (T'TT'I (U_I_I (These (rw @(->) `fo` rw new) rb)))
				That _ -> Construct x (T'TT'I (U_I_I (These lb (rw @(->) `fo` rw new))))

-- TODO: refactor using limits/colimits
-- instance Brancheable (U_T_I_TT_I LM I (U_T_I_TT_I LM (Backward List) List)) where
	-- branch p = W_I_II_II `compose` U_I_UU_III_U_II_I /
		-- \(U_T_I_TT_I (These (I x) (U_T_I_TT_I (These rs fs)))) -> These
			-- / case p of
				-- This _ -> rs
				-- That _ -> fs
			-- / \new -> case p of
				-- This _ -> U_T_I_TT_I (These (I x) (U_T_I_TT_I (These new fs)))
				-- This _ -> U_T_I_TT_I (These (I x) (U_T_I_TT_I (These rs new)))
