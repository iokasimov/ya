{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE UndecidableSuperClasses #-}
module Ya.Program.Interface where

import Ya.Algebra
import Ya.Program.Primitive

class Field e r where
	item :: Attribute r e

instance Field e e
	where item = identity

instance Field e (Only e)
	where item = W_I_II_II `a` U_I_UU_III_U_II_I
		`i` \(Only x) -> These `i` x `i` \x' -> Only x

instance Field e (e `LM` ee)
	where item = W_I_II_II `a` U_I_UU_III_U_II_I
		`i` \(These f fs) -> These `i` f `i` \f_ -> These f_ fs

instance {-# OVERLAPS #-} Field e ee => Field e (eee `LM` ee) where
	item = W_I_II_II `a` U_I_UU_III_U_II_I `i` \(These old fs) ->These
		`i` inspect (item @e @ee) fs
		`i` \new -> These old `i` adjust (item @e @ee) (\_ -> new) fs

instance Field (t e) (U_T_I_TT_I LM t tt e)
	where item = W_I_II_II `a` U_I_UU_III_U_II_I `i`
		\(U_T_I_TT_I (These f fs)) -> These `i` f `i` \f_ -> U_T_I_TT_I (These f_ fs)

instance {-# OVERLAPS #-} Field e (tt ee) => Field e (U_T_I_TT_I LM t tt ee) where
	item = W_I_II_II `a` U_I_UU_III_U_II_I `i` \(U_T_I_TT_I (These old fs)) -> These
		`i` inspect (item @e @(tt ee)) fs
		`i` \new -> U_T_I_TT_I (These old `i` adjust (item @e @(tt ee)) (\_ -> new) fs)

instance Field e (Construction t e)
	where item = W_I_II_II `a` U_I_UU_III_U_II_I `i`
		\(Root old xs) -> These / old / \new -> Root new xs

instance Covariant Endo Semi Functor (->) t =>
	Field (t (Construction t e)) (Construction t e)
	where item = W_I_II_II `a` U_I_UU_III_U_II_I `i`
		\(Root x old) -> These
			(wrap @Arrow @(R_U_I_T_I _ _ _) `fo` old)
			(\new -> Root x / rw @Arrow @(R_U_I_T_I _ _ _) `fo` new)

section :: forall t tt e .
	Field (t e) (tt e) =>
	Attribute (tt e) (t e)
section = item @(t e) @(tt e)

type family Vector x xs where
	Vector x (y `LM` xs) = (Same x y, Vector x xs)
	Vector x y = Same x y

class Stack datastructure where
	pop :: Automata `TI` datastructure item `TI` Optional item
	push :: item -> Automata `TI` datastructure item `TI` item

instance Stack List where
	pop = W_I_I_II `a` U_I_UU_II_III `i` \case
		Empty @List -> These `i` Empty @List `i` None
		List (Yet x xs) -> These `i` (T_TT_I / xs `yo` R_U_I_T_I) `i` Some x
	push x = W_I_I_II `a` U_I_UU_II_III `yi` \s -> These
		`i` rewrap (Some `a` R_U_I_T_I `a` Yet x `a` (`yo` rw @Arrow @(R_U_I_T_I _ _ _))) s
		`i` x

instance Stack (Construction Optional) where
	pop = W_I_I_II `a` U_I_UU_II_III `yi` \case
		Nonempty @List (Yet x (Some xs)) -> These `i` Nonempty @List xs `i` Some x
		Nonempty @List (Yet x None) -> These `i_i` Nonempty @List `i` Yet x None `i_i` None
	push x = W_I_I_II `a` U_I_UU_II_III `yi` \s -> These `i` rewrap (Next x) s `i` x

type family Scrolling datastructure where
	Scrolling List = U_T_I_TT_I LM Identity (U_T_I_TT_I LM (Backward List) (Forward List))

instance Mapping Straight Straight Arrow Arrow
	(R_U_I_T_I LM Optional) (U_T_I_TT_I LM Identity (U_T_I_TT_I LM (Backward List) (Forward List)))
	where mapping = rewrap / \from (Root x xs) ->
		U_T_I_TT_I / These (Identity (from x))
		(U_T_I_TT_I (These
			(label (Empty @List))
			(label ((T_TT_I / xs `yo` R_U_I_T_I) `yo` from))
			)
		)

type family Orientation datastructure where
	Orientation List = Horizontal

class Scrollable datastructure where
	scroll :: Orientation datastructure -> Automata
		`TI` Scrolling datastructure item
		`TI` Optional (Scrolling datastructure item)

-- TODO: try use the fact that `Horizontal` ~ `Boolean`
-- `Boolean` is `Representative` for `U_I_I LM`
instance Scrollable List where
	scroll Forth = W_I_I_II `a` U_I_UU_II_III `yi` \case
		previous@(U_T_I_TT_I (These (Identity x) (U_T_I_TT_I (These (T_'_I (T_TT_I bs)) (T_'_I (List (Yet f fs))))))) -> These
			(U_T_I_TT_I (These (Identity f) (U_T_I_TT_I (These (T_'_I (List (Yet x (bs `yo` unwrap)))) (T_'_I (T_TT_I / fs `yo` wrap @(->)))))))
			(Some previous)
		previous@(_) -> These previous None
	scroll Back = W_I_I_II `a` U_I_UU_II_III `yi` \case
		previous@(U_T_I_TT_I (These (Identity x) (U_T_I_TT_I (These (T_'_I (List (Yet b bs))) (T_'_I (T_TT_I fs)))))) -> These
			(U_T_I_TT_I (These (Identity b) (U_T_I_TT_I (These (T_'_I (T_TT_I / bs `yo` R_U_I_T_I)) (T_'_I (List (Yet x (fs `yo` unwrap))))))))
			(Some previous)
		previous@(_) -> These previous None

type family Substructure datastructure where
	Substructure (Construction t) = t `T_TT_I` Construction t
	Substructure (U_T_I_TT_I LM Identity (U_T_I_TT_I LM List List)) = U_T_I_TT_I LM List List

class Hierarchial datastructure where
	root :: Attribute (datastructure item) item
	subs :: Attribute (datastructure item) (Substructure datastructure item)

instance Covariant Endo Semi Functor (->) t
	=> Hierarchial (Construction t) where
	root = W_I_II_II `compose` U_I_UU_III_U_II_I /
		\(Root old xs) -> These / old / \new -> Root new xs
	subs = W_I_II_II `compose` U_I_UU_III_U_II_I /
		\(Root x old) -> These
			(T_TT_I / wrap @Arrow @(R_U_I_T_I _ _ _) `fo` old)
			(\new -> Root x / rw @Arrow @(R_U_I_T_I _ _ _) `fo` rw new)

instance Hierarchial (U_T_I_TT_I LM Identity (U_T_I_TT_I LM List List)) where
	root = W_I_II_II `compose` U_I_UU_III_U_II_I /
		\(U_T_I_TT_I (These (Identity old) xs)) -> These old (\new -> U_T_I_TT_I (These (Identity new) xs))
	subs = W_I_II_II `compose` U_I_UU_III_U_II_I /
		\(U_T_I_TT_I (These (Identity x) old)) -> These old (\new -> U_T_I_TT_I (These (Identity x) new))

type family Ramification datastructure where
	Ramification (Tree (U_I_I LM `T_TT_I` Optional)) = () `ML` ()
	-- Ramification (U_T_I_TT_I LM Identity (U_T_I_TT_I LM List List)) = () `ML` ()

type family Branching datastructure where
	Branching (Tree (U_I_I LM `T_TT_I` Optional)) = Optional `T_TT_I` Binary Tree
	-- Branching (U_T_I_TT_I LM Identity (U_T_I_TT_I LM List List)) = List

class Hierarchial datastructure => Brancheable datastructure where
	branch :: Ramification datastructure -> Attribute (datastructure item) (Branching datastructure item)

-- TODO: refactor using limits/colimits
instance Brancheable (Tree (U_I_I LM `T_TT_I` Optional)) where
	branch p = W_I_II_II `compose` U_I_UU_III_U_II_I /
		\(Root x (T_TT_I (U_I_I (These lb rb)))) -> These
			/ case p of
				This _ -> T_TT_I @Optional (wrap @(->) `fo` lb)
				That _ -> T_TT_I @Optional (wrap @(->) `fo` rb)
			/ \new -> case p of
				This _ -> Root x (T_TT_I (U_I_I (These (rw @(->) `fo` rw new) rb)))
				That _ -> Root x (T_TT_I (U_I_I (These lb (rw @(->) `fo` rw new))))

-- TODO: refactor using limits/colimits
-- instance Brancheable (U_T_I_TT_I LM Identity (U_T_I_TT_I LM (Backward List) List)) where
	-- branch p = W_I_II_II `compose` U_I_UU_III_U_II_I /
		-- \(U_T_I_TT_I (These (Identity x) (U_T_I_TT_I (These rs fs)))) -> These
			-- / case p of
				-- This _ -> rs
				-- That _ -> fs
			-- / \new -> case p of
				-- This _ -> U_T_I_TT_I (These (Identity x) (U_T_I_TT_I (These new fs)))
				-- This _ -> U_T_I_TT_I (These (Identity x) (U_T_I_TT_I (These rs new)))
