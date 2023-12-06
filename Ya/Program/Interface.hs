{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE UndecidableSuperClasses #-}
module Ya.Program.Interface where

import Ya.Algebra
import Ya.Program.Primitive

type family Record record where
	Record (x `LM` (xx `LM` (xxx `LM` (xxxx `LM` xs)))) = (Different x xx, Different x xxx, Different x xxxx, Different xx xxx, Different xx xxxx, Different xxx xxxx, Different x xs, Different xx xs, Different xxx xs, Different xxxx xs, Record xs)
	Record (x `LM` (xx `LM` (xxx `LM` xs))) = (Different x xx, Different x xxx, Different xx xxx, Different x xs, Different xx xs, Different xxx xs, Record xs)
	Record (x `LM` (xx `LM` xs)) = (Different x xx, Different x xs, Different xx xs, Record xs)
	Record (x `LM` xs) = (Different x xs, Record xs)
	Record x = ()

class Record r => Field x r where
	field :: Attribute r x

instance Record x => Field x x
	where field = identity

instance Record (x `LM` xs) => Field x (x `LM` xs)
	where field = W_I_II_II `a` U_I_UU_III_U_II_I
		`i` \(These f fs) -> These `i` f `i` \f' -> These f' fs

instance {-# OVERLAPS #-} (Record (y `LM` xs), Field x xs) => Field x (y `LM` xs) where
	field = W_I_II_II `a` U_I_UU_III_U_II_I `i` \(These old fs) ->These
		`i` inspect (field @x @xs) fs
		`i` \new -> These old `i` adjust (field @x @xs) (\_ -> new) fs

type family Vector x xs where
	Vector x (y `LM` xs) = (Matching x y, Vector x xs)
	Vector x y = Matching x y

class Stack datastructure where
	pop :: Transition / datastructure item / Optional item
	push :: item -> Transition / datastructure item / item

instance Stack List where
	pop = W_I_I_II `a` U_I_UU_II_III `i` \case
		Empty @List -> These `i` Empty @List `i` None
		List (Yet x xs) -> These `i` (T'TT'I / xs `yo` R_U_I_T_I) `i` Some x
	push x = W_I_I_II `a` U_I_UU_II_III `yi` \s -> These
		`i` rewrap (Some `a` R_U_I_T_I `a` Yet x `a` (`yo` uw @Arrow @(R_U_I_T_I _ _ _))) s
		`i` x

instance Stack (Construction Optional) where
	pop = W_I_I_II `a` U_I_UU_II_III `yi` \case
		Nonempty @List (Yet x (Some xs)) -> These `i` Nonempty @List xs `i` Some x
		Nonempty @List (Yet x None) -> These `i'i` Nonempty @List `i` Yet x None `i'i` None
	push x = W_I_I_II `a` U_I_UU_II_III `yi` \s -> These `i` rewrap (Next x) s `i` x

type family Scrolling datastructure where
	Scrolling List = List Unit `T'_'I` U_T_I_TT_I LM I (U_T_I_TT_I LM List List)

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
		previous@(T'_'I (U_T_I_TT_I (These (I x) (U_T_I_TT_I (These (List bs) (List (Yet f fs))))))) -> These
			(T'_'I (U_T_I_TT_I (These (I f) (U_T_I_TT_I (These (List (Yet x (Some bs))) (T'TT'I / R_U_I_T_I `fo` fs))))))
			(Some previous)
		previous@(_) -> These previous None
	scroll Backward = W_I_I_II `a` U_I_UU_II_III `yi` \case
		previous@(T'_'I (U_T_I_TT_I (These (I x) (U_T_I_TT_I (These (List (Yet b bs)) (List fs)))))) -> These
			(T'_'I (U_T_I_TT_I (These (I b) (U_T_I_TT_I (These (T'TT'I / R_U_I_T_I `fo` bs) (List (Yet x (Some fs))))))))
			(Some previous)
		previous@(_) -> These previous None

class Fastenable datastructure where
	fasten :: e -> datastructure e -> Scrolling datastructure e

instance Fastenable List
	where fasten x xs = T'_'I (U_T_I_TT_I (These (I x) (U_T_I_TT_I (These (Empty @List) xs))))

type family Substructure datastructure where
	Substructure (Construction t) = t `T'TT'I` Construction t

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
			(\new -> Construct x / uw @Arrow @(R_U_I_T_I _ _ _) `fo` uw new)

type family Ramification datastructure where
	Ramification (Tree (U_I_I LM `T'TT'I` Optional)) = Unit `ML` Unit

type family Branching datastructure where
	Branching (Tree (U_I_I LM `T'TT'I` Optional)) = Optional `T'TT'I` Binary Tree

class Hierarchial datastructure => Brancheable datastructure where
	branch :: Ramification datastructure ->
		Attribute (datastructure item) (Branching datastructure item)

-- TODO: refactor using limits
instance Brancheable (Tree (U_I_I LM `T'TT'I` Optional)) where
	branch p = W_I_II_II `compose` U_I_UU_III_U_II_I /
		\(Construct x (T'TT'I (U_I_I (These lb rb)))) -> These
			/ case p of
				This _ -> T'TT'I @Optional (wrap @(->) `fo` lb)
				That _ -> T'TT'I @Optional (wrap @(->) `fo` rb)
			/ \new -> case p of
				This _ -> Construct x (T'TT'I (U_I_I (These (uw @(->) `fo` uw new) rb)))
				That _ -> Construct x (T'TT'I (U_I_I (These lb (uw @(->) `fo` uw new))))
