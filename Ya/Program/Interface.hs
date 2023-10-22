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
	where field = W_I_II_II `ii` U_I_UU_III_U_II_I
		`i` (\(These f fs) -> These `i` f `ii` (\f' -> These f' fs))

instance {-# OVERLAPS #-} (Record (y /\ xs), Field x xs) => Field x (y /\ xs) where
	field = W_I_II_II `ii` U_I_UU_III_U_II_I `i` \(These old fs) -> These
		/ inspect (field @x @xs) fs
		/ \new -> These old `i`adjust (field @x @xs) (\_ -> new) fs

type family Vector x xs where
	Vector x (y /\ xs) = (Matching x y, Vector x xs)
	Vector x y = Matching x y

class Stack datastructure where
	pop :: Transition / datastructure item / Optional item
	push :: item -> Transition / datastructure item / item

instance Stack List where
	pop = W_I_I_II `i` U_I_UU_II_III `i` \case
		Empty @List -> These `i` Empty @List `ii` None
		List (Yet x xs) -> These `i` (T_TT_I / xs `yo`R_U_I_T_I) `ii` Some x
	push x = W_I_I_II `i` U_I_UU_II_III `i` \s -> These
		`i`rewrap (Some `compose` R_U_I_T_I `compose` Yet x `compose` (`yo`unwrap @Arrow @(R_U_I_T_I _ _ _))) s
		`ii`x

instance Stack (Construction Optional) where
	pop = W_I_I_II `i` U_I_UU_II_III `i` \case
		Nonempty @List (Yet x (Some xs)) -> These `i` Nonempty @List xs `ii` Some x
		Nonempty @List (Yet x None) -> These `i` Nonempty @List (Yet x None) `ii` None
	push x = W_I_I_II `i` U_I_UU_II_III `i` \s -> These `i` rewrap (Next x) s `ii` x
