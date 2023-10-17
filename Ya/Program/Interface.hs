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
	pop :: Stateful (datastructure item) (Optional item)
	push :: item -> Stateful (datastructure item) item

instance Stack List where
	pop = Statefully observe `yokl`\case
		Empty @List -> Statefully observe `ye`None
		List (Yet x xs) -> Statefully `i`replace (T_TT_I / xs `yo`R_U_I_T_I) `ye`Some x
	push x = (wrap `compose` transit `compose` rewrap / (`yo`rewrap `i`Next x)) `ye`x

instance Stack (Construction Optional) where
	pop = Statefully observe `yokl` \case
		Nonempty @List (Next x (Next xx xs)) ->
			Statefully `i`replace (Nonempty @List / Next xx xs) `ye` Some x
	push x = Statefully `i`transit (rewrap / Next x) `ye` x
