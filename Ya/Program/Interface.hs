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
		`i` (\(These f fs) -> These `i` f `i` (\f' -> These f' fs))

instance {-# OVERLAPS #-} (Record (y /\ xs), Field x xs) => Field x (y /\ xs) where
	field = W_I_II_II `ii` U_I_UU_III_U_II_I `i` \(These old fs) -> These
		`i` inspect (field @x @xs) fs
		`i` \new -> These old `i`adjust (field @x @xs) (\_ -> new) fs

type family Vector x xs where
	Vector x (y /\ xs) = (Matching x y, Vector x xs)
	Vector x y = Matching x y
