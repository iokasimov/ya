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

view ::
	Castable Flat Arrow (Reference origin target target) =>
	Castable Flat Arrow (Attribute origin target) =>
	Attribute origin target -> (origin -> target)
view r s = let (These qt _) = r `u'u` s in qt

change ::
	Castable Flat Arrow (Reference origin target target) =>
	Castable Flat Arrow (Attribute origin target) =>
	Attribute origin target -> (target -> target) -> (origin -> origin)
change attr f s = let (These h x) = attr `u'u` s in x `i`f h

type Transition = U_I_UU_II_III (->) (/\)

type Stateful = W_I_I_II Transition
