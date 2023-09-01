{-# LANGUAGE AllowAmbiguousTypes #-}
module Ya.Algebra.Operators where

import Ya.Algebra.Abstract
import Ya.Algebra.Definition

infixl 9 `i`
infixl 8 `ii`, `fi`, `fo`, `fa`
infixl 7 `iii`, `fi_`
infixl 6 `fi'fi`, `fo'fi`, `fa'fi`, `fokl`, `fo'fo`
infixl 5 `fi_'fi`
infixl 4 `fi'fi'fi`
infixl 3 `fi_'fi'fi`
infixl 2 `fi'fi'fi'fi`
infixl 0 `fi'fi'fi'fi'fi`

i, ii, iii :: Category into => into t t
iii = identity
ii = identity
i = identity

fi'fi'fi'fi'fi, fi'fi'fi'fi, fi'fi'fi, fi'fi, fi :: Category into => into t t
fi'fi'fi'fi'fi = identity
fi'fi'fi'fi = identity
fi'fi'fi = identity
fi'fi = identity
fi = identity

fi_, fi_'fi, fi_'fi'fi :: Category into => into (into s t) (into s t)
fi_ = identity
fi_'fi = identity
fi_'fi'fi = identity

fo, fo'fi :: forall from into f s t .
	Covariant Semifunctor f from into =>
	from s t -> into (f s) (f t)
fo'fi = semifunctor @Flat
fo = semifunctor @Flat

fa, fa'fi :: forall from into f s t .
	Contravariant Semifunctor f from into =>
	from s t -> into (f t) (f s)
fa'fi = semifunctor @Dual
fa = semifunctor @Dual

fokl :: forall from into f g s t .
	Covariant Semifunctor f (Kleisli g from) into =>
	from s (g t) -> into (f s) (f t)
fokl k = transformation `fi` U_I_II (U_I_T_II k)

fo'fo :: forall from into f g s t .
	Covariant Semifunctor g from into =>
	Covariant Semifunctor f into into =>
	from s t -> into (f (g s)) (f (g t))
fo'fo = fo @into @into `compose` fo @from @into