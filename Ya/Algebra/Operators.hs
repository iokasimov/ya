module Ya.Algebra.Operators where

import Ya.Algebra.Abstract
import Ya.Algebra.Definition

infixl 9 `i`
infixl 8 `ii`, `fi`, `fo`, `fa`
infixl 7 `iii`
infixl 6 `fi'fi`, `fo'fi`, `fa'fi`
infixl 4 `fi'fi'fi`
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