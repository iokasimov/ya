{-# LANGUAGE AllowAmbiguousTypes #-}
module Ya.Algebra.Operators where

import Ya.Algebra.Abstract
import Ya.Algebra.Definition

infixl 9 `i`
infixl 8 `ii`, `fi`, `fo`, `fa`
infixl 7 `iii`, `fi_`, `_fo`
infixl 6 `fi'fi`, `fo'fi`, `fa'fi`, `fokl`, `fo'fo`
infixl 5 `fi_'fi`, `_fo'fi`, `_fo'fo`
infixl 4 `fi'fi'fi`
infixl 3 `fi_'fi'fi`, `_fo'fi'fi`
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
fokl = semifunctor @Flat `compose` U_I_T_II

fo'fo :: forall from into f g s t .
	Covariant Semifunctor g from into =>
	Covariant Semifunctor f into into =>
	from s t -> into (f (g s)) (f (g t))
fo'fo = fo @into @into `compose` fo @from @into

_fo, _fo'fi, _fo'fi'fi :: forall from into f s t i .
	Covariant Semifunctor (U_I_II f i) from into =>
	Wrapper into (U_I_II f i s) =>
	Wrapper into (U_I_II f i t) =>
	from s t -> into (f i s) (f i t)
_fo from = unwrap `compose` fo @_ @_ @(U_I_II _ _) from `compose` wrap
_fo'fi from = unwrap `compose` fo @_ @_ @(U_I_II _ _) from `compose` wrap
_fo'fi'fi from = unwrap `compose` fo @_ @_ @(U_I_II _ _) from `compose` wrap

_fo'fo :: forall from into f g o s t .
	Covariant Semifunctor (U_I_II f o) into into =>
	Covariant Semifunctor g from into =>
	(forall i . Wrapper into (U_I_II f o i)) =>
	from s t -> into (f o (g s)) (f o (g t))
_fo'fo = _fo @into @into `compose` fo @from @into