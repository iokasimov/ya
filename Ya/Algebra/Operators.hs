{-# LANGUAGE AllowAmbiguousTypes #-}
module Ya.Algebra.Operators where

import Ya.Algebra.Abstract
import Ya.Algebra.Definition

infixl 9 `i`
infixl 8 `ii`, `fi`, `fo`, `fa`, `yo`, `ro`, `ra`, `w'u`, `u'w`
infixl 7 `iii`, `fi_`, `_fo`, `fo_`, `fa_`
infixl 6 `fi'fi`, `fo'fi`, `fa'fi`, `fokl`, `fo'fo`, `yokl`
infixl 5 `fi_'fi`, `_fo'fi`, `_fo'fo`
infixl 4 `fi'fi'fi`, `fo'fo'fo`
infixl 3 `fi_'fi'fi`, `_fo'fi'fi`
infixl 2 `fi'fi'fi'fi`
infixl 0 `fi'fi'fi'fi'fi`

i, ii, iii :: Category into => into t t
iii = identity
ii = identity
i = identity

fi'fi'fi'fi'fi, fi'fi'fi'fi, fi'fi'fi, fi'fi, fi
	:: Category into => into t t
fi'fi'fi'fi'fi = identity
fi'fi'fi'fi = identity
fi'fi'fi = identity
fi'fi = identity
fi = identity

fi_, fi_'fi, fi_'fi'fi
	:: Category into => into (into s t) (into s t)
fi_ = identity
fi_'fi = identity
fi_'fi'fi = identity

fo, fo'fi :: forall from into f s t .
	Covariant Semi Functor from into f =>
	from s t -> into (f s) (f t)
fo'fi = semifunctor @Flat
fo = semifunctor @Flat

yo :: forall from into f s t .
	Yoneda Category Flat from into f t =>
	Covariant Functor from Arrow f =>
	Contravariant Semi Functor from Arrow (U_II_I into (f t)) =>
	Castable Dual from (U_I_II from s t) =>
	f s -> into (from s t) (f t)
yo = fa_ @from wrap `compose` yoneda @Category @Flat identity

fa, fa'fi :: forall from into f s t .
	Contravariant Semi Functor from into f =>
	from s t -> into (f t) (f s)
fa'fi = semifunctor @Dual
fa = semifunctor @Dual

fokl :: forall from into f g s t .
	Component Natural from into (T_TT_I f g) f =>
	Castable Dual into (T_TT_I f g t) =>
	from s (g t) -> into (f s) (f t)
fokl from = component @Flat @from @into @(f `T_TT_I` g) @f
	`compose` wrap `compose` fo from

yokl :: forall from into g f s t .
	Component Natural from into (T_TT_I f g) f =>
	Yoneda Category Flat from into f (g t) =>
	Castable Dual into (Flat from s (g t)) =>
	Castable Dual into (T_TT_I f g t) =>
	f s -> into (from s (g t)) (f t)
yokl x = component @Flat @from @into @(T_TT_I f g)
	`compose` wrap @into @(T_TT_I f g _)
	`compose` yoneda @Category @Flat @from identity x
	`compose` wrap

fo'fo :: forall from into f g s t .
	Covariant Semi Functor from into g =>
	Covariant Endo Semi Functor into f =>
	from s t -> into (f (g s)) (f (g t))
fo'fo = fo @into @into `compose` fo @from @into

fo'fo'fo :: forall from into f g h s t .
	Covariant Semi Functor from into h =>
	Covariant Endo Semi Functor into g =>
	Covariant Endo Semi Functor into f =>
	from s t -> into (f (g (h s))) (f (g (h t)))
fo'fo'fo = fo @into @into `compose` fo @into @into `compose` fo @from @into

_fo, _fo'fi, _fo'fi'fi :: forall from into f s t i .
	Covariant Semi Functor from into (U_I_II f i) =>
	Wrapper into (U_I_II f i s) =>
	Wrapper into (U_I_II f i t) =>
	from s t -> into (f i s) (f i t)
_fo from = unwrap `compose` fo @_ @_ @(U_I_II _ _) from `compose` wrap
_fo'fi from = unwrap `compose` fo @_ @_ @(U_I_II _ _) from `compose` wrap
_fo'fi'fi from = unwrap `compose` fo @_ @_ @(U_I_II _ _) from `compose` wrap

fo_ :: forall from into f s t i .
	Covariant Semi Functor from into (U_II_I f i) =>
	Wrapper into (U_II_I f i s) =>
	Wrapper into (U_II_I f i t) =>
	from s t -> into (f s i) (f t i)
fo_ from = unwrap `compose` fo @_ @_ @(U_II_I _ _) from `compose` wrap

fa_ :: forall from into f s t i .
	Contravariant Semi Functor from into (U_II_I f i) =>
	Wrapper into (U_II_I f i s) =>
	Wrapper into (U_II_I f i t) =>
	from s t -> into (f t i) (f s i)
fa_ from = unwrap `compose` fa @_ @_ @(U_II_I _ _) from `compose` wrap

_fo'fo :: forall from into f g o s t .
	Covariant Semi Functor into into (U_I_II f o) =>
	Covariant Semi Functor from into g =>
	(forall i . Wrapper into (U_I_II f o i)) =>
	from s t -> into (f o (g s)) (f o (g t))
_fo'fo = _fo @into @into `compose` fo @from @into

ya :: forall from into f s t .
	Yoneda Category Dual from into f t =>
	Covariant Functor from Arrow f =>
	Contravariant Semi Functor from Arrow (U_II_I into (f t)) =>
	Castable Dual from (U_II_I from s t) =>
	f s -> into (from t s) (f t)
ya = fa_ @from wrap `compose` yoneda @Category @Dual identity

ro :: forall from into hom f i .
	Covariant (Representable hom) Category from into f =>
	Castable Flat into (Flat hom (Representation f) i) =>
	into (f i) (hom (Representation f) i)
ro = unwrap `compose` component @Flat @from @into @f @(Flat hom (Representation f))

ra :: forall from into hom f i .
	Contravariant (Representable hom) Category from into f =>
	Castable Flat into (Dual hom (Representation f) i) =>
	into (f i) (hom i (Representation f))
ra = unwrap `compose` component @Dual @from @into @f @(Dual hom (Representation f))

w'u :: forall into s t .
	Precategory into =>
	Castable Dual into t =>
	Castable Flat into s =>
	into (Supertype s) (Supertype t) -> into s t
w'u into = wrap @into `compose` into `compose` unwrap @into

u'w :: forall into s t .
	Precategory into =>
	Castable Dual into s =>
	Castable Flat into t =>
	into s t -> into (Supertype s) (Supertype t)
u'w into = unwrap @into `compose` into `compose` wrap @into
