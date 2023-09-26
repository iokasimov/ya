{-# LANGUAGE AllowAmbiguousTypes #-}
module Ya.Algebra.Operators where

import Ya.Algebra.Abstract
import Ya.Algebra.Definition

infixl 9 `i`
infixl 8 `ii`, `fi`, `fo`, `fa`, `yo`, `ya`, `ho`, `ha`, `ro`, `ra`, `w'u`, `u'w`, `u'u`
infixl 7 `iii`, `ljo`, `rjo`, `fi_`, `_fo`, `fo_`, `fa_`
infixl 6 `fi'fi`, `fo'fi`, `fa'fi`, `fokl`, `fo'fo`, `yokl`, `hokl`
infixl 5 `fi_'fi`, `_fo'fi`, `_fo'fo`, `_yokl`
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
	Category from =>
	Precategory into =>
	Covariant Yoneda Functor from into f t =>
	Castable Dual into (U_I_II from s t) =>
	f s -> into (from s t) (f t)
yo x = yoneda @Flat @Functor identity x `compose` wrap

fa, fa'fi :: forall from into f s t .
	Contravariant Semi Functor from into f =>
	from s t -> into (f t) (f s)
fa'fi = semifunctor @Dual
fa = semifunctor @Dual

ya :: forall from into f s t .
	Category from =>
	Precategory into =>
	Contravariant Yoneda Functor from into f t =>
	Castable Dual into (Dual from s t) =>
	f s -> into (from t s) (f t)
ya x = yoneda @Dual @Functor identity x `compose` wrap 

fokl :: forall from into f g s t .
	Component Natural from into (T_TT_I f g) f =>
	Castable Dual into (T_TT_I f g t) =>
	from s (g t) -> into (f s) (f t)
fokl from = component @Flat @from @into @(f `T_TT_I` g) @f
	`compose` wrap `compose` fo from

yokl :: forall from into g f s t .
	Component Natural from into (T_TT_I f g) f =>
	Covariant Yoneda Functor from into f (g t) =>
	Castable Dual into (Flat from s (g t)) =>
	Castable Dual into (T_TT_I f g t) =>
	f s -> into (from s (g t)) (f t)
yokl x = component @Flat @from @into @(T_TT_I f g)
	`compose` wrap @into @(T_TT_I f g _)
	`compose` yoneda @Flat @Functor @from identity x
	`compose` wrap

_yokl :: forall from into g f i s t .
	Component Natural from into (T_TT_I (U_I_II f i) g) (U_I_II f i) =>
	Covariant Yoneda Functor from into (U_I_II f i) (g t) =>
	Castable Dual into (U_I_II from s (g t)) =>
	Castable Flat into (U_I_II f i t) =>
	Castable Dual into (T_TT_I (U_I_II f i) g t) =>
	f i s -> into (from s (g t)) (f i t)
_yokl x = unwrap @into @(U_I_II f i t)
	`compose` component @Flat @from @into @(T_TT_I (U_I_II f i) g)
	`compose` wrap @into @(T_TT_I (U_I_II f i) g _)
	`compose` yoneda @Flat @Functor @from identity (U_I_II x)
	`compose` wrap

fo'fo :: forall from into f g s t .
	Covariant Semi Functor from into g =>
	Covariant Endo Semi Functor into f =>
	from s t -> into (f (g s)) (f (g t))
fo'fo from = fo @into @into (fo @from @into from)

fo'fo'fo :: forall from into f g h s t .
	Covariant Semi Functor from into h =>
	Covariant Endo Semi Functor into g =>
	Covariant Endo Semi Functor into f =>
	from s t -> into (f (g (h s))) (f (g (h t)))
fo'fo'fo from = fo @into @into (fo @into @into (fo @from @into from))

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
_fo'fo from = _fo @into @into (fo @from @into from)

ho :: forall f from into i s t .
	Category from =>
	Precategory into =>
	Covariant Yoneda Functor from into (U_I_II f i) t =>
	Castable Dual into (U_I_II from s t) =>
	Castable Flat into (U_I_II f i t) =>
	f i s -> into (from s t) (f i t)
ho x = unwrap `compose` yo @from @into @(U_I_II f _) (U_I_II x)

hokl :: forall f from into (i :: *) s t .
	Category from =>
	Component Natural from into (T_TT_I (U_I_II f i) (U_I_II f i)) (U_I_II f i) =>
	Covariant Functor into into (U_I_II f i) =>
	Covariant Yoneda Functor from into (U_I_II f i) (f i t) =>
	Castable Dual into (U_I_II from s (f i t)) =>
	Castable Dual into (U_I_II from s t) =>
	Castable Dual into (T_TT_I (U_I_II f i) (U_I_II f i) t) =>
	Castable Flat into (U_I_II f i t) =>
	Castable Dual into (U_I_II f i t) =>
	f i s -> into (from s (f i t)) (f i t)
hokl x = unwrap @into @(U_I_II f i t)
	`compose` component @Flat @from @into @(T_TT_I (U_I_II f i) (U_I_II f i))
	`compose` wrap @into @(T_TT_I (U_I_II f i) (U_I_II f i) _)
	`compose` fo (wrap @into @(U_I_II f i _))
	`compose` yo @from @into @(U_I_II f _) (U_I_II x) 

ha :: forall into from f i s t .
	Category from =>
	Precategory into =>
	Contravariant Yoneda Functor from into (U_II_I f i) t =>
	Castable Dual into (Dual from s t) =>
	Castable Flat into (Dual f i t) =>
	f s i -> into (from t s) (f t i)
ha x = unwrap `compose` ya @from @into @(U_II_I f _) (U_II_I x)

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

ljo :: forall from into f g s t .
	Covariant Adjoint Functor f g from into =>
	Castable Flat into ((T_TT_I g f) s) =>
	Castable Dual into (I s) =>
	from (f s) t -> into s (g t)
ljo from = semifunctor @Flat from
	`compose` unwrap @into
	`compose` component @Flat @from @into @I @(g `T_TT_I` f)
	`compose` wrap @into

rjo :: forall from into f g s t .
	Covariant Adjoint Functor f g from into =>
	Castable Dual from ((T_TT_I f g) t) =>
	Castable Flat from (I t) =>
	into s (g t) -> from (f s) t
rjo from =  unwrap @from
	`compose` component @Flat @into @from @(f `T_TT_I` g) @I
	`compose` wrap @from
	`compose` semifunctor @Flat from

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

u'u :: forall into s t .
	Precategory into =>
	Castable Flat into s =>
	Castable Flat into (Supertype s) =>
	into s (Supertype (Supertype s))
u'u = unwrap @into `compose` unwrap @into
