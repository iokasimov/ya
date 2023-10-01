{-# OPTIONS_GHC -fno-warn-orphans #-}
{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE UndecidableInstances #-}
module Ya.Algebra.Instances where

import Ya.Algebra.Abstract
import Ya.Algebra.Definition

instance
	( Precategory into
	, forall e . Wrapper into (I e)
	) => Mapping Flat into into I I
	where mapping (U_I_II from) = wrap @into `compose` from `compose` unwrap @into

instance
	( Covariant Semi Functor from into g
	, Covariant Endo Semi Functor into f
	, forall e . Wrapper into (T_TT_I f g e)
	) => Mapping Flat from into (T_TT_I f g) (T_TT_I f g)
	where mapping (U_I_II from) = wrap @into
		`compose` (semifunctor @Flat @into @into
			`compose` semifunctor @Flat @from @into
			) from
		`compose` unwrap @into

instance
	( Covariant Semi Functor from into h
	, Covariant Endo Semi Functor into g
	, Covariant Endo Semi Functor into f
	, forall e . Wrapper into (T_TT_TTT_I f g h e)
	) => Mapping Flat from into (T_TT_TTT_I f g h) (T_TT_TTT_I f g h)
	where mapping (U_I_II from) = wrap @into
		`compose` (semifunctor @Flat @into @into
			`compose` semifunctor @Flat @into @into
			`compose` semifunctor @Flat @from @into
			) from
		`compose` unwrap @into

instance
	( forall e . Wrapper from (U_I_II from e i)
	, forall e . Wrapper from (U_II_I from i e)
	, forall e . Wrapper into (U_II_I into (f i) (Flat from e i))
	, forall e . Wrapper into (UU_V_U_I_II_T_II Flat from into f i e)
	, Contravariant Endo Semi Functor from (U_II_I from i)
	, Contravariant Semi Functor from into (U_II_I into (f i))
	) => Mapping Flat from into
		(UU_V_U_I_II_T_II Flat from into f i)
		(UU_V_U_I_II_T_II Flat from into f i)
	where mapping (U_I_II from) = wrap @into @(UU_V_U_I_II_T_II _ _ _ _ _ _)
		`compose` unwrap @into @(U_II_I _ _ _)
		`compose` semifunctor @Dual @from @into
			(wrap @from `compose` unwrap @from @(U_II_I _ _ _)
				`compose` semifunctor @Dual @from @from from
	 		`compose` wrap @from @(U_II_I _ _ _) `compose` unwrap @from)
		`compose` wrap @into @(U_II_I _ _ _)
		`compose` unwrap @into @(UU_V_U_I_II_T_II _ _ _ _ _ _)

instance
	( forall e . Covariant Semi Functor from into (U_I_II (U_I_T_II t u) e)
	, forall e . Covariant Semi Functor from into (U_II_I (U_I_T_II t u) e)
	, forall e . Covariant Endo Semi Functor from (U_I_II (U_I_T_II t u) e)
	, forall e . Covariant Endo Semi Functor from (U_II_I (U_I_T_II t u) e)
	, forall e . Wrapper from (R_U_I_T_I u t e)
	, forall e . Wrapper into (R_U_I_T_I u t e)
	, forall e . Wrapper from (Recursive (U_I_T_II t u e))
	, forall e . Wrapper into (Recursive (U_I_T_II t u e))
	, forall e e' . Wrapper from (U_II_I (U_I_T_II t u) e e')
	, forall e e' . Wrapper into (U_II_I (U_I_T_II t u) e e')
	, forall e e' . Wrapper from (U_I_II (U_I_T_II t u) e e')
	, forall e e' . Wrapper into (U_I_II (U_I_T_II t u) e e')
	) => Mapping Flat from into (R_U_I_T_I u t) (R_U_I_T_I u t)
	where mapping (U_I_II from) = wrap @into @(R_U_I_T_I u t _)
		`compose` wrap @into @(Recursive _)
		`compose` unwrap @into @(U_II_I _ _ _)
		`compose` semifunctor @Flat from
		`compose` wrap @into @(U_II_I _ _ _)
		`compose` unwrap @into @(U_I_II _ _ _)
		`compose` semifunctor @Flat
			(unwrap @from
			`compose` semifunctor @Flat @from from
			`compose` wrap @from @(R_U_I_T_I u t _))
		`compose` wrap @into @(U_I_II _ _ _)
		`compose` unwrap @into @(Recursive _)
		`compose` unwrap @into @(R_U_I_T_I u t _)

instance Mapping Flat Arrow Arrow (U_I_II Arrow s) (U_I_II Arrow s)
	where mapping (U_I_II from) (U_I_II between) = U_I_II (\x -> from (between x))

instance Mapping Dual Arrow Arrow (U_II_I Arrow t) (U_II_I Arrow t)
	where mapping (U_II_I from) (U_II_I between) = U_II_I (\x -> between (from x))

instance Category Arrow where
	identity = \x -> x
