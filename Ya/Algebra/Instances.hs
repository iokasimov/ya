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
	( Covariant Semi Functor from into f
	, Covariant Endo Semi Functor into g
	, forall e . Wrapper into (TT_T_I f g e)
	) => Mapping Flat from into (TT_T_I f g) (TT_T_I f g)
	where mapping (U_I_II from) = wrap @into
		`compose` (semifunctor @Flat @into @into
			`compose` semifunctor @Flat @from @into
			) from
		`compose` unwrap @into

instance
	( Covariant Semi Functor from into t
	, forall ee . Covariant Endo Semi Functor into (U_I_II u ee)
	, forall ee . Wrapper into (U_I_II (U_I_T_II t u) e ee)
	, forall ee . Wrapper into (U_I_T_II t u e ee)
	, forall ee . Wrapper into (U_I_II u e (t ee))
	) => Mapping Flat from into (U_I_II (U_I_T_II t u) e) (U_I_II (U_I_T_II t u) e)
	where mapping (U_I_II from) =
		wrap @into @(U_I_II _ _ _)
		`compose` wrap @into @(U_I_T_II _ _ _ _)
		`compose` unwrap @into @(U_I_II _ _ _)
		`compose` semifunctor @Flat @into @into (semifunctor @Flat @from @into from)
		`compose` wrap @into @(U_I_II _ _ _)
		`compose` unwrap @into @(U_I_T_II _ _ _ _)
		`compose` unwrap @into @(U_I_II _ _ _)

instance
	( forall ee . Covariant Semi Functor from into (U_II_I u ee)
	, forall ee . Wrapper into (U_II_I (U_I_T_II t u) e ee)
	, forall ee . Wrapper into (U_I_T_II t u ee e)
	, forall ee . Wrapper into (U_II_I u (t e) ee)
	) => Mapping Flat from into (U_II_I (U_I_T_II t u) e) (U_II_I (U_I_T_II t u) e)
	where mapping (U_I_II from) =
		wrap @into @(U_II_I _ _ _)
		`compose` wrap @into @(U_I_T_II _ _ _ _)
		`compose` unwrap @into @(U_II_I _ _ _)
		`compose` semifunctor @Flat @from @into from
		`compose` wrap @into @(U_II_I _ _ _)
		`compose` unwrap @into @(U_I_T_II _ _ _ _)
		`compose` unwrap @into @(U_II_I _ _ _)

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
	( Category from
	, Precategory into
	, Limit from into U_I_I
	, Limit into into U_I_I
	, forall ee . Mapping Flat from into (This (Product Object into) ee) I
	, forall ee . Mapping Flat from into (That (Product Object into) ee) I
	, forall ee . Wrapper into (This (Product Object into) ee e)
	, forall ee . Wrapper into (That (Product Object into) e ee)
	, forall ee . Wrapper into (I ee)
	) => Mapping Flat from into (That (Product Object into) e) (That (Product Object into) e)
	where mapping (U_I_II from) = rewrap / project @This @from identity /\ project @That from

instance
	( Category from
	, Precategory into
	, Limit from into U_I_I
	, Limit into into U_I_I
	, forall ee . Mapping Flat from into (This (Product Object into) ee) I
	, forall ee . Mapping Flat from into (That (Product Object into) ee) I
	, forall ee . Wrapper into (This (Product Object into) e ee)
	, forall ee . Wrapper into (That (Product Object into) ee e)
	, forall ee . Wrapper into (I ee)
	) => Mapping Flat from into (This (Product Object into) e) (This (Product Object into) e)
	where mapping (U_I_II from) = rewrap / project @This from /\ project @That @from identity

instance
	( Category from
	, Precategory into
	, Co Limit from into U_I_I
	, Co Limit into into U_I_I
	, forall ee . Mapping Flat from into I (This (Sum Object into) ee)
	, forall ee . Mapping Flat from into I (That (Sum Object into) ee)
	, forall ee . Wrapper into (This (Sum Object into) ee e)
	, forall ee . Wrapper into (That (Sum Object into) e ee)
	, forall ee . Wrapper into (I ee)
	) => Mapping Flat from into (That (Sum Object into) e) (That (Sum Object into) e)
	where mapping (U_I_II from) = rewrap / inject @This @from identity \/ inject @That from

instance
	( Category from
	, Precategory into
	, Co Limit from into U_I_I
	, Co Limit into into U_I_I
	, forall ee . Mapping Flat from into I (This (Sum Object into) ee)
	, forall ee . Mapping Flat from into I (That (Sum Object into) ee)
	, forall ee . Wrapper into (This (Sum Object into) e ee)
	, forall ee . Wrapper into (That (Sum Object into) ee e)
	, forall ee . Wrapper into (I ee)
	) => Mapping Flat from into (This (Sum Object into) e) (This (Sum Object into) e)
	where mapping (U_I_II from) = rewrap / inject @This from \/ inject @That @from identity

instance
	( Covariant Semi Functor into into (U_I_II u e)
	, Covariant Semi Functor from into (U_I_II uu e)
	, forall ee . Wrapper into (U_I_II (W_I_I_II (U_I_UU_II_III u uu)) e ee)
	, forall ee . Wrapper into (W_I_I_II (U_I_UU_II_III u uu) e ee)
	, forall ee . Wrapper into (U_I_UU_II_III u uu e e ee)
	, forall ee . Wrapper into (U_I_II u e ee)
	, forall ee . Wrapper into (U_I_II uu e ee)
	) => Mapping Flat from into
	(U_I_II (W_I_I_II (U_I_UU_II_III u uu)) e)
	(U_I_II (W_I_I_II (U_I_UU_II_III u uu)) e)
	where mapping (U_I_II from) =
		wrap @into @(U_I_II _ _ _)
		`compose` wrap @into @(W_I_I_II _ _ _)
		`compose` wrap @into @(U_I_UU_II_III _ _ _ _ _)
		`compose` unwrap @into @(U_I_II u _ _)
		`compose` semifunctor @Flat @into @into
			(unwrap @into @(U_I_II uu _ _)
			`compose` semifunctor @Flat @from @into from
			`compose` wrap @into @(U_I_II uu _ _))
		`compose` wrap @into @(U_I_II u _ _)
		`compose` unwrap @into @(U_I_UU_II_III _ _ _ _ _)
		`compose` unwrap @into @(W_I_I_II _ _ _)
		`compose` unwrap @into @(U_I_II _ _ _)

instance Mapping Flat Arrow Arrow
	(UU_V_U_I_II_T_II Flat Arrow Arrow f i)
	(UU_V_U_I_II_T_II Flat Arrow Arrow f i)
	where mapping from = rewrap (`compose` (rewrap (`compose` unwrap from)))

instance Mapping Flat Arrow Arrow
	(UU_V_U_I_II_T_II Flat Constant Arrow f i)
	(UU_V_U_I_II_T_II Flat Constant Arrow f i)
	where mapping _ = rewrap (`compose` (rewrap (rewrap identity)))

instance Mapping Dual Arrow Arrow
	(UU_V_U_I_II_T_II Dual Arrow Arrow f i)
	(UU_V_U_I_II_T_II Dual Arrow Arrow f i)
	where mapping from = rewrap (`compose` (rewrap (compose (unwrap from)) ))

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

instance Wrapper Arrow x
	=> Castable Flat (W_I_II_II (U_I_UU_III_U_II_I (->) (/\))) x where
	cast = U_I_II (W_I_II_II (U_I_UU_III_U_II_I (\x -> These (unwrap x) wrap)))

instance Wrapper Arrow x
	=> Castable Dual (W_I_II_II (U_I_UU_III_U_II_I (->) (/\))) x where
	cast = U_II_I (W_I_II_II (U_I_UU_III_U_II_I (\x -> These (wrap x) unwrap)))

instance Mapping Flat Arrow Arrow (U_I_II Constant s) (U_I_II Constant s)
	where mapping (U_I_II from) (U_I_II (Constant x)) = U_I_II (Constant (from x))

instance Mapping Dual Arrow Arrow (U_II_I Constant t) (U_II_I Constant t)
	where mapping _ (U_II_I (Constant x)) = U_II_I (Constant (x))

instance Mapping Flat Arrow into f g => Mapping Flat Constant into f g
	where mapping (U_I_II (Constant x)) = mapping (U_I_II (\_ -> x))

instance Mapping Dual Arrow into f g => Mapping Dual Constant into f g
	where mapping (U_II_I (Constant x)) = mapping (U_II_I (\_ -> x))
