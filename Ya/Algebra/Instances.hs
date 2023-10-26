{-# OPTIONS_GHC -fno-warn-orphans #-}
{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE UndecidableInstances #-}
module Ya.Algebra.Instances where

import Ya.Algebra.Abstract
import Ya.Algebra.Definition

instance
	( Precategory into
	, forall e . Wrapper into (I e)
	) => Mapping Flat Flat into into I I
	where mapping = rewrap / \from -> rewrap from

instance
	( forall e . Wrapper into (I e)
	, forall e . Wrapper into (TT_T_I I g e)
	, forall e . Wrapper into (T_TT_I I g e)
	, Covariant Endo Semi Functor into g
	) => Mapping Flat Flat into into (T_TT_I I g) (TT_T_I I g)
	where mapping = rewrap / \from -> rewrap /
		semifunctor @Flat @into @into (wrap `compose` from) `compose` unwrap @into

instance
	( Covariant Semi Functor from into g
	, Covariant Endo Semi Functor into f
	, forall e . Wrapper into (T_TT_I f g e)
	) => Mapping Flat Flat from into (T_TT_I f g) (T_TT_I f g)
	where mapping = rewrap / \from -> wrap @into
		`compose` (semifunctor @Flat @into @into
			`compose` semifunctor @Flat @from @into
			) from
		`compose` unwrap @into

instance
	( Covariant Semi Functor from into f
	, Covariant Endo Semi Functor into g
	, forall e . Wrapper into (TT_T_I f g e)
	) => Mapping Flat Flat from into (TT_T_I f g) (TT_T_I f g)
	where mapping = rewrap / \from -> wrap @into
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
	) => Mapping Flat Flat from into (U_I_II (U_I_T_II t u) e) (U_I_II (U_I_T_II t u) e)
	where mapping = rewrap / \from ->
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
	) => Mapping Flat Flat from into (U_II_I (U_I_T_II t u) e) (U_II_I (U_I_T_II t u) e)
	where mapping = rewrap / \from -> 
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
	) => Mapping Flat Flat from into (T_TT_TTT_I f g h) (T_TT_TTT_I f g h)
	where mapping = rewrap / \from -> wrap @into
		`compose` (semifunctor @Flat @into @into
			`compose` semifunctor @Flat @into @into
			`compose` semifunctor @Flat @from @into
			) from
		`compose` unwrap @into

instance Mapping Flat Flat Arrow Arrow (That (/\) e) (That (/\) e)
	where mapping = rewrap / \from -> rewrap / \case
		These e x -> These e (from x)

instance Mapping Flat Flat Arrow Arrow (This (/\) e) (This (/\) e)
	where mapping = rewrap / \from -> rewrap / \case
		These x e -> These (from x) e

instance Mapping Flat Flat Arrow Arrow (That (\/) e) (That (\/) e)
	where mapping = rewrap / \from -> rewrap / \case
		That x -> That (from x)
		This e -> This e

instance Mapping Flat Flat Arrow Arrow (This (\/) e) (This (\/) e)
	where mapping = rewrap / \from -> rewrap / \case
		This x -> This (from x)
		That e -> That e

instance
	( Covariant Semi Functor from into t
	, Covariant Semi Functor from into tt
	, forall e . Covariant Endo Semi Functor into (U_I_II u (t e))
	, forall e . Covariant Endo Semi Functor into (U_II_I u (tt e))
	, forall e . Wrapper into (U_T_I_TT_I u t tt e)
	, forall e ee . Wrapper into (U_I_II u (t e) (tt ee))
	, forall e ee . Wrapper into (U_II_I u (tt e) (t ee))
	) => Mapping Flat Flat from into (U_T_I_TT_I u t tt) (U_T_I_TT_I u t tt)
	where mapping = rewrap / \from -> rewrap /
		_i (map @Flat @Flat @into @into `compose` map @Flat @Flat @from @into / from) `compose`
		i_ (map @Flat @Flat @into @into `compose` map @Flat @Flat @from @into / from)

-- 1. u (t (g s)) (tt (g s))
-- 2. u (g (t s)) (tt (g s))
-- 3. u (g (t s)) (g (tt s))
-- 4. g (u (t s) (g (tt s)))
-- 5. g (g (u (t s) (tt s)))
-- 6. g (u (t s) (tt s))

instance
	( forall e . Mapping Flat Flat Arrow Arrow (U_II_I u e `T_TT_I` g) (U_II_I u e `TT_T_I` g)
	, Mapping Flat Flat from Arrow (t `T_TT_I` g) (t `TT_T_I` g)
	, Mapping Flat Flat from Arrow (tt `T_TT_I` g) (tt `TT_T_I` g)
	, forall e . Covariant Endo Semi Functor Arrow (This u e)
	, forall e . Covariant Endo Semi Functor Arrow (That u e)
	, Covariant Monoidal Functor from u u g
	, forall e . Castable Dual from (U_T_I_TT_I u t tt e)
	) => Mapping Flat Flat from Arrow (U_T_I_TT_I u t tt `T_TT_I` g) (U_T_I_TT_I u t tt `TT_T_I` g)
	where mapping = rewrap / \from -> rewrap @Arrow @(T_TT_I _ _ _) @(TT_T_I _ _ _) /
			map @Flat @Flat @from @Arrow @g @g (wrap @from @(U_T_I_TT_I u t tt _)) `compose`
			-- TODO: the problem is here, we need to generalize `monoidal`
			monoidal @Flat @from identity identity `compose`
			unwrap @Arrow @(U_I_II u (g (t _)) (g (tt _))) `compose`
			map @Flat @Flat @Arrow @Arrow @(U_I_II u _) @(U_I_II u _)
				( wrapped @Arrow `compose` map @Flat @Flat @from @Arrow @(tt `T_TT_I` g) @(tt `TT_T_I` g) / from
				) `compose`
			wrap @Arrow @(U_I_II u (g (t _)) (tt (g _))) `compose`
			unwrap @Arrow @(U_II_I u (tt (g _)) (g (t _))) `compose`
			map @Flat @Flat @Arrow @Arrow @(U_II_I u _) @(U_II_I u _)
				( wrapped @Arrow `compose` map @Flat @Flat @from @Arrow @(t `T_TT_I` g) @(t `TT_T_I` g) / from
				) `compose`
			wrap @Arrow @(U_II_I u (tt (g _)) (t (g _))) `compose`
			unwrap @Arrow @(U_T_I_TT_I u t tt _)

-- TODO: I cannot generalize instance above to an instance below
-- since `monoidal` expression is not generalized enough
-- instance
	-- ( forall e . Mapping Flat into into (U_II_I u e `T_TT_I` g) (g `T_TT_I` U_II_I u e)
	-- , Mapping Flat from into (t `T_TT_I` g) (g `T_TT_I` t)
	-- , Mapping Flat from into (tt `T_TT_I` g) (g `T_TT_I` tt)
	-- ) => Mapping Flat from into (U_T_I_TT_I u t tt `T_TT_I` g) (g `T_TT_I` U_T_I_TT_I u t tt)
	-- where mapping (U_I_II from) = rewrap @into @(T_TT_I _ _ _) @(T_TT_I _ _ _) /
		-- -- TODO: try to apply monoidal functor here	
			-- 
			-- map @Flat @from @into @g @g (wrap @into @(U_T_I_TT_I u t tt _)) `compose`
			-- -- TODO: the problem is here, we need to generalize `monoidal`
			-- monoidal @Flat @from identity identity `compose`
		-- -- (
			-- unwrap @into @(U_I_II u (g (t _)) (g (tt _))) `compose`
			-- map @Flat @into @into @(U_I_II u _) @(U_I_II u _)
				-- ( wrapped @into `compose` map @Flat @from @into @(tt `T_TT_I` g) @(g `T_TT_I` tt) / from
				-- ) `compose`
			-- wrap @into @(U_I_II u (g (t _)) (tt (g _))) `compose`
	-- 
			-- unwrap @into @(U_II_I u (tt (g _)) (g (t _))) `compose`
			-- map @Flat @into @into @(U_II_I u _) @(U_II_I u _)
				-- ( wrapped @into `compose` map @Flat @from @into @(t `T_TT_I` g) @(g `T_TT_I` t) / from
				-- ) `compose`
			-- wrap @into @(U_II_I u (tt (g _)) (t (g _))) `compose`
-- 
			-- unwrap @into @(U_T_I_TT_I u t tt _)
		-- -- :: _)

-- TODO: generalize
instance Covariant Yoneda Functor Arrow Arrow g =>
	Mapping Flat Flat Arrow Arrow (This (/\) e `T_TT_I` g) (This (/\) e `TT_T_I` g)
	where mapping = rewrap / \from -> rewrap @Arrow @(T_TT_I _ _ _) @(TT_T_I _ _ _) /
		\(U_II_I (These x e)) -> yoneda @Flat @Functor x (U_II_I `compose` (\x' -> These (from x') e))
		
instance
	( Covariant Semi Functor into into (U_I_II u e)
	, Covariant Semi Functor from into (U_I_II uu e)
	, forall ee . Wrapper into (U_I_II (W_I_I_II (U_I_UU_II_III u uu)) e ee)
	, forall ee . Wrapper into (W_I_I_II (U_I_UU_II_III u uu) e ee)
	, forall ee . Wrapper into (U_I_UU_II_III u uu e e ee)
	, forall ee . Wrapper into (U_I_II u e ee)
	, forall ee . Wrapper into (U_I_II uu e ee)
	) => Mapping Flat Flat from into
	(U_I_II (W_I_I_II (U_I_UU_II_III u uu)) e)
	(U_I_II (W_I_I_II (U_I_UU_II_III u uu)) e)
	where mapping = rewrap / \from ->
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

instance Mapping Flat Flat Arrow Arrow
	(UU_V_U_I_II_T_II Flat Arrow Arrow f i)
	(UU_V_U_I_II_T_II Flat Arrow Arrow f i)
	where mapping = rewrap / \from -> rewrap (`compose` (rewrap (`compose` from)))

instance Mapping Flat Flat Arrow Arrow
	(UU_V_U_I_II_T_II Flat Constant Arrow f i)
	(UU_V_U_I_II_T_II Flat Constant Arrow f i)
	where mapping = rewrap / \_ -> rewrap (`compose` (rewrap (rewrap identity)))

instance Mapping Dual Flat Arrow Arrow
	(UU_V_U_I_II_T_II Dual Arrow Arrow f i)
	(UU_V_U_I_II_T_II Dual Arrow Arrow f i)
	where mapping = rewrap / \from -> rewrap (`compose` (rewrap (compose (from))))

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
	) => Mapping Flat Flat from into (R_U_I_T_I u t) (R_U_I_T_I u t)
	where mapping = rewrap / \from ->
		wrap @into @(R_U_I_T_I u t _)
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

instance Mapping Flat Flat Arrow Arrow (U_I_II Arrow s) (U_I_II Arrow s)
	where mapping (U_I_II from) = U_I_II / \(U_I_II between) -> U_I_II (\x -> from (between x))

instance Mapping Dual Flat Arrow Arrow (U_II_I Arrow t) (U_II_I Arrow t)
	where mapping (U_II_I from) = U_I_II / \(U_II_I between) -> U_II_I (\x -> between (from x))

instance Category Arrow where
	identity = \x -> x

instance Mapping Flat Flat Arrow Arrow (U_I_II Constant s) (U_I_II Constant s)
	where mapping = rewrap / \from (U_I_II (Constant x)) -> U_I_II (Constant (from x))

instance Mapping Dual Flat Arrow Arrow (U_II_I Constant t) (U_II_I Constant t)
	where mapping = rewrap / \_ (U_II_I (Constant x)) -> U_II_I (Constant (x))

instance Mapping Flat Flat Arrow into f g => Mapping Flat Flat Constant into f g
	where mapping (U_I_II (Constant x)) = mapping (U_I_II (\_ -> x))

instance Mapping Dual Flat Arrow into f g => Mapping Dual Flat Constant into f g
	where mapping (U_II_I (Constant x)) = mapping (U_II_I (\_ -> x))

instance Mapping Flat Flat Arrow Arrow I (Both (/\))
	where mapping (U_I_II from) = U_I_II / \(I x) -> U_I_I (These (from x) (from x))

instance Mapping Flat Flat Arrow Arrow (U_I_II (/\) e) I
	where mapping (U_I_II from) = U_I_II / \(U_I_II (These _ x)) -> I (from x)

instance Mapping Flat Flat Arrow Arrow (U_II_I (/\) e) I
	where mapping (U_I_II from) = U_I_II / \(U_II_I (These x _)) -> I (from x)

instance Mapping Flat Flat Arrow Arrow (Both (\/)) I
	where mapping (U_I_II from) = U_I_II / \case
		U_I_I (This x) -> I (from x)
		U_I_I (That x) -> I (from x)

instance Mapping Flat Flat Arrow Arrow I (U_I_II (\/) e)
	where mapping (U_I_II from) = U_I_II / \(I x) -> U_I_II (That (from x))

instance Mapping Flat Flat Arrow Arrow I (U_II_I (\/) e)
	where mapping (U_I_II from) = U_I_II / \(I x) -> U_II_I (This (from x))
