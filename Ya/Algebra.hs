{-# OPTIONS_GHC -fno-warn-orphans #-}
{-# LANGUAGE UndecidableInstances #-}
module Ya.Algebra (module Exports) where

import Ya.Algebra.Abstract as Exports
import Ya.Algebra.Definition as Exports
import Ya.Algebra.Operators as Exports

instance
	( Precategory into
	, forall e . Wrapper into (I e)
	) => Mapping Flat into into I I
	where mapping (U_I_II from) = w'u from

instance
	( Covariant Semi Functor from into g
	, Covariant Endo Semi Functor into f
	, forall e . Wrapper into (T_TT_I f g e)
	) => Mapping Flat from into (T_TT_I f g) (T_TT_I f g)
	where mapping (U_I_II from) = w'u `i` fo'fo from

instance
	( Covariant Semi Functor from into h
	, Covariant Endo Semi Functor into g
	, Covariant Endo Semi Functor into f
	, forall e . Wrapper into (T_TT_TTT_I f g h e)
	) => Mapping Flat from into (T_TT_TTT_I f g h) (T_TT_TTT_I f g h)
	where mapping (U_I_II from) = w'u `i` fo'fo'fo from

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
	where mapping (U_I_II from) = w'u (fa_ @from @into (w'u (fa_ @from @from from)))

-- instance Mapping Flat Arrow Arrow (U_I_II Constant s) (U_I_II Constant s)
-- instance Mapping Flat Arrow Arrow (U_I_II Constant s) (U_I_II Constant s)
	-- where mapping (U_I_II from) (U_I_II (Constant x)) = U_I_II (Constant (from x))

-- instance Mapping Flat Arrow Arrow (U_II_I Constant t) (U_II_I Constant t)
	-- where mapping _ (U_II_I (Constant x)) = U_II_I (Constant x)

-- instance Covariant Semi Functor Arrow Arrow f => Mapping Flat Constant Arrow f f
	-- where mapping (U_I_II (Constant new)) = fo `i` \_ -> new

-- instance Covariant Semi Functor (Kleisli g Arrow) Arrow f
	-- => Mapping Flat (Kleisli g Constant) Arrow f f
	-- where mapping (U_I_II (U_I_T_II (Constant new))) = fokl `i` \_ -> new

-- instance Contravariant Semi Functor Arrow Arrow f => Mapping Dual Constant Arrow f f
	-- where mapping (U_II_I (Constant new)) = fa `i` \_ -> new

-- instance (Covariant Semi Functor Arrow Arrow f, Component Natural Arrow Arrow (f `T_TT_I` g) f)
	-- => Mapping Flat (Kleisli g Arrow) Arrow f f
	-- where mapping (U_I_II (U_I_T_II from)) =
		-- component @Flat @Arrow @Arrow @(f `T_TT_I` g) @f `compose` wrap `compose` fo from

-- Required by `Mapping Flat (Kleisli g Arrow) Arrow f f`
-- instance Mapping Flat Arrow Arrow (f `T_TT_I` g) f =>
	-- Mapping Flat Arrow Arrow (Flat (Kleisli f Arrow) i `T_TT_I` g) (Flat (Kleisli f Arrow) i)
	-- where mapping (U_I_II from) (T_TT_I (U_I_II (U_I_T_II x))) =
		-- U_I_II (U_I_T_II (\e -> map @Flat @Arrow @Arrow @(f `T_TT_I` g) @f from (T_TT_I (x e))))

-- instance Covariant Semi Functor Arrow Arrow g
	-- => Mapping Flat Arrow Arrow (Flat (Kleisli g Arrow) i) (Flat (Kleisli g Arrow) i)
	-- where mapping (U_I_II from) (U_I_II (U_I_T_II x)) =
		-- U_I_II (U_I_T_II (from `_fo'fo` x))

-- instance Mapping Dual Arrow Arrow (Dual (Kleisli g Arrow) i) (Dual (Kleisli g Arrow) i)
	-- where mapping (U_II_I from) (U_II_I (U_I_T_II x)) =
		-- U_II_I (U_I_T_II (unwrap (from `fa` U_II_I x)))

-- We need this instance to complete Precategory instance for `Kleisli f Arrow`
-- instance (Covariant Semi Functor Arrow Arrow g, Semi Natural Transformation Arrow Arrow (g `T_TT_I` f) f) =>
-- instance (Covariant Semi Functor Arrow Arrow g, Transformation Flat Precategory Arrow Arrow (g `T_TT_I` f) f) =>
	-- Mapping Dual (Kleisli g Arrow) Arrow (Dual (Kleisli f Arrow) i) (Dual (Kleisli f Arrow) i)
	-- where mapping (U_II_I (U_I_T_II from)) (U_II_I (U_I_T_II between)) =
		-- U_II_I (U_I_T_II (component @Flat @Arrow @Arrow @(g `T_TT_I` f) @f `compose` T_TT_I `compose` fo between `compose` from))

-- instance 
	-- ( Covariant Semi Functor Arrow Arrow g 
	-- , Mapping Flat Arrow Arrow (g `T_TT_I` g) g
	-- ) => Category (Kleisli g Arrow) where -- TODO

instance
	( Covariant Semi Functor from Arrow f
	, forall e . Covariant Semi Functor into Arrow (U_I_II from e)
	) => Mapping Flat from Arrow f (UU_V_U_I_II_T_II Flat into Arrow f r)
	where mapping (U_I_II from) x = UU_V_U_I_II_T_II (\(U_I_II e) -> e `_fo` from `fo'fi` x)

instance Mapping Flat Arrow Arrow (Day (Flat Arrow) (/\) (/\) I I i ii) I
	where mapping (U_I_II from) = \case
		U_UU_UUU_UUUU_T_TT_I_II_III (These (These (I i) (I ii)) (U_I_II f))
			-> I (from (f (These i ii)))

instance Mapping Flat Arrow Arrow (Flat Arrow Unit) I
	where mapping (U_I_II from) (U_I_II f) = I (from (f Unit))

instance Mapping Flat Arrow Arrow (Day (Flat Arrow) (/\) (/\) (U_I_II (\/) e) (U_I_II (\/) e) i ii) (U_I_II (\/) e)
	where mapping (U_I_II from) = \case
		U_UU_UUU_UUUU_T_TT_I_II_III (These (These (U_I_II (That i)) (U_I_II (That ii))) (U_I_II f))
			-> U_I_II (That (from (f (These i ii))))
		U_UU_UUU_UUUU_T_TT_I_II_III (These (These (U_I_II (This e)) _) (U_I_II f))
			-> U_I_II (This e)

instance Mapping Flat Arrow Arrow (Day (Flat Arrow) (/\) (\/) (U_I_II (\/) e) (U_I_II (\/) e) i ii) (U_I_II (\/) e)
	where mapping (U_I_II from) = \case
		U_UU_UUU_UUUU_T_TT_I_II_III (These (These (U_I_II (That i)) _) (U_I_II f))
			-> U_I_II (That (from (f (This i))))
		U_UU_UUU_UUUU_T_TT_I_II_III (These (These _ (U_I_II (That ii))) (U_I_II f))
			-> U_I_II (That (from (f (That ii))))
		U_UU_UUU_UUUU_T_TT_I_II_III (These (These _ (U_I_II (This ii))) (U_I_II f))
			-> U_I_II (This ii)

instance Mapping Flat Arrow Arrow (Flat Arrow Unit) (U_I_II (\/) e)
	where mapping (U_I_II from) (U_I_II f) = U_I_II (That (from (f Unit)))

instance Mapping Flat Arrow Arrow (Day (Flat Arrow) (/\) (/\) (U_II_I (\/) e) (U_II_I (\/) e) i ii) (U_II_I (\/) e)
	where mapping (U_I_II from) = \case
		U_UU_UUU_UUUU_T_TT_I_II_III (These (These (U_II_I (This i)) (U_II_I (This ii))) (U_I_II f))
			-> U_II_I (This (from (f (These i ii))))
		U_UU_UUU_UUUU_T_TT_I_II_III (These (These (U_II_I (That e)) _) (U_I_II f))
			-> U_II_I (That e)

instance Mapping Flat Arrow Arrow (Day (Flat Arrow) (/\) (\/) (U_II_I (\/) e) (U_II_I (\/) e) i ii) (U_II_I (\/) e)
	where mapping (U_I_II from) = \case
		U_UU_UUU_UUUU_T_TT_I_II_III (These (These (U_II_I (This i)) _) (U_I_II f))
			-> U_II_I (This (from (f (This i))))
		U_UU_UUU_UUUU_T_TT_I_II_III (These (These _ (U_II_I (This ii))) (U_I_II f))
			-> U_II_I (This (from (f (That ii))))
		U_UU_UUU_UUUU_T_TT_I_II_III (These (These _ (U_II_I (That ii))) (U_I_II f))
			-> U_II_I (That ii)

instance Mapping Flat Arrow Arrow (Flat Arrow Unit) (U_II_I (\/) e)
	where mapping (U_I_II from) (U_I_II f) = U_II_I (This (from (f Unit)))
