{-# OPTIONS_GHC -fno-warn-orphans #-}
module Ya.Algebra (module Exports) where

import Ya.Algebra.Abstract as Exports
import Ya.Algebra.Definition as Exports
import Ya.Algebra.Operators as Exports

instance (Covariant Semifunctor f Arrow Arrow, Covariant Semifunctor g Arrow Arrow)
	=> Transformation Flat Arrow Arrow (f `T_TT_I` g) (f `T_TT_I` g)
	where transformation (U_I_II from) (T_TT_I x) = T_TT_I (from `fo'fo` x)

instance (Covariant Semifunctor f Arrow Arrow, Transformation Flat Arrow Arrow (f `T_TT_I` g) f)
	=> Transformation Flat (Kleisli g Arrow) Arrow f f
	where transformation (U_I_II (U_I_T_II from)) =
		component @Flat @Arrow @Arrow @(f `T_TT_I` g) @f `compose` wrap `compose` fo from

-- Required by `Transformation Flat (Kleisli g Arrow) Arrow f f`
instance Transformation Flat Arrow Arrow (f `T_TT_I` g) f =>
	Transformation Flat Arrow Arrow (Flat (Kleisli f Arrow) i `T_TT_I` g) (Flat (Kleisli f Arrow) i)
	where transformation (U_I_II from) (T_TT_I (U_I_II (U_I_T_II x))) =
		U_I_II (U_I_T_II (\e -> transform @Flat @Arrow @Arrow @(f `T_TT_I` g) @f from (T_TT_I (x e))))

instance Covariant Semifunctor g Arrow Arrow
	=> Transformation Flat Arrow Arrow (Flat (Kleisli g Arrow) i) (Flat (Kleisli g Arrow) i)
	where transformation (U_I_II from) (U_I_II (U_I_T_II x)) =
		U_I_II (U_I_T_II (from `_fo'fo` x))

instance Transformation Dual Arrow Arrow (Dual (Kleisli g Arrow) i) (Dual (Kleisli g Arrow) i)
	where transformation (U_II_I from) (U_II_I (U_I_T_II x)) =
		U_II_I (U_I_T_II (unwrap (from `fa` U_II_I x)))

-- We need this instance to complete Semigroupoid instance for `Kleisli f Arrow`
instance (Covariant Semifunctor g Arrow Arrow, Transformation Flat Arrow Arrow (g `T_TT_I` f) f) =>
	Transformation Dual (Kleisli g Arrow) Arrow (Dual (Kleisli f Arrow) i) (Dual (Kleisli f Arrow) i)
	where transformation (U_II_I (U_I_T_II from)) (U_II_I (U_I_T_II between)) =
		U_II_I (U_I_T_II (component @Flat @Arrow @Arrow @(g `T_TT_I` f) @f `compose` T_TT_I `compose` fo between `compose` from))