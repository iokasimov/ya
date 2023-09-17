{-# OPTIONS_GHC -fno-warn-orphans #-}
module Ya.Algebra (module Exports) where

import Ya.Algebra.Abstract as Exports
import Ya.Algebra.Definition as Exports
import Ya.Algebra.Operators as Exports

instance Transformation Flat (U_I_II Constant s) (U_I_II Constant s) Arrow Arrow
	where transformation (U_I_II from) (U_I_II (Constant x)) = U_I_II (Constant (from x))

instance Transformation Flat (U_II_I Constant t) (U_II_I Constant t) Arrow Arrow
	where transformation _ (U_II_I (Constant x)) = U_II_I (Constant x)

instance Covariant Semi Functor Arrow Arrow f => Transformation Flat f f Constant Arrow
	where transformation (U_I_II (Constant new)) = fo `i` \_ -> new

instance Covariant Semi Functor (Kleisli g Arrow) Arrow f
	=> Transformation Flat f f (Kleisli g Constant) Arrow
	where transformation (U_I_II (U_I_T_II (Constant new))) = fokl `i` \_ -> new

instance Contravariant Semi Functor Arrow Arrow f => Transformation Dual f f Constant Arrow
	where transformation (U_II_I (Constant new)) = fa `i` \_ -> new

instance (Covariant Semi Functor Arrow Arrow f, Covariant Semi Functor Arrow Arrow g)
	=> Transformation Flat (f `T_TT_I` g) (f `T_TT_I` g) Arrow Arrow
	where transformation (U_I_II from) (T_TT_I x) = T_TT_I (from `fo'fo` x)

instance (Covariant Semi Functor Arrow Arrow f, Transformation Flat (f `T_TT_I` g) f Arrow Arrow)
	=> Transformation Flat f f (Kleisli g Arrow) Arrow
	where transformation (U_I_II (U_I_T_II from)) =
		component @Flat @Arrow @Arrow @(f `T_TT_I` g) @f `compose` wrap `compose` fo from

-- Required by `Transformation Flat (Kleisli g Arrow) Arrow f f`
instance Transformation Flat (f `T_TT_I` g) f Arrow Arrow =>
	Transformation Flat (Flat (Kleisli f Arrow) i `T_TT_I` g) (Flat (Kleisli f Arrow) i) Arrow Arrow
	where transformation (U_I_II from) (T_TT_I (U_I_II (U_I_T_II x))) =
		U_I_II (U_I_T_II (\e -> transform @Flat @Arrow @Arrow @(f `T_TT_I` g) @f from (T_TT_I (x e))))

instance Covariant Semi Functor Arrow Arrow g
	=> Transformation Flat (Flat (Kleisli g Arrow) i) (Flat (Kleisli g Arrow) i) Arrow Arrow
	where transformation (U_I_II from) (U_I_II (U_I_T_II x)) =
		U_I_II (U_I_T_II (from `_fo'fo` x))

instance Transformation Dual (Dual (Kleisli g Arrow) i) (Dual (Kleisli g Arrow) i) Arrow Arrow
	where transformation (U_II_I from) (U_II_I (U_I_T_II x)) =
		U_II_I (U_I_T_II (unwrap (from `fa` U_II_I x)))

-- We need this instance to complete Semigroupoid instance for `Kleisli f Arrow`
instance (Covariant Semi Functor Arrow Arrow g, Transformation Flat (g `T_TT_I` f) f Arrow Arrow) =>
	Transformation Dual (Dual (Kleisli f Arrow) i) (Dual (Kleisli f Arrow) i) (Kleisli g Arrow) Arrow
	where transformation (U_II_I (U_I_T_II from)) (U_II_I (U_I_T_II between)) =
		U_II_I (U_I_T_II (component @Flat @Arrow @Arrow @(g `T_TT_I` f) @f `compose` T_TT_I `compose` fo between `compose` from))

instance Transformation Flat (Day (Flat Arrow) (/\) (/\) I I i ii) I Arrow Arrow
	where transformation (U_I_II from) = \case
		U_UU_UUU_UUUU_T_TT_I_II_III (These (These (I i) (I ii)) (U_I_II f))
			-> I (from (f (These i ii)))

instance Transformation Flat (Flat Arrow Unit) I Arrow Arrow
	where transformation (U_I_II from) (U_I_II f) = I (from (f Unit))

instance Transformation Flat (Day (Flat Arrow) (/\) (/\) (U_I_II (\/) e) (U_I_II (\/) e) i ii) (U_I_II (\/) e) Arrow Arrow
	where transformation (U_I_II from) = \case
		U_UU_UUU_UUUU_T_TT_I_II_III (These (These (U_I_II (That i)) (U_I_II (That ii))) (U_I_II f))
			-> U_I_II (That (from (f (These i ii))))
		U_UU_UUU_UUUU_T_TT_I_II_III (These (These (U_I_II (This e)) _) (U_I_II f))
			-> U_I_II (This e)

instance Transformation Flat (Day (Flat Arrow) (/\) (\/) (U_I_II (\/) e) (U_I_II (\/) e) i ii) (U_I_II (\/) e) Arrow Arrow
	where transformation (U_I_II from) = \case
		U_UU_UUU_UUUU_T_TT_I_II_III (These (These (U_I_II (That i)) _) (U_I_II f))
			-> U_I_II (That (from (f (This i))))
		U_UU_UUU_UUUU_T_TT_I_II_III (These (These _ (U_I_II (That ii))) (U_I_II f))
			-> U_I_II (That (from (f (That ii))))
		U_UU_UUU_UUUU_T_TT_I_II_III (These (These _ (U_I_II (This ii))) (U_I_II f))
			-> U_I_II (This ii)

instance Transformation Flat (Flat Arrow Unit) (U_I_II (\/) e) Arrow Arrow
	where transformation (U_I_II from) (U_I_II f) = U_I_II (That (from (f Unit)))

instance Transformation Flat (Day (Flat Arrow) (/\) (/\) (U_II_I (\/) e) (U_II_I (\/) e) i ii) (U_II_I (\/) e) Arrow Arrow
	where transformation (U_I_II from) = \case
		U_UU_UUU_UUUU_T_TT_I_II_III (These (These (U_II_I (This i)) (U_II_I (This ii))) (U_I_II f))
			-> U_II_I (This (from (f (These i ii))))
		U_UU_UUU_UUUU_T_TT_I_II_III (These (These (U_II_I (That e)) _) (U_I_II f))
			-> U_II_I (That e)

instance Transformation Flat (Day (Flat Arrow) (/\) (\/) (U_II_I (\/) e) (U_II_I (\/) e) i ii) (U_II_I (\/) e) Arrow Arrow
	where transformation (U_I_II from) = \case
		U_UU_UUU_UUUU_T_TT_I_II_III (These (These (U_II_I (This i)) _) (U_I_II f))
			-> U_II_I (This (from (f (This i))))
		U_UU_UUU_UUUU_T_TT_I_II_III (These (These _ (U_II_I (This ii))) (U_I_II f))
			-> U_II_I (This (from (f (That ii))))
		U_UU_UUU_UUUU_T_TT_I_II_III (These (These _ (U_II_I (That ii))) (U_I_II f))
			-> U_II_I (That ii)

instance Transformation Flat (Flat Arrow Unit) (U_II_I (\/) e) Arrow Arrow
	where transformation (U_I_II from) (U_I_II f) = U_II_I (This (from (f Unit)))
