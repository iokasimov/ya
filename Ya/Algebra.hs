{-# OPTIONS_GHC -fno-warn-orphans #-}
{-# LANGUAGE UndecidableInstances #-}
module Ya.Algebra (module Exports) where

import Ya.Algebra.Abstract as Exports
import Ya.Algebra.Definition as Exports
import Ya.Algebra.Instances as Exports
import Ya.Algebra.Operators as Exports

-- TODO: Mapping Flat from into
-- 	(T_TT_I (T_TT_I f Construction f) g)
-- 	(T_TT_I g (T_TT_I f Construction f))

-- TODO: Mapping Flat from into
--		(T_TT_I (U_T_I_T_I And f) g)
--		(T_TT_I g (U_T_I_T_I And f))

instance Mapping Flat (W_I_II_II (U_I_UU_III_U_II_I (->) (/\))) Arrow
	(U_I_II (W_I_II_II (U_I_UU_III_U_II_I (->) (/\))) origin)
	(U_I_II (W_I_II_II (U_I_UU_III_U_II_I (->) (/\))) origin)
	where mapping (U_I_II into) = w'u `iii` w'u `ii` w'u `i` \from origin ->
		let These source source_origin = from origin in
		let These target target_source = into `u'u` source in
		These `iii` target `iii` target_source `o` source_origin

instance Mapping Dual (W_I_II_II (U_I_UU_III_U_II_I (->) (/\))) Arrow
	(U_II_I (W_I_II_II (U_I_UU_III_U_II_I (->) (/\))) origin)
	(U_II_I (W_I_II_II (U_I_UU_III_U_II_I (->) (/\))) origin)
	where mapping (U_II_I from) = w'u `iii` w'u `ii` w'u `i` \into origin ->
		let These source source_origin = from `u'u` origin in
		let These target target_source = into source in
		These `iii` target `iii` target_source `o` source_origin

instance Category (W_I_II_II (U_I_UU_III_U_II_I (->) (/\))) where
	identity = W_I_II_II `i` U_I_UU_III_U_II_I
		(\x -> These `i` x `i` identity)

instance Mapping Flat Arrow Arrow (T_TT_I (U_I_II (/\) e) (U_I_II (->) e)) I
	where mapping (U_I_II from) = w'u `i` \(U_I_II (These e (U_I_II f))) -> from `i` f e

instance Mapping Flat Arrow Arrow I (T_TT_I (U_I_II (->) e) (U_I_II (/\) e))
	where mapping (U_I_II from) = w'u `i` \x -> U_I_II `i` \e -> U_I_II `i` These e (from x)

-- TODO: gereralize this instance
instance Mapping Flat Arrow Arrow
	(U_I_II (W_I_I_II (U_I_UU_II_III (->) (/\))) e)
	(U_I_II (W_I_I_II (U_I_UU_II_III (->) (/\))) e)
	where mapping (U_I_II from) = w'u `iii` w'u `ii`  w'u `i`
		((_fo @Arrow `compose` _fo @Arrow) from)

instance Mapping Dual (W_I_II_II (U_I_UU_III_U_II_I (->) (/\))) Arrow
	(U_II_I (W_I_I_II (U_I_UU_II_III (->) (/\))) e)
	(U_II_I (W_I_I_II (U_I_UU_II_III (->) (/\))) e)
	where mapping (U_II_I from) = w'u `iii` w'u `ii`  w'u `i` \state old ->
		let (These new f) = from `u'u` old in f `fo_` state new

instance Mapping Flat Arrow Arrow
	(T_TT_I
		(U_I_II (W_I_I_II (U_I_UU_II_III (->) (/\))) e)
		(U_I_II (W_I_I_II (U_I_UU_II_III (->) (/\))) e)
	)
	(U_I_II (W_I_I_II (U_I_UU_II_III (->) (/\))) e)
	where mapping (U_I_II from) = w'u `iii` w'u `ii`  w'u `i` \(U_I_UU_II_III state) old ->
		(\(These s (U_I_II f)) -> from `_fo` f `u'u` s) (state old)

instance
	( Covariant Semi Functor from Arrow f
	, forall e . Covariant Semi Functor into Arrow (U_I_II from e)
	) => Mapping Flat from Arrow f (UU_V_U_I_II_T_II Flat into Arrow f r)
	where mapping (U_I_II from) x = UU_V_U_I_II_T_II (\(U_I_II e) -> e `_fo` from `fo'fi` x)

instance
	( Contravariant Semi Functor from Arrow f
	, forall e . Contravariant Semi Functor into Arrow (U_II_I from e)
	) => Mapping Dual from Arrow f (UU_V_U_I_II_T_II Dual into Arrow f r)
	where mapping (U_II_I from) x = UU_V_U_I_II_T_II (\(U_II_I e) -> e `fa_` from `fa'fi` x)

instance Mapping Flat Arrow Arrow (Day Flat Arrow (/\) (/\) I I i ii) I
	where mapping (U_I_II from) = w'u `i` \case
		These (These (I i) (I ii)) (U_I_II f) -> from (f (These i ii))

instance Mapping Flat Arrow Arrow (Flat Arrow Unit) I
	where mapping (U_I_II from) (U_I_II f) = I (from (f Unit))

instance Mapping Flat Arrow Arrow (Day Flat Arrow (/\) (/\) (U_I_II (\/) e) (U_I_II (\/) e) i ii) (U_I_II (\/) e)
	where mapping (U_I_II from) = w'u `i` \case
		These (These (U_I_II (That i)) (U_I_II (That ii))) (U_I_II f) -> That (from (f (These i ii)))
		These (These (U_I_II (This e)) _) (U_I_II _) -> This e
		These (These _ (U_I_II (This e))) (U_I_II _) -> This e

instance Mapping Flat Arrow Arrow (Day Flat Arrow (/\) (\/) (U_I_II (\/) e) (U_I_II (\/) e) i ii) (U_I_II (\/) e)
	where mapping (U_I_II from) = w'u `i` \case
		These (These (U_I_II (That i)) _) (U_I_II f) -> That (from (f (This i)))
		These (These _ (U_I_II (That ii))) (U_I_II f) -> That (from (f (That ii)))
		These (These _ (U_I_II (This ii))) (U_I_II f) -> This ii

instance Mapping Flat Arrow Arrow (Flat Arrow Unit) (U_I_II (\/) e)
	where mapping (U_I_II from) (U_I_II f) = U_I_II (That (from (f Unit)))

instance Mapping Flat Arrow Arrow (Day Flat Arrow (/\) (/\) (U_II_I (\/) e) (U_II_I (\/) e) i ii) (U_II_I (\/) e)
	where mapping (U_I_II from) = w'u `i` \case
		These (These (U_II_I (This i)) (U_II_I (This ii))) (U_I_II f) -> This (from (f (These i ii)))
		These (These (U_II_I (That e)) _) (U_I_II f) -> That e

instance Mapping Flat Arrow Arrow (Day Flat Arrow (/\) (\/) (U_II_I (\/) e) (U_II_I (\/) e) i ii) (U_II_I (\/) e)
	where mapping (U_I_II from) = w'u `i` \case
		These (These (U_II_I (This i)) _) (U_I_II f) -> This (from (f (This i)))
		These (These _ (U_II_I (This ii))) (U_I_II f) -> This (from (f (That ii)))
		These (These _ (U_II_I (That ii))) (U_I_II f) -> That ii

instance Mapping Flat Arrow Arrow (Flat Arrow Unit) (U_II_I (\/) e)
	where mapping (U_I_II from) (U_I_II f) = U_II_I (This (from (f Unit)))

instance Mapping Flat Arrow Arrow (U_I_II (/\) e) (U_I_II (/\) e)
	where mapping (U_I_II from) = w'u `i` \(These e x) -> These e (from x)

instance Mapping Flat Arrow Arrow (U_II_I (/\) e) (U_II_I (/\) e)
	where mapping (U_I_II from) = w'u `i` \(These x e) -> These (from x) e

instance Mapping Flat Arrow Arrow (U_I_II (\/) e) (U_I_II (\/) e)
	where mapping (U_I_II from) = w'u `i` \case
		That x -> That (from x)
		This e -> This e

instance Mapping Flat Arrow Arrow (U_II_I (\/) e) (U_II_I (\/) e)
	where mapping (U_I_II from) = w'u `i` \case
		This x -> This (from x)
		That e -> That e

instance Mapping Flat Arrow Arrow (U_I_II (/\) e) I
	where mapping (U_I_II from) (U_I_II (These e x)) = I (from x)

instance Mapping Flat Arrow Arrow (U_II_I (/\) e) I
	where mapping (U_I_II from) (U_II_I (These x e)) = I (from x)

instance Mapping Flat Arrow Arrow I (U_I_II (\/) e)
	where mapping (U_I_II from) (I x) = U_I_II (That (from x))

instance Mapping Flat Arrow Arrow I (U_II_I (\/) e)
	where mapping (U_I_II from) (I x) = U_II_I (This (from x))
