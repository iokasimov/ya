{-# OPTIONS_GHC -fno-warn-orphans #-}
{-# LANGUAGE UndecidableInstances #-}
module Ya.Algebra (module Exports) where

import Ya.Algebra.Abstract as Exports
import Ya.Algebra.Definition as Exports
import Ya.Algebra.Instances as Exports
import Ya.Algebra.Operators as Exports

instance
	( Covariant Endo Semi Functor Arrow f
	, Transformation Flat Functor Arrow Arrow (T_TT_I g g) g
	, Transformation Flat Functor Arrow Arrow (T_TT_I f g) (TT_T_I f g)
	) => Mapping Flat Flat Arrow Arrow
		(T_TT_I (f `T_TT_I` R_U_I_T_I (/\) f) g)
		(TT_T_I (f `T_TT_I` R_U_I_T_I (/\) f) g)
	where mapping = rewrap / \from -> rewrap / \(T_TT_I x) ->
		(wrapped (component @Flat @Arrow @Arrow @(f `T_TT_I` g) @(f `TT_T_I` g))
			/ x `yo` wrapped (map @Flat @Flat @Arrow @Arrow
				@(R_U_I_T_I (/\) f `T_TT_I` g)
				@(R_U_I_T_I (/\) f `TT_T_I` g) from)
			) `yo` wrap @Arrow @(T_TT_I _ _ _)

-- TODO: I need to reduce transformations here
instance
	( Covariant Endo Semi Functor Arrow f
	, Transformation Flat Functor Arrow Arrow (T_TT_I g g) g
	, Transformation Flat Functor Arrow Arrow (T_TT_I f g) (TT_T_I f g)
	) => Mapping Flat Flat Arrow Arrow (R_U_I_T_I (/\) f `T_TT_I` g) (R_U_I_T_I (/\) f `TT_T_I` g) 
	where mapping = rewrap / \from -> rewrap `i`
		\(R_U_I_T_I (Recursive (U_I_T_II (These x xs)))) ->
			component @Flat @Arrow @Arrow @(T_TT_I _ _)
			`compose` wrap @Arrow @(T_TT_I _ _ _)
			`compose` yoneda @Flat @Functor @Arrow x
			`ii` \s ->
				wrap @Arrow @(R_U_I_T_I _ _ _)
				`compose` wrap @Arrow @(Recursive _)
				`compose` U_I_T_II
				`compose` These (from s)
				`fo` (unwrap @Arrow
					`fo'fo` unwrap @Arrow
						`compose` component @Flat @Arrow @Arrow
							@(f `T_TT_I` g) @(f `TT_T_I` g)
						`compose` wrap @Arrow @(T_TT_I _ _ _)
						`iii` unwrap @Arrow @(TT_T_I _ _ _)
							`compose` map @Flat @Flat @Arrow @Arrow
								@(R_U_I_T_I (/\) f `T_TT_I` g)
								@(R_U_I_T_I (/\) f `TT_T_I` g) from
							`compose` wrap @Arrow @(T_TT_I _ _ _)
							`compose` wrap @Arrow @(R_U_I_T_I _ _ _) 
						`fo` xs
				)
 
instance Mapping Flat Flat (W_I_II_II (U_I_UU_III_U_II_I (->) (/\))) Arrow
	(U_I_II (W_I_II_II (U_I_UU_III_U_II_I (->) (/\))) origin)
	(U_I_II (W_I_II_II (U_I_UU_III_U_II_I (->) (/\))) origin)
	where mapping = rewrap / \into -> rewrap `iii` rewrap `ii` rewrap `i` \from origin ->
		let These source source_origin = from origin in
		let These target target_source = into `u'u` source in
		These / target / target_source `o` source_origin

instance Mapping Dual Flat (W_I_II_II (U_I_UU_III_U_II_I (->) (/\))) Arrow
	(U_II_I (W_I_II_II (U_I_UU_III_U_II_I (->) (/\))) origin)
	(U_II_I (W_I_II_II (U_I_UU_III_U_II_I (->) (/\))) origin)
	where mapping = rewrap / \from -> rewrap `iii` rewrap `ii` rewrap `i` \into origin ->
		let These source source_origin = from `u'u` origin in
		let These target target_source = into source in
		These `ii` target `iii` target_source `o` source_origin

instance Category (W_I_II_II (U_I_UU_III_U_II_I (->) (/\))) where
	identity = W_I_II_II `i` U_I_UU_III_U_II_I (\x -> These `i` x `ii` identity)

instance Mapping Flat Flat Arrow Arrow (T_TT_I (U_I_II (/\) e) (U_I_II (->) e)) I
	where mapping = rewrap / \from -> rewrap / \(U_I_II (These e (U_I_II f))) -> from `i` f e

instance Mapping Flat Flat Arrow Arrow I (T_TT_I (U_I_II (->) e) (U_I_II (/\) e))
	where mapping = rewrap / \from -> rewrap / \x -> U_I_II `i` \e -> U_I_II `i` These e (from x)

-- TODO: generalize this instance
instance Mapping Dual Flat (W_I_II_II (U_I_UU_III_U_II_I (->) (/\))) Arrow
	(U_II_I (W_I_I_II (U_I_UU_II_III (->) (/\))) e)
	(U_II_I (W_I_I_II (U_I_UU_II_III (->) (/\))) e)
	where mapping = rewrap / \(W_I_II_II (U_I_UU_III_U_II_I from)) -> 
		wrap @Arrow @(U_II_I _ _ _)
		`compose` wrap @Arrow @(W_I_I_II _ _ _)
		`compose` wrap @Arrow @(U_I_UU_II_III (->) _ _ _ _)
		`compose` (\state old -> let (These new f) = from old in f `fo_` state new)
		`compose` unwrap @Arrow @(U_I_UU_II_III (->) _ _ _ _)
		`compose` unwrap @Arrow @(W_I_I_II _ _ _) 
		`compose` unwrap @Arrow @(U_II_I _ _ _)

instance Mapping Flat Flat Arrow Arrow
	(T_TT_I
		(U_I_II (W_I_I_II (U_I_UU_II_III (->) (/\))) e)
		(U_I_II (W_I_I_II (U_I_UU_II_III (->) (/\))) e)
	)
	(U_I_II (W_I_I_II (U_I_UU_II_III (->) (/\))) e)
	where mapping = rewrap / \from -> rewrap `iii` rewrap `ii`  rewrap `i` \(U_I_UU_II_III state) old ->
		(\(These s (U_I_II f)) -> from `_fo` f `u'u` s) (state old)

instance Covariant Endo Semi Functor Arrow u
	=> Mapping Flat Flat Arrow Arrow u (T_TT_TTT_I (U_I_II (->) e) u (U_I_II (/\) e))
	where mapping = rewrap / \from x -> T_TT_TTT_I `compose` U_I_II `yi` \state ->
		x `yo` from `o` These state `o` U_I_II

instance Covariant Monoidal Functor Arrow (/\) (/\) u 
	=> Mapping Flat Flat Arrow Arrow
		(U_I_II (W_I_I_II (U_I_UU_II_III (->) (/\))) e)
		(T_TT_TTT_I (U_I_II (->) e) u (U_I_II (/\) e))
	where mapping = rewrap / \from (U_I_II (W_I_I_II (U_I_UU_II_III x))) -> 
		wrap @Arrow @(T_TT_TTT_I _ _ _ _)
		`compose` wrap @Arrow @(U_I_II _ _ _)
		`identity` (point
			`compose` semifunctor @Flat from
			`compose` wrap @Arrow @(U_I_II _ _ _)
			`compose` x)

-- TODO: try to use adjunctions here
instance
	( Covariant Endo Semi Functor Arrow g
	, Transformation Natural Functor Arrow Arrow (T_TT_I g g) g
	) => Mapping Flat Flat Arrow Arrow
	(T_TT_I
		(T_TT_TTT_I (U_I_II (->) old) g (U_I_II (/\) btw))
		(T_TT_TTT_I (U_I_II (->) btw) g (U_I_II (/\) new))
	)
	(T_TT_TTT_I (U_I_II (->) old) g (U_I_II (/\) new))
	where mapping = rewrap / \from (T_TT_I (T_TT_TTT_I (U_I_II x))) -> 
		wrap @Arrow @(T_TT_TTT_I _ _ _ _) `compose` wrap @Arrow @(U_I_II _ _ _)
		`yi` \old -> x old `yokl` \(U_I_II (These btw (T_TT_TTT_I (U_I_II f))))
			-> f btw `yo'o` from

-- TODO: try to use adjunctions here
instance
	( Covariant Monoidal Functor Arrow (/\) (/\) g
	, Transformation Natural Functor Arrow Arrow (T_TT_I g g) g
	) => Mapping Flat Flat Arrow Arrow
	(T_TT_I
		(T_TT_TTT_I (U_I_II (->) e) g (U_I_II (/\) e))
		(U_I_II (W_I_I_II (U_I_UU_II_III (->) (/\))) e)
	)
	(T_TT_TTT_I (U_I_II (->) e) g (U_I_II (/\) e))
	where mapping = rewrap / \from (T_TT_I (T_TT_TTT_I (U_I_II x))) -> 
		wrap @Arrow @(T_TT_TTT_I _ _ _ _) `compose` wrap @Arrow @(U_I_II _ _ _)
		`yi` \old -> x old `yokl` \(U_I_II (These btw (U_I_II (W_I_I_II (U_I_UU_II_III f)))))
			-> point @g / U_I_II (f btw) `yo`from

instance Mapping Flat Flat Arrow Arrow (U_I_II (/\) e `T_TT_I` g) (U_I_II (/\) e `TT_T_I` g) =>
	Mapping Flat Flat Arrow Arrow
		(U_I_II (W_I_I_II (U_I_UU_II_III (->) (/\))) e `T_TT_I` g)
		(T_TT_TTT_I (U_I_II (->) e) g (U_I_II (/\) e))
	where mapping = rewrap / \from (T_TT_I (U_I_II (W_I_I_II (U_I_UU_II_III x)))) -> 
		T_TT_TTT_I `compose` U_I_II / \old -> wrapped @Arrow
			`i` map @Flat @Flat @Arrow @Arrow @(U_I_II (/\) e `T_TT_I` g) @(U_I_II (/\) e `TT_T_I` g) from
			`ii` U_I_II (x old)

instance 
	( Component Natural Arrow Arrow (T_TT_I g g) g
	, Covariant Yoneda Functor Arrow Arrow g
	) => Mapping Flat Flat Arrow Arrow (Day Flat Arrow (/\) (/\)
		(T_TT_TTT_I (U_I_II (->) e) g (U_I_II (/\) e))
		(T_TT_TTT_I (U_I_II (->) e) g (U_I_II (/\) e))
		i ii)
		(T_TT_TTT_I (U_I_II (->) e) g (U_I_II (/\) e))
	where mapping = rewrap / \from -> rewrap / \case
		These (These (T_TT_TTT_I (U_I_II x)) (T_TT_TTT_I (U_I_II y))) (U_I_II f) ->
			U_I_II / \old ->
				x old `yokl` \(U_I_II (These btw i)) ->
					from `a` f `a` These i `fo'fo`y btw

instance
	Monoidal Flat Functor Arrow (/\) (/\) g =>
	Mapping Flat Flat Arrow Arrow (U_I_II Arrow Unit)
		(T_TT_TTT_I (U_I_II (->) e) g (U_I_II (/\) e))
	where mapping = rewrap / \from (U_I_II f) -> T_TT_TTT_I `compose` U_I_II
		/ \old -> point `compose` U_I_II `compose` These old `compose` from `ii`f Unit

instance
	( Covariant Semi Functor from Arrow f
	, forall e . Covariant Semi Functor into Arrow (U_I_II from e)
	) => Mapping Flat Flat from Arrow f (UU_V_U_I_II_T_II Flat into Arrow f r)
	where mapping = rewrap / \from x -> UU_V_U_I_II_T_II (\(U_I_II e) -> e `_fo` from `fo'fi` x)

instance
	( Contravariant Semi Functor from Arrow f
	, forall e . Contravariant Semi Functor into Arrow (U_II_I from e)
	) => Mapping Dual Flat from Arrow f (UU_V_U_I_II_T_II Dual into Arrow f r)
	where mapping = rewrap / \from x -> UU_V_U_I_II_T_II (\(U_II_I e) -> e `fa_` from `fa'fi` x)

instance
	( Co Limit Arrow Arrow U_I_I
	, Transformation Natural Functor from Arrow I (U_I_II (\/) e)
	, Cone Dual from Arrow (\/)
	, forall ee . Transformation Natural Functor from Arrow I (U_II_I (\/) ee)
	, forall ee . Wrapper Arrow (I ee)
	, forall ee . Wrapper Arrow (U_II_I (\/) ee e)
	, forall ee . Wrapper Arrow (U_I_II (\/) e ee)
	, forall ee . Wrapper Arrow (T_TT_I (U_I_II (\/) e) (U_I_II (\/) e) ee)
	) => Mapping Flat Flat from Arrow (U_I_II (\/) e `T_TT_I` U_I_II (\/) e) (U_I_II (\/) e)
	where mapping = rewrap / \from -> rewrap @Arrow
		(wrapped (this @Dual @from @Arrow identity)
			\/ (wrapped (this @Dual @from @Arrow identity) \/ wrapped (that @Dual @from @Arrow from))
				`compose` unwrap @Arrow @(U_I_II _ _ _)
		) `compose` unwrap @Arrow @(T_TT_I _ _ _)

instance Covariant Monoidal Functor Arrow (/\) (/\) f =>
	Mapping Flat Flat Arrow Arrow (U_I_II (\/) e `T_TT_I` f) (U_I_II (\/) e `TT_T_I` f)
	where mapping = rewrap / \from -> rewrap / \case
		U_I_II (This e) -> point (U_I_II `i` This e)
		U_I_II (That x) -> x `yo` from `o` That  `o` U_I_II

instance Mapping Flat Flat Arrow Arrow (Day Flat Arrow (/\) (/\) I I i ii) I
	where mapping = rewrap / \from -> rewrap / \case
		These (These (I i) (I ii)) (U_I_II f) -> from (f (These i ii))

instance Mapping Flat Flat Arrow Arrow (Flat Arrow Unit) I
	where mapping = rewrap / \from (U_I_II f) -> I (from (f Unit))

instance Mapping Flat Flat Arrow Arrow (Day Flat Arrow (/\) (/\) (U_I_II (\/) e) (U_I_II (\/) e) i ii) (U_I_II (\/) e)
	where mapping = rewrap / \from -> rewrap / \case
		These (These (U_I_II (That i)) (U_I_II (That ii))) (U_I_II f) -> That (from (f (These i ii)))
		These (These (U_I_II (This e)) _) (U_I_II _) -> This e
		These (These _ (U_I_II (This e))) (U_I_II _) -> This e

instance Mapping Flat Flat Arrow Arrow (Day Flat Arrow (/\) (\/) (U_I_II (\/) e) (U_I_II (\/) e) i ii) (U_I_II (\/) e)
	where mapping = rewrap / \from -> rewrap / \case
		These (These (U_I_II (That i)) _) (U_I_II f) -> That (from (f (This i)))
		These (These _ (U_I_II (That ii))) (U_I_II f) -> That (from (f (That ii)))
		These (These _ (U_I_II (This ii))) (U_I_II _) -> This ii

instance Mapping Flat Flat Arrow Arrow (Day Flat Arrow (/\) (/\) (U_II_I (\/) e) (U_II_I (\/) e) i ii) (U_II_I (\/) e)
	where mapping = rewrap / \from -> rewrap `i` \case
		These (These (U_II_I (This i)) (U_II_I (This ii))) (U_I_II f) -> This (from (f (These i ii)))
		These (These (U_II_I (That e)) _) (U_I_II f) -> That e

instance Mapping Flat Flat Arrow Arrow (Day Flat Arrow (/\) (\/) (U_II_I (\/) e) (U_II_I (\/) e) i ii) (U_II_I (\/) e)
	where mapping = rewrap / \from -> rewrap `i` \case
		These (These (U_II_I (This i)) _) (U_I_II f) -> This (from (f (This i)))
		These (These _ (U_II_I (This ii))) (U_I_II f) -> This (from (f (That ii)))
		These (These _ (U_II_I (That ii))) (U_I_II f) -> That ii

instance Mapping Flat Flat Arrow Arrow (Flat Arrow Unit) (U_II_I (\/) e)
	where mapping = rewrap / \from (U_I_II f) -> U_II_I (This (from (f Unit)))

instance Mapping Flat Flat Arrow Arrow (Flat Arrow Unit) (U_I_II (\/) e)
	where mapping = rewrap / \from (U_I_II f) -> U_I_II (That (from (f Unit)))

instance Mapping Flat Flat Arrow Arrow (Flat Arrow Void) (U_I_II (\/) Unit)
	where mapping = rewrap / \from _ -> U_I_II (This Unit)

instance Mapping Flat Flat Arrow Arrow (Flat Arrow Void) (U_II_I (\/) Unit)
	where mapping = rewrap / \from _ -> U_II_I (That Unit)

-- TODO: generalize with limits
instance Covariant Monoidal Functor Arrow (/\) (/\) g =>
	Mapping Flat Flat Arrow Arrow (U_I_II (/\) e `T_TT_I` g) (U_I_II (/\) e `TT_T_I` g)
	where mapping = rewrap / \from -> rewrap / \case
		U_I_II (These e x) -> x `yo` from `o` These e `o` U_I_II

instance Covariant Endo Semi Functor Arrow g =>
	Mapping Flat Flat Arrow Arrow (g `T_TT_I` U_I_II (->) e) (g `TT_T_I` U_I_II (->) e)
	where mapping = rewrap / \from -> rewrap / \x ->
		U_I_II / \e -> x `yo`(from `compose` (`i` e) `compose` unwrap)
