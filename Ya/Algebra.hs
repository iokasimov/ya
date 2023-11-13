{-# OPTIONS_GHC -fno-warn-orphans #-}
{-# LANGUAGE UndecidableInstances #-}
module Ya.Algebra (module Exports) where

import Ya.Algebra.Abstract as Exports
import Ya.Algebra.Definition as Exports
import Ya.Algebra.Instances as Exports
import Ya.Algebra.Operators as Exports

instance
	( Covariant Endo Semi Functor Arrow f
	, Transformation Straight Functor Arrow Arrow (T_TT_I g g) g
	, Transformation Straight Functor Arrow Arrow (T_TT_I f g) (TT_T_I f g)
	) => Mapping Straight Straight Arrow Arrow
		(T_TT_I (f `T_TT_I` R_U_I_T_I (/\) f) g)
		(TT_T_I (f `T_TT_I` R_U_I_T_I (/\) f) g)
	where mapping = rw / \from -> rw / \(T_TT_I x) ->
		(wrapped (component @Straight @Arrow @Arrow @(f `T_TT_I` g) @(f `TT_T_I` g))
			/ x `yo` wrapped (map @Straight @Straight @Arrow @Arrow
				@(R_U_I_T_I (/\) f `T_TT_I` g)
				@(R_U_I_T_I (/\) f `TT_T_I` g) from)
			) `yo` wrap @Arrow @(T_TT_I _ _ _)

-- TODO: I need to reduce transformations here
instance
	( Covariant Endo Semi Functor Arrow f
	, Transformation Straight Functor Arrow Arrow (T_TT_I g g) g
	, Transformation Straight Functor Arrow Arrow (T_TT_I f g) (TT_T_I f g)
	) => Mapping Straight Straight Arrow Arrow (R_U_I_T_I (/\) f `T_TT_I` g) (R_U_I_T_I (/\) f `TT_T_I` g) 
	where mapping = rw / \from -> rw `i`
		\(R_U_I_T_I (Recursive (U_I_T_II (These x xs)))) ->
			component @Straight @Arrow @Arrow @(T_TT_I _ _)
			`compose` wrap @Arrow @(T_TT_I _ _ _)
			`compose` yoneda @Straight @Functor @Arrow x
			`i'i` \s ->
				wrap @Arrow @(R_U_I_T_I _ _ _)
				`compose` wrap @Arrow @(Recursive _)
				`compose` U_I_T_II
				`compose` These (from s)
				`fo` (uw @Arrow
					`fo'fo` uw @Arrow
						`compose` component @Straight @Arrow @Arrow
							@(f `T_TT_I` g) @(f `TT_T_I` g)
						`compose` wrap @Arrow @(T_TT_I _ _ _)
						`i'i'i` uw @Arrow @(TT_T_I _ _ _)
							`compose` map @Straight @Straight @Arrow @Arrow
								@(R_U_I_T_I (/\) f `T_TT_I` g)
								@(R_U_I_T_I (/\) f `TT_T_I` g) from
							`compose` wrap @Arrow @(T_TT_I _ _ _)
							`compose` wrap @Arrow @(R_U_I_T_I _ _ _) 
						`fo` xs
				)

instance Mapping Straight Straight Arrow Arrow (T_TT_I (U_I_II (/\) e) (U_I_II (->) e)) I
	where mapping = rw / \from -> rw / \(U_I_II (These e (U_I_II f))) -> from `i` f e

instance Mapping Straight Straight Arrow Arrow I (T_TT_I (U_I_II (->) e) (U_I_II (/\) e))
	where mapping = rw / \from -> rw / \x -> U_I_II `i` \e -> U_I_II `i` These e (from x)

-- TODO: generalize this instance
instance Mapping Opposite Straight (W_I_II_II (U_I_UU_III_U_II_I (->) (/\))) Arrow
	(U_II_I (W_I_I_II (U_I_UU_II_III (->) (/\))) e)
	(U_II_I (W_I_I_II (U_I_UU_II_III (->) (/\))) e)
	where mapping = rw / \(W_I_II_II (U_I_UU_III_U_II_I from)) -> 
		wrap @Arrow @(U_II_I _ _ _)
		`compose` wrap @Arrow @(W_I_I_II _ _ _)
		`compose` wrap @Arrow @(U_I_UU_II_III (->) _ _ _ _)
		`compose` (\state old -> let (These new f) = from old in f `fo_` state new)
		`compose` uw @Arrow @(U_I_UU_II_III (->) _ _ _ _)
		`compose` uw @Arrow @(W_I_I_II _ _ _) 
		`compose` uw @Arrow @(U_II_I _ _ _)

instance Mapping Straight Straight Arrow Arrow
	(T_TT_I
		(U_I_II (W_I_I_II (U_I_UU_II_III (->) (/\))) e)
		(U_I_II (W_I_I_II (U_I_UU_II_III (->) (/\))) e)
	)
	(U_I_II (W_I_I_II (U_I_UU_II_III (->) (/\))) e)
	where mapping = rw / \from -> rw `i'i'i` rw `i'i`  rw `i` \(U_I_UU_II_III state) old ->
		(\(These s (U_I_II f)) -> from `_fo` f `uw'uw` s) (state old)

instance Covariant Endo Semi Functor Arrow u
	=> Mapping Straight Straight Arrow Arrow u (T_TT_TTT_I (U_I_II (->) e) u (U_I_II (/\) e))
	where mapping = rw / \from x -> T_TT_TTT_I `compose` U_I_II `yi` \state ->
		x `yo` from `o` These state `o` U_I_II

instance Covariant Monoidal Functor Arrow (/\) (/\) u 
	=> Mapping Straight Straight Arrow Arrow
		(U_I_II (W_I_I_II (U_I_UU_II_III (->) (/\))) e)
		(T_TT_TTT_I (U_I_II (->) e) u (U_I_II (/\) e))
	where mapping = rw / \from (U_I_II (W_I_I_II (U_I_UU_II_III x))) -> 
		wrap @Arrow @(T_TT_TTT_I _ _ _ _)
		`compose` wrap @Arrow @(U_I_II _ _ _)
		`identity` (point
			`compose` semifunctor @Straight from
			`compose` wrap @Arrow @(U_I_II _ _ _)
			`compose` x)

-- TODO: try to use adjunctions here
instance
	( Covariant Endo Semi Functor Arrow g
	, Transformation Natural Functor Arrow Arrow (T_TT_I g g) g
	) => Mapping Straight Straight Arrow Arrow
	(T_TT_I
		(T_TT_TTT_I (U_I_II (->) old) g (U_I_II (/\) btw))
		(T_TT_TTT_I (U_I_II (->) btw) g (U_I_II (/\) new))
	)
	(T_TT_TTT_I (U_I_II (->) old) g (U_I_II (/\) new))
	where mapping = rw / \from (T_TT_I (T_TT_TTT_I (U_I_II x))) -> 
		wrap @Arrow @(T_TT_TTT_I _ _ _ _) `compose` wrap @Arrow @(U_I_II _ _ _)
		`yi` \old -> x old `yokl` \(U_I_II (These btw (T_TT_TTT_I (U_I_II f))))
			-> f btw `yo'o` from

-- TODO: try to use adjunctions here
instance
	( Covariant Monoidal Functor Arrow (/\) (/\) g
	, Transformation Natural Functor Arrow Arrow (T_TT_I g g) g
	) => Mapping Straight Straight Arrow Arrow
	(T_TT_I
		(T_TT_TTT_I (U_I_II (->) e) g (U_I_II (/\) e))
		(U_I_II (W_I_I_II (U_I_UU_II_III (->) (/\))) e)
	)
	(T_TT_TTT_I (U_I_II (->) e) g (U_I_II (/\) e))
	where mapping = rw / \from (T_TT_I (T_TT_TTT_I (U_I_II x))) -> 
		wrap @Arrow @(T_TT_TTT_I _ _ _ _) `compose` wrap @Arrow @(U_I_II _ _ _)
		`yi` \old -> x old `yokl` \(U_I_II (These btw (U_I_II (W_I_I_II (U_I_UU_II_III f)))))
			-> point @g / U_I_II (f btw) `yo`from

instance
	( Covariant Endo Semi Functor (->) t
	, Mapping Straight Straight (->) (->) (t `T_TT_I` t) t
	) => Mapping Straight Straight (->) (->)
		(T_TT_I (T_TT_TTT_I (Straight Arrow e) t (Straight (/\) e)) t)
		(T_TT_TTT_I (Straight Arrow e) t (Straight (/\) e))
	where mapping = rw / \from (T_TT_I (T_TT_TTT_I (U_I_II f))) -> T_TT_TTT_I `compose` U_I_II / \old ->
		component @Straight @(->) @(->) @(t `T_TT_I` t) @t
			(T_TT_I (f old `yo` (\(U_I_II (These x y)) -> y `yo` U_I_II `a` These x `a` from)))

instance Mapping Straight Straight Arrow Arrow (U_I_II (/\) e `T_TT_I` g) (U_I_II (/\) e `TT_T_I` g) =>
	Mapping Straight Straight Arrow Arrow
		(U_I_II (W_I_I_II (U_I_UU_II_III (->) (/\))) e `T_TT_I` g)
		(T_TT_TTT_I (U_I_II (->) e) g (U_I_II (/\) e))
	where mapping = rw / \from (T_TT_I (U_I_II (W_I_I_II (U_I_UU_II_III x)))) -> 
		T_TT_TTT_I `compose` U_I_II / \old -> wrapped @Arrow
			`i` map @Straight @Straight @Arrow @Arrow @(U_I_II (/\) e `T_TT_I` g) @(U_I_II (/\) e `TT_T_I` g) from
			`i'i` U_I_II (x old)

instance 
	( Component Natural Arrow Arrow (T_TT_I g g) g
	, Covariant Yoneda Functor Arrow Arrow g
	) => Mapping Straight Straight Arrow Arrow (Day Straight Arrow (/\) (/\)
		(T_TT_TTT_I (U_I_II (->) e) g (U_I_II (/\) e))
		(T_TT_TTT_I (U_I_II (->) e) g (U_I_II (/\) e))
		i ii)
		(T_TT_TTT_I (U_I_II (->) e) g (U_I_II (/\) e))
	where mapping = rw / \from -> rw / \case
		These (These (T_TT_TTT_I (U_I_II x)) (T_TT_TTT_I (U_I_II y))) (U_I_II f) ->
			U_I_II / \old ->
				x old `yokl` \(U_I_II (These btw i)) ->
					from `a` f `a` These i `fo'fo`y btw

instance
	Monoidal Straight Functor Arrow (/\) (/\) g =>
	Mapping Straight Straight Arrow Arrow (U_I_II Arrow Unit)
		(T_TT_TTT_I (U_I_II (->) e) g (U_I_II (/\) e))
	where mapping = rw / \from (U_I_II f) -> T_TT_TTT_I `compose` U_I_II
		/ \old -> point `compose` U_I_II `compose` These old `compose` from `i'i` f Unit

instance
	( Covariant Semi Functor from Arrow f
	, forall e . Covariant Semi Functor into Arrow (U_I_II from e)
	) => Mapping Straight Straight from Arrow f (UU_V_U_I_II_T_II Straight into Arrow f r)
	where mapping = rw / \from x -> UU_V_U_I_II_T_II (\(U_I_II e) -> e `_fo` from `fo'fi` x)

instance
	( Covariant Endo Semi Functor Arrow f
	, forall e . Covariant Endo Semi Functor Arrow (U_I_II Arrow e)
	) => Mapping Constant Straight Arrow Arrow f (UU_V_U_I_II_T_II Constant Arrow Arrow f r)
	where mapping = rw / \_ x -> UU_V_U_I_II_T_II (\(U_1_I e) -> (\_ -> e Unit) `fo'fi` x)

instance
	( Contravariant Semi Functor from Arrow f
	, forall e . Contravariant Semi Functor into Arrow (U_II_I from e)
	) => Mapping Opposite Straight from Arrow f (UU_V_U_I_II_T_II Opposite into Arrow f r)
	where mapping = rw / \from x -> UU_V_U_I_II_T_II (\(U_II_I e) -> e `fa_` from `fa'fi` x)

instance Mapping Straight Straight Arrow Arrow (U_I_II (\/) e `T_TT_I` U_I_II (\/) e) (U_I_II (\/) e)
	where mapping = rw / \from -> \case
		T_TT_I (U_I_II (That (U_I_II (That x)))) -> U_I_II (That / from x)
		T_TT_I (U_I_II (That (U_I_II (This e)))) -> U_I_II (This e)
		T_TT_I (U_I_II (This e)) -> U_I_II (This e)

instance Covariant Monoidal Functor Arrow (/\) (/\) f =>
	Mapping Straight Straight Arrow Arrow (U_I_II (\/) e `T_TT_I` f) (U_I_II (\/) e `TT_T_I` f)
	where mapping = rw / \from -> rw / \case
		U_I_II (This e) -> point (U_I_II `i` This e)
		U_I_II (That x) -> x `yo` from `o` That  `o` U_I_II

instance Mapping Straight Straight Arrow Arrow (Day Straight Arrow (/\) (/\) I I i ii) I
	where mapping = rw / \from -> rw / \case
		These (These (I i) (I ii)) (U_I_II f) -> from (f (These i ii))

instance Mapping Straight Straight Arrow Arrow (Straight Arrow Unit) I
	where mapping = rw / \from (U_I_II f) -> I (from (f Unit))

instance Mapping Straight Straight Arrow Arrow (Day Straight Arrow (/\) (/\) (U_I_II (\/) e) (U_I_II (\/) e) i ii) (U_I_II (\/) e)
	where mapping = rw / \from -> rw / \case
		These (These (U_I_II (That i)) (U_I_II (That ii))) (U_I_II f) -> That (from (f (These i ii)))
		These (These (U_I_II (This e)) _) (U_I_II _) -> This e
		These (These _ (U_I_II (This e))) (U_I_II _) -> This e

instance Mapping Straight Straight Arrow Arrow (Day Straight Arrow (/\) (\/) (U_I_II (\/) e) (U_I_II (\/) e) i ii) (U_I_II (\/) e)
	where mapping = rw / \from -> rw / \case
		These (These (U_I_II (That i)) _) (U_I_II f) -> That (from (f (This i)))
		These (These _ (U_I_II (That ii))) (U_I_II f) -> That (from (f (That ii)))
		These (These _ (U_I_II (This ii))) (U_I_II _) -> This ii

instance Mapping Straight Straight Arrow Arrow (Day Straight Arrow (/\) (/\) (U_II_I (\/) e) (U_II_I (\/) e) i ii) (U_II_I (\/) e)
	where mapping = rw / \from -> rw `i` \case
		These (These (U_II_I (This i)) (U_II_I (This ii))) (U_I_II f) -> This (from (f (These i ii)))
		These (These (U_II_I (That e)) _) (U_I_II f) -> That e

instance Mapping Straight Straight Arrow Arrow (Day Straight Arrow (/\) (\/) (U_II_I (\/) e) (U_II_I (\/) e) i ii) (U_II_I (\/) e)
	where mapping = rw / \from -> rw `i` \case
		These (These (U_II_I (This i)) _) (U_I_II f) -> This (from (f (This i)))
		These (These _ (U_II_I (This ii))) (U_I_II f) -> This (from (f (That ii)))
		These (These _ (U_II_I (That ii))) (U_I_II f) -> That ii

instance Mapping Straight Straight Arrow Arrow (Straight Arrow Unit) (U_II_I (\/) e)
	where mapping = rw / \from (U_I_II f) -> U_II_I (This (from (f Unit)))

instance Mapping Straight Straight Arrow Arrow (Straight Arrow Unit) (U_I_II (\/) e)
	where mapping = rw / \from (U_I_II f) -> U_I_II (That (from (f Unit)))

instance Mapping Straight Straight Arrow Arrow (Straight Arrow Void) (U_I_II (\/) Unit)
	where mapping = rw / \from _ -> U_I_II (This Unit)

instance Mapping Straight Straight Arrow Arrow (Straight Arrow Void) (U_II_I (\/) Unit)
	where mapping = rw / \from _ -> U_II_I (That Unit)

-- TODO: generalize with limits
instance Covariant Monoidal Functor Arrow (/\) (/\) g =>
	Mapping Straight Straight Arrow Arrow (U_I_II (/\) e `T_TT_I` g) (U_I_II (/\) e `TT_T_I` g)
	where mapping = rw / \from -> rw / \case
		U_I_II (These e x) -> x `yo` from `o` These e `o` U_I_II

instance Covariant Endo Semi Functor Arrow g =>
	Mapping Straight Straight Arrow Arrow (g `T_TT_I` U_I_II (->) e) (g `TT_T_I` U_I_II (->) e)
	where mapping = rw / \from -> rw / \x ->
		U_I_II / \e -> x `yo`(from `compose` (`i` e) `compose` uw)
