{-# OPTIONS_GHC -fno-warn-orphans #-}
{-# LANGUAGE UndecidableInstances #-}
module Ya.Algebra (module Exports) where

import Ya.Algebra.Abstract as Exports
import Ya.Algebra.Definition as Exports
import Ya.Algebra.Instances as Exports ()
import Ya.Algebra.Operators as Exports

-- instance
-- 	( Covariant Endo Semi Functor (->) t
-- 	, Monoidal Straight Functor (->) (/\) (/\) tt
-- 	) => Mapping Straight Straight (->) (->) t (t `T'TT'I` tt)
-- 	where mapping = rw / \from -> wrap @(->) @(T'TT'I _ _ _)
-- 		`compose` semifunctor @Straight @(->) @(->) (yu enter `compose` from)

-- instance
-- 	( Covariant Endo Semi Functor (->) tt
-- 	, Monoidal Straight Functor (->) (/\) (/\) t
-- 	) => Mapping Straight Straight (->) (->) tt (t `T'TT'I` tt)
-- 	where mapping = rw / \from ->
-- 		wrap @(->) @(T'TT'I _ _ _) `compose` yu enter
-- 			`compose` semifunctor @Straight @(->) @(->) from

-- instance {-# OVERLAPS #-}
-- 	Mapping Straight Straight (->) (->) ttt tt =>
-- 	Mapping Straight Straight (->) (->) ttt (t `T'TT'I` tt)

instance
	( Covariant Endo Semi Functor (->) f
	, Transformation Straight Functor (->) (->) (g `T'TT'I` g) g
	, Transformation Straight Functor (->) (->) (f `T'TT'I` g) (TT_T_I f g)
	) => Mapping Straight Straight (->) (->)
		(T'TT'I (f `T'TT'I` R_U_I_T_I (/\) f) g)
		(TT_T_I (f `T'TT'I` R_U_I_T_I (/\) f) g)
	where mapping = rw / \from -> rw / \(T'TT'I x) ->
		(wrapped (component @Straight @(->) @(->) @(f `T'TT'I` g) @(f `TT_T_I` g))
			/ x `yo` wrapped (map @Straight @Straight @(->) @(->)
				@(R_U_I_T_I (/\) f `T'TT'I` g)
				@(R_U_I_T_I (/\) f `TT_T_I` g) from)
			) `yo` wrap @(->) @(T'TT'I _ _ _)

-- TODO: I need to reduce transformations here
instance
	( Covariant Endo Semi Functor (->) f
	, Transformation Straight Functor (->) (->) (T'TT'I g g) g
	, Transformation Straight Functor (->) (->) (T'TT'I f g) (TT_T_I f g)
	) => Mapping Straight Straight (->) (->) (R_U_I_T_I (/\) f `T'TT'I` g) (R_U_I_T_I (/\) f `TT_T_I` g) 
	where mapping = rw / \from -> rw `i`
		\(R_U_I_T_I (Recursive (U_I_T_II (These x xs)))) ->
			component @Straight @(->) @(->) @(T'TT'I _ _)
			`compose` wrap @(->) @(T'TT'I _ _ _)
			`compose` yoneda @Straight @Functor @(->) x
			`i'i` \s ->
				wrap @(->) @(R_U_I_T_I _ _ _)
				`compose` wrap @(->) @(Recursive _)
				`compose` U_I_T_II
				`compose` These (from s)
				`fo` (uw @(->)
					`fo'fo` uw @(->)
						`compose` component @Straight @(->) @(->)
							@(f `T'TT'I` g) @(f `TT_T_I` g)
						`compose` wrap @(->) @(T'TT'I _ _ _)
						`i'i'i` uw @(->) @(TT_T_I _ _ _)
							`compose` map @Straight @Straight @(->) @(->)
								@(R_U_I_T_I (/\) f `T'TT'I` g)
								@(R_U_I_T_I (/\) f `TT_T_I` g) from
							`compose` wrap @(->) @(T'TT'I _ _ _)
							`compose` wrap @(->) @(R_U_I_T_I _ _ _) 
						`fo` xs
				)

instance Mapping Straight Straight (->) (->) (T'TT'I (U_I_II (/\) e) (U_I_II (->) e)) I
	where mapping = rw / \from -> rw / \(U_I_II (These e (U_I_II f))) -> from `i` f e

instance Mapping Straight Straight (->) (->) I (T'TT'I (U_I_II (->) e) (U_I_II (/\) e))
	where mapping = rw / \from -> rw / \x -> U_I_II `i` \e -> U_I_II `i` These e (from x)

-- TODO: generalize this instance
instance Mapping Opposite Straight (W_I_II_II (U_I_UU_III_U_II_I (->) (/\))) (->)
	(U_II_I (W_I_I_II (U_I_UU_II_III (->) (/\))) e)
	(U_II_I (W_I_I_II (U_I_UU_II_III (->) (/\))) e)
	where mapping = rw / \(W_I_II_II (U_I_UU_III_U_II_I from)) -> 
		wrap @(->) @(U_II_I _ _ _)
		`compose` wrap @(->) @(W_I_I_II _ _ _)
		`compose` wrap @(->) @(U_I_UU_II_III (->) _ _ _ _)
		`compose` (\state old -> let (These new f) = from old in f `fo_` state new)
		`compose` uw @(->) @(U_I_UU_II_III (->) _ _ _ _)
		`compose` uw @(->) @(W_I_I_II _ _ _) 
		`compose` uw @(->) @(U_II_I _ _ _)

instance Mapping Straight Straight (->) (->)
	(T'TT'I
		(U_I_II (W_I_I_II (U_I_UU_II_III (->) (/\))) e)
		(U_I_II (W_I_I_II (U_I_UU_II_III (->) (/\))) e)
	)
	(U_I_II (W_I_I_II (U_I_UU_II_III (->) (/\))) e)
	where mapping = rw / \from -> rw `i'i'i` rw `i'i`  rw `i` \(U_I_UU_II_III state) old ->
		(\(These s (U_I_II f)) -> from `_fo` f `uw'uw` s) (state old)

instance Covariant Endo Semi Functor (->) u
	=> Mapping Straight Straight (->) (->) u (T_TT_TTT_I (U_I_II (->) e) u (U_I_II (/\) e))
	where mapping = rw / \from x -> T_TT_TTT_I `compose` U_I_II `yi` \state ->
		x `yo` from `o` These state `o` U_I_II

instance Covariant Monoidal Functor (->) (/\) (/\) u 
	=> Mapping Straight Straight (->) (->)
		(U_I_II (W_I_I_II (U_I_UU_II_III (->) (/\))) e)
		(T_TT_TTT_I (U_I_II (->) e) u (U_I_II (/\) e))
	where mapping = rw / \from (U_I_II (W_I_I_II (U_I_UU_II_III x))) -> 
		wrap @(->) @(T_TT_TTT_I _ _ _ _)
		`compose` wrap @(->) @(U_I_II _ _ _)
		`identity` (yu enter
			`compose` semifunctor @Straight from
			`compose` wrap @(->) @(U_I_II _ _ _)
			`compose` x)

-- TODO: try to use adjunctions here
instance
	( Covariant Endo Semi Functor (->) g
	, Transformation Natural Functor (->) (->) (T'TT'I g g) g
	) => Mapping Straight Straight (->) (->)
	(T'TT'I
		(T_TT_TTT_I (U_I_II (->) old) g (U_I_II (/\) btw))
		(T_TT_TTT_I (U_I_II (->) btw) g (U_I_II (/\) new))
	)
	(T_TT_TTT_I (U_I_II (->) old) g (U_I_II (/\) new))
	where mapping = rw / \from (T'TT'I (T_TT_TTT_I (U_I_II x))) -> 
		wrap @(->) @(T_TT_TTT_I _ _ _ _) `compose` wrap @(->) @(U_I_II _ _ _)
		`yi` \old -> x old `yokl` \(U_I_II (These btw (T_TT_TTT_I (U_I_II f))))
			-> f btw `yo'o` from

-- TODO: try to use adjunctions here
instance
	( Covariant Monoidal Functor (->) (/\) (/\) g
	, Transformation Natural Functor (->) (->) (T'TT'I g g) g
	) => Mapping Straight Straight (->) (->)
	(T'TT'I
		(T_TT_TTT_I (U_I_II (->) e) g (U_I_II (/\) e))
		(U_I_II (W_I_I_II (U_I_UU_II_III (->) (/\))) e)
	)
	(T_TT_TTT_I (U_I_II (->) e) g (U_I_II (/\) e))
	where mapping = rw / \from (T'TT'I (T_TT_TTT_I (U_I_II x))) -> 
		wrap @(->) @(T_TT_TTT_I _ _ _ _) `compose` wrap @(->) @(U_I_II _ _ _)
		`yi` \old -> x old `yokl` \(U_I_II (These btw (U_I_II (W_I_I_II (U_I_UU_II_III f)))))
			-> yu (enter @g) / U_I_II (f btw) `yo` from

instance
	( Covariant Endo Semi Functor (->) t
	, Mapping Straight Straight (->) (->) (t `T'TT'I` t) t
	) => Mapping Straight Straight (->) (->)
		(T'TT'I (T_TT_TTT_I (Straight (->) e) t (Straight (/\) e)) t)
		(T_TT_TTT_I (Straight (->) e) t (Straight (/\) e))
	where mapping = rw / \from (T'TT'I (T_TT_TTT_I (U_I_II f))) -> T_TT_TTT_I `compose` U_I_II / \old ->
		component @Straight @(->) @(->) @(t `T'TT'I` t) @t
			(T'TT'I (f old `yo` (\(U_I_II (These x y)) -> y `yo` U_I_II `a` These x `a` from)))

instance Mapping Straight Straight (->) (->) (U_I_II (/\) e `T'TT'I` g) (U_I_II (/\) e `TT_T_I` g) =>
	Mapping Straight Straight (->) (->)
		(U_I_II (W_I_I_II (U_I_UU_II_III (->) (/\))) e `T'TT'I` g)
		(T_TT_TTT_I (U_I_II (->) e) g (U_I_II (/\) e))
	where mapping = rw / \from (T'TT'I (U_I_II (W_I_I_II (U_I_UU_II_III x)))) -> 
		T_TT_TTT_I `compose` U_I_II / \old -> wrapped @(->)
			`i` map @Straight @Straight @(->) @(->) @(U_I_II (/\) e `T'TT'I` g) @(U_I_II (/\) e `TT_T_I` g) from
			`i'i` U_I_II (x old)

instance 
	( Component Natural (->) (->) (T'TT'I g g) g
	, Covariant Yoneda Functor (->) (->) g
	) => Mapping Straight Straight (->) (->) (Day Straight (->) (/\) (/\)
		(T_TT_TTT_I (U_I_II (->) e) g (U_I_II (/\) e))
		(T_TT_TTT_I (U_I_II (->) e) g (U_I_II (/\) e))
		ee eee)
		(T_TT_TTT_I (U_I_II (->) e) g (U_I_II (/\) e))
	where mapping = rw / \from -> rw / \case
		These (These (T_TT_TTT_I (U_I_II x)) (T_TT_TTT_I (U_I_II y))) (U_I_II f) ->
			U_I_II / \old ->
				x old `yokl` \(U_I_II (These btw e)) ->
					from `a` f `a` These e `fo'fo` y btw

instance
	Monoidal Straight Functor (->) (/\) (/\) g =>
	Mapping Straight Straight (->) (->) (U_I_II (->) Unit)
		(T_TT_TTT_I (U_I_II (->) e) g (U_I_II (/\) e))
	where mapping = rw / \from (U_I_II f) -> T_TT_TTT_I `compose` U_I_II
		/ \old -> yu enter `compose` U_I_II `compose` These old `compose` from `i'i` f Unit

instance
	( Covariant Semi Functor from (->) f
	, forall e . Covariant Semi Functor into (->) (U_I_II from e)
	) => Mapping Straight Straight from (->) f (UU_V_U_I_II_T_II Straight into (->) f r)
	where mapping = rw / \from x -> UU_V_U_I_II_T_II (\(U_I_II e) -> e `_fo` from `fo'fi` x)

instance
	( Covariant Endo Semi Functor (->) f
	, forall e . Covariant Endo Semi Functor (->) (U_I_II (->) e)
	) => Mapping Constant Straight (->) (->) f (UU_V_U_I_II_T_II Constant (->) (->) f r)
	where mapping = rw / \_ x -> UU_V_U_I_II_T_II (\(U_1_I e) -> (\_ -> e Unit) `fo'fi` x)

instance
	( Contravariant Semi Functor from (->) f
	, forall e . Contravariant Semi Functor into (->) (U_II_I from e)
	) => Mapping Opposite Straight from (->) f (UU_V_U_I_II_T_II Opposite into (->) f r)
	where mapping = rw / \from x -> UU_V_U_I_II_T_II (\(U_II_I e) -> e `fa_` from `fa'fi` x)

instance Mapping Straight Straight (->) (->) (U_I_II (\/) e `T'TT'I` U_I_II (\/) e) (U_I_II (\/) e)
	where mapping = rw / \from -> \case
		T'TT'I (U_I_II (That (U_I_II (That x)))) -> U_I_II (That / from x)
		T'TT'I (U_I_II (That (U_I_II (This e)))) -> U_I_II (This e)
		T'TT'I (U_I_II (This e)) -> U_I_II (This e)

instance Covariant Monoidal Functor (->) (/\) (/\) f =>
	Mapping Straight Straight (->) (->) (U_I_II (\/) e `T'TT'I` f) (U_I_II (\/) e `TT_T_I` f)
	where mapping = rw / \from -> rw / \case
		U_I_II (This e) -> yu enter (U_I_II `i` This e)
		U_I_II (That x) -> x `yo` from `o` That  `o` U_I_II

instance Mapping Straight Straight (->) (->) (Day Straight (->) (/\) (/\) I I e ee) I
	where mapping = rw / \from -> rw / \case
		These (These (I e) (I ee)) (U_I_II f) -> from (f (These e ee))

instance Mapping Straight Straight (->) (->) (Straight (->) Unit) I
	where mapping = rw / \from (U_I_II f) -> I (from (f Unit))

instance Mapping Straight Straight (->) (->) (Day Straight (->) (/\) (/\) (U_I_II (\/) e) (U_I_II (\/) e) ee eee) (U_I_II (\/) e)
	where mapping = rw / \from -> rw / \case
		These (These (U_I_II (That ee)) (U_I_II (That eee))) (U_I_II f) -> That (from (f (These ee eee)))
		These (These (U_I_II (This e)) _) (U_I_II _) -> This e
		These (These _ (U_I_II (This e))) (U_I_II _) -> This e

instance Mapping Straight Straight (->) (->) (Day Straight (->) (/\) (\/) (U_I_II (\/) e) (U_I_II (\/) e) ee eee) (U_I_II (\/) e)
	where mapping = rw / \from -> rw / \case
		These (These (U_I_II (That ee)) _) (U_I_II f) -> That (from (f (This ee)))
		These (These _ (U_I_II (That eee))) (U_I_II f) -> That (from (f (That eee)))
		These (These _ (U_I_II (This eee))) (U_I_II _) -> This eee

instance Mapping Straight Straight (->) (->) (Day Straight (->) (/\) (/\) (U_II_I (\/) e) (U_II_I (\/) e) ee eee) (U_II_I (\/) e)
	where mapping = rw / \from -> rw `i` \case
		These (These (U_II_I (This ee)) (U_II_I (This eee))) (U_I_II f) -> This (from (f (These ee eee)))
		These (These (U_II_I (That e)) _) _ -> That e

instance Mapping Straight Straight (->) (->) (Day Straight (->) (/\) (\/) (U_II_I (\/) e) (U_II_I (\/) e) ee eee) (U_II_I (\/) e)
	where mapping = rw / \from -> rw `i` \case
		These (These (U_II_I (This ee)) _) (U_I_II f) -> This (from (f (This ee)))
		These (These _ (U_II_I (This eee))) (U_I_II f) -> This (from (f (That eee)))
		These (These _ (U_II_I (That eee))) _ -> That eee

instance Mapping Straight Straight (->) (->) (Straight (->) Unit) (U_II_I (\/) e)
	where mapping = rw / \from (U_I_II f) -> U_II_I (This (from (f Unit)))

instance Mapping Straight Straight (->) (->) (Straight (->) Unit) (U_I_II (\/) e)
	where mapping = rw / \from (U_I_II f) -> U_I_II (That (from (f Unit)))

instance Mapping Straight Straight (->) (->) (Straight (->) Void) (U_I_II (\/) Unit)
	where mapping = rw / \_ _ -> U_I_II (This Unit)

instance Mapping Straight Straight (->) (->) (Straight (->) Void) (U_II_I (\/) Unit)
	where mapping = rw / \_ _ -> U_II_I (That Unit)

-- TODO: generalize with limits
instance Covariant Monoidal Functor (->) (/\) (/\) g =>
	Mapping Straight Straight (->) (->) (U_I_II (/\) e `T'TT'I` g) (U_I_II (/\) e `TT_T_I` g)
	where mapping = rw / \from -> rw / \case
		U_I_II (These e x) -> x `yo` from `o` These e `o` U_I_II

instance Covariant Endo Semi Functor (->) g =>
	Mapping Straight Straight (->) (->) (g `T'TT'I` U_I_II (->) e) (g `TT_T_I` U_I_II (->) e)
	where mapping = rw / \from -> rw / \x ->
		U_I_II / \e -> x `yo`(from `compose` (`i` e) `compose` uw)
