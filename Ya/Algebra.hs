{-# OPTIONS_GHC -fno-warn-orphans #-}
{-# LANGUAGE UndecidableInstances #-}
module Ya.Algebra (module Exports) where

import Ya.Algebra.Abstract as Exports
import Ya.Algebra.Definition as Exports
import Ya.Algebra.Instances as Exports ()
import Ya.Algebra.Operators as Exports

instance
	( Covariant Endo Semi Functor (->) t
	, Monoidal Straight Functor (->) LM LM tt
	) => Mapping Straight Straight (->) (->) t (t `T'TT'I` tt)
	where mapping = rwr / \from -> wrap `compose` semifunctor @Straight @(->) @(->) (yu enter `compose` from)

instance
	( Covariant Endo Semi Functor (->) tt
	, Monoidal Straight Functor (->) LM LM t
	) => Mapping Straight Straight (->) (->) tt (t `T'TT'I` tt)
	where mapping = rwr / \from -> wrap `compose` yu enter `compose` semifunctor @Straight @(->) @(->) from

-- TODO: reduce a number of transformations here
instance
	( Covariant Endo Semi Functor (->) t
	, Covariant Monoidal Functor (->) LM LM tt
	, Component Natural (->) (->) (t `T'TT'I` tt) (t `TT'T'I` tt)
	, Component Natural (->) (->) (Labeled l (R_U_I_T_I LM t) `T'TT'I` tt) (Labeled l (R_U_I_T_I LM t) `TT'T'I` tt)
	) => Mapping Straight Straight (->) (->)
		(Labeled l (t `T'TT'I` R_U_I_T_I LM t) `T'TT'I` tt)
		(Labeled l (t `T'TT'I` R_U_I_T_I LM t) `TT'T'I` tt)
	where mapping = rwr / \from -> rwr / \(T'_'I (T'TT'I x)) ->
		map @Straight @Straight @(->) @(->) @tt
			(wrap @(->) @(Labeled l (t `T'TT'I` R_U_I_T_I LM t) _)
				`compose` wrap @(->) @(T'TT'I t _ _))
		/ (wrapped (component @Straight @(->) @(->) @(t `T'TT'I` tt) @(t `TT'T'I` tt))
			(x `yo`wrapped (map @Straight @Straight @_ @_
					@(Labeled l (R_U_I_T_I LM t) `T'TT'I` tt)
					@(Labeled l (R_U_I_T_I LM t) `TT'T'I` tt) from)
				`compose` wrap @(->) @(Labeled l (R_U_I_T_I LM t) (tt _))
				`yo'yo`rw @(->) @(Labeled l _ _)
				)
			)

-- TODO: reduce a number of transformations here
instance
	( Covariant Endo Semi Functor (->) t
	, Covariant Endo Semi Functor (->) tt
	, Covariant Monoidal Functor (->) LM LM tt
	, Transformation Straight Functor (->) (->) (T'TT'I t tt) (TT'T'I t tt)
	) => Mapping Straight Straight (->) (->)
		(Forward (R_U_I_T_I LM t) `T'TT'I` tt)
		(Forward (R_U_I_T_I LM t) `TT'T'I` tt)
	where mapping = rwr / \from -> rwr `yi`
		\(T'_'I (R_U_I_T_I (Recursive (U_I_T_II (These x xs))))) ->
			monoidal @Straight @Arrow @tt @LM @LM identity
				(wrap @(->) @(Forward _ _) `compose` wrap @(->) @(R_U_I_T_I _ _ _) `compose` wrap @(->) @(Recursive _) `compose` wrap @(->) @(U_I_T_II _ _ _ _))
				/ (x `yo` from) `lm`
					(wrapped (component @Straight @(->) @_ @(t `T'TT'I` tt) @(t `TT'T'I` tt))
						(xs `yo`wrapped
							(map @Straight @Straight @_ @_
								@(Forward (R_U_I_T_I LM t) `T'TT'I` tt)
								@(Forward (R_U_I_T_I LM t) `TT'T'I` tt)
							from)
								`compose` wrap @(->) @(Forward _ _) `compose` wrap @(->) @(R_U_I_T_I _ _ _)
							`yo'yo` rw @(->) @(R_U_I_T_I _ _ _) `compose` rw @(->) @(Forward _ _)
						)
					)

-- TODO: reduce a number of transformations here
instance
	( Covariant Endo Semi Functor (->) t
	, Covariant Endo Semi Functor (->) tt
	, Covariant Monoidal Functor (->) LM LM tt
	, Transformation Straight Functor (->) (->) (T'TT'I t tt) (TT'T'I t tt)
	) => Mapping Straight Straight (->) (->)
		(Backward (R_U_I_T_I LM t) `T'TT'I` tt)
		(Backward (R_U_I_T_I LM t) `TT'T'I` tt)
	where mapping = rwr / \from -> rwr `yi` \(T'_'I (R_U_I_T_I (Recursive (U_I_T_II (These x xs))))) ->
			(\x' xs' -> wrap @(->) @(Backward _ _)
				`compose` wrap @(->) @(R_U_I_T_I _ _ _)
				`compose` wrap @(->) @(Recursive _)
				`compose` wrap @(->) @(U_I_T_II _ _ _ _)
				/ These x' xs'
			)
			`fo` (x `yo` from)
			`fc` (wrapped (component @Straight @(->) @_ @(t `T'TT'I` tt) @(t `TT'T'I` tt))
				(xs `yo`wrapped
					(map @Straight @Straight @_ @_
						@(Backward (R_U_I_T_I LM t) `T'TT'I` tt)
						@(Backward (R_U_I_T_I LM t) `TT'T'I` tt)
					from) `compose` wrap @(->) @(Backward _ _) `compose` wrap @(->) @(R_U_I_T_I _ _ _)
					`yo'yo` rw @(->) @(R_U_I_T_I _ _ _) `compose` rw @(->) @(Backward _ _)
				)
			)

-- instance Mapping Straight Straight (->) (->)
	-- ((t `T'TT'I` R_U_I_T_I LM t) `T'TT'I` (t `T'TT'I` R_U_I_T_I LM t))
	-- (t `T'TT'I` R_U_I_T_I LM t)
	-- where mapping = rwr / \from (T'TT'I x) -> x

-- TODO: generalize this instance
instance Mapping Opposite Straight (W_I_II_II (U_I_UU_III_U_II_I (->) LM ))(->)
	(U_II_I (W_I_I_II (U_I_UU_II_III (->) LM)) e)
	(U_II_I (W_I_I_II (U_I_UU_II_III (->) LM)) e)
	where mapping = rwr / \(W_I_II_II (U_I_UU_III_U_II_I from)) -> 
		wrap @(->) @(U_II_I _ _ _)
		`compose` wrap @(->) @(W_I_I_II _ _ _)
		`compose` wrap @(->) @(U_I_UU_II_III (->) _ _ _ _)
		`compose` (\state old -> let (These new f) = from old in f `fo_` state new)
		`compose` rw @(->) @(U_I_UU_II_III (->) _ _ _ _)
		`compose` rw @(->) @(W_I_I_II _ _ _) 
		`compose` rw @(->) @(U_II_I _ _ _)

instance Mapping Straight Straight (->) (->)
	(T'TT'I
		(U_I_II (W_I_I_II (U_I_UU_II_III (->) LM)) e)
		(U_I_II (W_I_I_II (U_I_UU_II_III (->) LM)) e)
	)
	(U_I_II (W_I_I_II (U_I_UU_II_III (->) LM)) e)
	where mapping = rwr / \from -> rwr `i'i'i` rwr `i'i` rwr `i` \(U_I_UU_II_III state) old ->
		(\(These s (U_I_II f)) -> from `_fo` f `rw'rw` s) (state old)

instance Covariant Endo Semi Functor (->) t
	=> Mapping Straight Straight (->) (->) t (T_TT_TTT_I (U_I_II (->) e) t (U_I_II LM e))
	where mapping = rwr / \from x -> T_TT_TTT_I `compose` U_I_II `yi` \state ->
		x `yo` from `o` These state `o` U_I_II

instance Covariant Monoidal Functor (->) LM LM t 
	=> Mapping Straight Straight (->) (->)
		(U_I_II (W_I_I_II (U_I_UU_II_III (->) LM)) e)
		(T_TT_TTT_I (U_I_II (->) e) t (U_I_II LM e))
	where mapping = rwr / \from (U_I_II (W_I_I_II (U_I_UU_II_III x))) -> 
		wrap @(->) @(T_TT_TTT_I _ _ _ _)
		`compose` wrap @(->) @(U_I_II _ _ _)
		`identity` (yu enter
			`compose` semifunctor @Straight from
			`compose` wrap @(->) @(U_I_II _ _ _)
			`compose` x)

instance  {-# OVERLAPPABLE #-} Component Natural (->) (->) (T'TT'I t tt) t => Mapping Straight Straight (->) (->)
	(T'TT'I (Straight (->) e `T'TT'I` t) tt) (Straight (->) e `T'TT'I` t)
	where mapping = rwr / \from -> rwr `compose` rwr /
		\(U_I_II f) e -> map @Straight @Straight @(->) @(->) @(t `T'TT'I` tt) @t from (T'TT'I (f e))

instance {-# OVERLAPS #-} Covariant Endo Semi Functor (->) t => Mapping Straight Straight (->) (->)
	(T'TT'I (Straight (->) e `T'TT'I` t) (Straight (->) e)) (Straight (->) e `T'TT'I` t)
	where mapping = rwr / \from -> rwr `compose` rwr /
		\(U_I_II f) e -> f e `yo` unwrap `o` (`i` e) `o` from

-- TODO: try to use adjunctions here
instance
	( Covariant Endo Semi Functor (->) t
	, Transformation Natural Functor (->) (->) (T'TT'I t t) t
	) => Mapping Straight Straight (->) (->)
	(T'TT'I
		(T_TT_TTT_I (U_I_II (->) old) t (U_I_II LM btw))
		(T_TT_TTT_I (U_I_II (->) btw) t (U_I_II LM new))
	)
	(T_TT_TTT_I (U_I_II (->) old) t (U_I_II LM new))
	where mapping = rwr / \from (T'TT'I (T_TT_TTT_I (U_I_II x))) -> 
		wrap @(->) @(T_TT_TTT_I _ _ _ _) `compose` wrap @(->) @(U_I_II _ _ _)
		`yi` \old -> x old `yokl` \(U_I_II (These btw (T_TT_TTT_I (U_I_II f))))
			-> f btw `yo'yo` from

-- TODO: try to use adjunctions here
instance
	( Covariant Monoidal Functor (->) LM LM tt
	, Transformation Natural Functor (->) (->) (T'TT'I tt tt) tt
	) => Mapping Straight Straight (->) (->)
	(T'TT'I
		(T_TT_TTT_I (U_I_II (->) e) tt (U_I_II LM e))
		(U_I_II (W_I_I_II (U_I_UU_II_III (->) LM)) e)
	)
	(T_TT_TTT_I (U_I_II (->) e) tt (U_I_II LM e))
	where mapping = rwr / \from (T'TT'I (T_TT_TTT_I (U_I_II x))) -> 
		wrap @(->) @(T_TT_TTT_I _ _ _ _) `compose` wrap @(->) @(U_I_II _ _ _)
		`yi` \old -> x old `yokl` \(U_I_II (These btw (U_I_II (W_I_I_II (U_I_UU_II_III f)))))
			-> yu (enter @tt) / U_I_II (f btw) `yo` from

instance
	( Covariant Endo Semi Functor (->) t
	, Mapping Straight Straight (->) (->) (t `T'TT'I` t) t
	) => Mapping Straight Straight (->) (->)
		(T'TT'I (T_TT_TTT_I (Straight (->) e) t (Straight LM e)) t)
		(T_TT_TTT_I (Straight (->) e) t (Straight LM e))
	where mapping = rwr / \from (T'TT'I (T_TT_TTT_I (U_I_II f))) -> T_TT_TTT_I `compose` U_I_II / \old ->
		component @Straight @(->) @(->) @(t `T'TT'I` t) @t
			(T'TT'I (f old `yo` (\(U_I_II (These x y)) -> y `yo` U_I_II `a` These x `a` from)))

instance Mapping Straight Straight (->) (->) (That LM e `T'TT'I` tt) (That LM e `TT'T'I` tt) =>
	Mapping Straight Straight (->) (->)
		(U_I_II (W_I_I_II (U_I_UU_II_III (->) LM)) e `T'TT'I` tt)
		(T_TT_TTT_I (U_I_II (->) e) tt (U_I_II LM e))
	where mapping = rwr / \from (T'TT'I (U_I_II (W_I_I_II (U_I_UU_II_III x)))) -> 
		T_TT_TTT_I `compose` U_I_II / \old -> wrapped @(->)
			`i` map @Straight @Straight @(->) @(->) @(That LM e `T'TT'I` tt) @(That LM e `TT'T'I` tt) from
			`i'i` U_I_II (x old)

instance Monoidal Straight Functor (->) LM LM t =>
	Mapping Straight Straight (->) (->) (That (->) Unit) (That (->) e `T'TT'I` t)
	where mapping = rwr / \from -> rwr / \f -> U_I_II / \_ -> yu enter `compose` from `i` f Unit

instance Mapping Straight Straight (->) (->) (That (->) Unit) (That (W_I_I_II (U_I_UU_II_III (->) LM)) e)
	where mapping = rwr / \from -> rwr / \f -> W_I_I_II `a` U_I_UU_II_III `yi` \e -> These e (f Unit `u` from)

instance Monoidal Straight Functor (->) LM LM t =>
	Mapping Straight Straight (->) (->) (That (->) Unit) (T_TT_TTT_I (That (->) e) t (That LM e))
	where mapping = rwr / \from (U_I_II f) -> T_TT_TTT_I `compose` U_I_II
		/ \old -> yu enter `compose` U_I_II `compose` These old `compose` from `i'i` f Unit

instance
	( Covariant Semi Functor from (->) t
	, forall e . Covariant Semi Functor into (->) (That from e)
	) => Mapping Straight Straight from (->) t (UU_V_U_I_II_T_II Straight into (->) t r)
	where mapping = rwr / \from x -> UU_V_U_I_II_T_II (\(U_I_II e) -> fo @from (_fo @into @(->) e from) x)

instance
	( Covariant Endo Semi Functor (->) t
	, forall e . Covariant Endo Semi Functor (->) (That (->) e)
	) => Mapping Constant Straight (->) (->) t (UU_V_U_I_II_T_II Constant (->) (->) t r)
	where mapping = rwr / \_ x -> UU_V_U_I_II_T_II (\(U_1_I e) -> (\_ -> e Unit) `fo` x)

instance
	( Contravariant Semi Functor from (->) t
	, forall e . Contravariant Semi Functor into (->) (U_II_I from e)
	) => Mapping Opposite Straight from (->) t (UU_V_U_I_II_T_II Opposite into (->) t r)
	where mapping = rwr / \from x -> UU_V_U_I_II_T_II (\(U_II_I e) -> fa @from (fa_ @into @(->) e from) x)

instance Mapping Straight Straight (->) (->) (That ML e `T'TT'I` That ML e) (That ML e)
	where mapping = rwr / \from -> \case
		T'TT'I (U_I_II (That (U_I_II (That x)))) -> U_I_II (That / from x)
		T'TT'I (U_I_II (That (U_I_II (This e)))) -> U_I_II (This e)
		T'TT'I (U_I_II (This e)) -> U_I_II (This e)

instance Covariant Monoidal Functor (->) LM LM t =>
	Mapping Straight Straight (->) (->) (That ML e `T'TT'I` t) (That ML e `TT'T'I` t)
	where mapping = rwr / \from -> rwr / \case
		U_I_II (This e) -> yu enter (U_I_II `i` This e)
		U_I_II (That x) -> x `yo` from `o` That  `o` U_I_II

instance Mapping Straight Straight (->) (->)
		(Day Straight (->) LM LM
			(That (W_I_I_II (U_I_UU_II_III (->) LM)) e)
			(That (W_I_I_II (U_I_UU_II_III (->) LM)) e) ee eee)
		(That (W_I_I_II (U_I_UU_II_III (->) LM)) e)
	where mapping = rwr / \from -> rwr / \case
		These (These ee eee) (U_I_II f) -> W_I_I_II `a` U_I_UU_II_III `yi` \old ->
			let These new x = ee `rw'rw'rw` old in
			let These upd y = eee `rw'rw'rw` new in
			These upd (f (These x y) `u` from)

instance
	( Component Natural (->) (->) (t `T'TT'I` t) t
	, Covariant Yoneda Functor (->) (->) t
	) => Mapping Straight Straight (->) (->)
		(Day Straight (->) LM LM (T_TT_TTT_I (That (->) e) t (That LM e)) (T_TT_TTT_I (That (->) e) t (That LM e)) ee eee)
		(T_TT_TTT_I (That (->) e) t (That LM e))
	where mapping = rwr / \from -> rwr / \case
		These (These (T_TT_TTT_I (U_I_II x)) (T_TT_TTT_I (U_I_II y))) (U_I_II f) ->
			U_I_II / \old -> x old `yokl` \(U_I_II (These btw e)) -> from `compose` f `compose` These e `fo'fo` y btw

instance
	( Component Natural (->) (->) (T'TT'I t t) t
	, Monoidal Straight Functor (->) LM LM t
	) => Mapping Straight Straight (->) (->)
		(Day Straight (->) LM LM (T'TT'I (That (->) a) t) (T'TT'I (That (->) a) t) ee eee)
		(T'TT'I (That (->) a) t)
	where mapping = rwr / \from -> rwr / \case
		These (These (T'TT'I (U_I_II f)) (T'TT'I (U_I_II g))) (U_I_II h) -> U_I_II / \a ->
			dp (These (f a) (g a)) `yo` h `o` from

-- TODO: generalize with limits
instance Covariant Monoidal Functor (->) LM LM t =>
	Mapping Straight Straight (->) (->) (That LM e `T'TT'I` t) (That LM e `TT'T'I` t)
	where mapping = rwr / \from -> rwr / \case
		U_I_II (These e x) -> x `yo` from `o` These e `o` U_I_II

instance Covariant Endo Semi Functor (->) t =>
	Mapping Straight Straight (->) (->) (t `T'TT'I` That (->) e) (t `TT'T'I` That (->) e)
	where mapping = rwr / \from -> rwr / \x ->
		U_I_II / \e -> x `yo` (from `compose` (`i` e) `compose` rw)
