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
	) => Mapping Straight Straight (->) (->) t (t `T_TT_I` tt)
	where mapping = rwr / \from -> wrap `compose` map @Straight @Straight @(->) @(->) (yu enter `compose` from)

instance
	( Covariant Endo Semi Functor (->) tt
	, Monoidal Straight Functor (->) LM LM t
	) => Mapping Straight Straight (->) (->) tt (t `T_TT_I` tt)
	where mapping = rwr / \from -> wrap `compose` yu enter `compose` map @Straight @Straight @(->) @(->) from

-- TODO: reduce a number of transformations here
instance
	( Covariant Endo Semi Functor (->) t
	, Covariant Monoidal Functor (->) LM LM tt
	, Component Natural (->) (->) (t `T_TT_I` tt) (t `TT_T_I` tt)
	, Component Natural (->) (->) (Labeled l (R_U_I_T_I LM t) `T_TT_I` tt) (Labeled l (R_U_I_T_I LM t) `TT_T_I` tt)
	) => Mapping Straight Straight (->) (->)
		(Labeled l (t `T_TT_I` R_U_I_T_I LM t) `T_TT_I` tt)
		(Labeled l (t `T_TT_I` R_U_I_T_I LM t) `TT_T_I` tt)
	where mapping = rwr / \from -> rwr / \(T_'_I (T_TT_I x)) ->
		map @Straight @Straight @(->) @(->) @tt
			(wrap @(->) @(Labeled l (t `T_TT_I` R_U_I_T_I LM t) _)
				`compose` wrap @(->) @(T_TT_I t _ _))
		/ (wrapped (component @Straight @(->) @(->) @(t `T_TT_I` tt) @(t `TT_T_I` tt))
			(x `yo`wrapped (map @Straight @Straight @_ @_
					@(Labeled l (R_U_I_T_I LM t) `T_TT_I` tt)
					@(Labeled l (R_U_I_T_I LM t) `TT_T_I` tt) from)
				`compose` wrap @(->) @(Labeled l (R_U_I_T_I LM t) (tt _))
				`yo_yo`rw @(->) @(Labeled l _ _)
				)
			)

-- TODO: reduce a number of transformations here
instance
	( Covariant Endo Semi Functor (->) t
	, Covariant Endo Semi Functor (->) tt
	, Covariant Monoidal Functor (->) LM LM tt
	, Transformation Straight Functor (->) (->) (T_TT_I t tt) (TT_T_I t tt)
	) => Mapping Straight Straight (->) (->)
		(Forward (R_U_I_T_I LM t) `T_TT_I` tt)
		(Forward (R_U_I_T_I LM t) `TT_T_I` tt)
	where mapping = rwr / \from -> rwr `yi`
		\(T_'_I (R_U_I_T_I (Recursive (U_I_T_II (These x xs))))) ->
			day @Straight @Arrow @tt @LM @LM identity
				(wrap @(->) @(Forward _ _) `compose` wrap @(->) @(R_U_I_T_I _ _ _) `compose` wrap @(->) @(Recursive _) `compose` wrap @(->) @(U_I_T_II _ _ _ _))
				/ (x `yo` from) `lm`
					(wrapped (component @Straight @(->) @_ @(t `T_TT_I` tt) @(t `TT_T_I` tt))
						(xs `yo`wrapped
							(map @Straight @Straight @_ @_
								@(Forward (R_U_I_T_I LM t) `T_TT_I` tt)
								@(Forward (R_U_I_T_I LM t) `TT_T_I` tt)
							from)
								`compose` wrap @(->) @(Forward _ _) `compose` wrap @(->) @(R_U_I_T_I _ _ _)
							`yo_yo` rw @(->) @(R_U_I_T_I _ _ _) `compose` rw @(->) @(Forward _ _)
						)
					)

-- TODO: reduce a number of transformations here
instance
	( Covariant Endo Semi Functor (->) t
	, Covariant Endo Semi Functor (->) tt
	, Covariant Monoidal Functor (->) LM LM tt
	, Transformation Straight Functor (->) (->) (T_TT_I t tt) (TT_T_I t tt)
	) => Mapping Straight Straight (->) (->)
		(Backward (R_U_I_T_I LM t) `T_TT_I` tt)
		(Backward (R_U_I_T_I LM t) `TT_T_I` tt)
	where mapping = rwr / \from -> rwr `yi` \(T_'_I (R_U_I_T_I (Recursive (U_I_T_II (These x xs))))) ->
			(\x_ xs_ -> wrap @(->) @(Backward _ _)
				`compose` wrap @(->) @(R_U_I_T_I _ _ _)
				`compose` wrap @(->) @(Recursive _)
				`compose` wrap @(->) @(U_I_T_II _ _ _ _)
				/ These x_ xs_
			)
			`fo` (x `yo` from)
			`fc` (wrapped (component @Straight @(->) @_ @(t `T_TT_I` tt) @(t `TT_T_I` tt))
				(xs `yo`wrapped
					(map @Straight @Straight @_ @_
						@(Backward (R_U_I_T_I LM t) `T_TT_I` tt)
						@(Backward (R_U_I_T_I LM t) `TT_T_I` tt)
					from) `compose` wrap @(->) @(Backward _ _) `compose` wrap @(->) @(R_U_I_T_I _ _ _)
					`yo_yo` rw @(->) @(R_U_I_T_I _ _ _) `compose` rw @(->) @(Backward _ _)
				)
			)

-- TODO: try to simplify
instance
	Mapping Straight Straight (->) (->)
		(Day Straight (->) LM LM t t (Recursive (U_I_T_II t LM e)) (Recursive (U_I_T_II t LM ee))) t =>
	Mapping Straight Straight (->) (->)
		(Day Straight (->) LM LM (R_U_I_T_I LM t) (R_U_I_T_I LM t) e ee) (R_U_I_T_I LM t)
	where mapping = rwr / \from -> rwr / \case
		These (These e ee) (Straight f) ->
			let These e_ e__ = rw_rw_rw e in
			let These ee_ ee__ = rw_rw_rw ee in
			Recursive `compose` U_I_T_II / These
				(from `compose` f / These e_ ee_)
				(day @Straight @Arrow @t @LM @LM identity
					(unwrap
						`compose` day @Straight @(->)
							@(R_U_I_T_I LM t) @LM @LM
								identity (from `compose` f)
						`compose` fio R_U_I_T_I
						`compose` foi R_U_I_T_I)
					/ These e__ ee__)

instance
	Monoidal Straight Functor (->) LM ML t =>
	Mapping Straight Straight (->) (->) (Straight (->) ()) (R_U_I_T_I LM t)
	where mapping = rwr / \from (Straight f) ->
		R_U_I_T_I `compose` Recursive `compose` U_I_T_II
			/ These (from / f ()) (empty @t `yo` absurd)

instance
	( Mapping Straight Straight (->) (->) (Day Straight (->) LM LM t t (R_U_I_T_I LM t e) (R_U_I_T_I LM t ee)) t
	, Mapping Straight Straight (->) (->) (Day Straight (->) LM LM t t (Recursive (U_I_T_II t LM e)) (Recursive (U_I_T_II t LM ee))) t
	) => Mapping Straight Straight (->) (->) (Day Straight (->) LM LM (t `T_TT_I` R_U_I_T_I LM t) (t `T_TT_I` R_U_I_T_I LM t) e ee) (t `T_TT_I` R_U_I_T_I LM t)
	where mapping = rwr / \from -> rwr / \case
		These (These (T_TT_I e) (T_TT_I ee)) (Straight f) ->
				day @Straight @Arrow @t @LM @LM identity
					(day @Straight @Arrow @(R_U_I_T_I LM t) @LM @LM identity (from `compose` f))
						(These e ee)

instance
	( Monoidal Straight Functor (->) LM LM t
	, Monoidal Straight Functor (->) LM LM (R_U_I_T_I LM tt)
	) => Mapping Straight Straight (->) (->) (Straight (->) ()) (t `T_TT_I` R_U_I_T_I LM tt)
	where mapping = rwr / \from (Straight f) -> T_TT_I /
		enter @t `yi_yu` enter @(R_U_I_T_I LM tt) `yo` from `compose` f

-- TODO: try to avoid mapping twice datastructure here
instance
	( Covariant Endo Semi Functor (->) t
	, Mapping Straight Straight (->) (->) (Day Straight (->) LM MLM t t (R_U_I_T_I LM t e) (R_U_I_T_I LM t ee)) t
	, Mapping Straight Straight (->) (->) (Day Straight (->) LM MLM t t (Recursive (U_I_T_II t LM e)) (Recursive (U_I_T_II t LM ee))) t
	) => Mapping Straight Straight (->) (->) (Day Straight (->) LM MLM (t `T_TT_I` R_U_I_T_I LM t) (t `T_TT_I` R_U_I_T_I LM t) e ee) (t `T_TT_I` R_U_I_T_I LM t)
	where mapping = rwr / \from -> rwr / \case
		These (These (T_TT_I e) (T_TT_I ee)) (Straight f) ->
				(day @Straight @Arrow @t @LM @MLM identity
					(\case
						MLM (This (This x)) -> x `yo` from `compose` f `compose` MLM `compose` This `compose` This
						MLM (This (That x)) -> x `yo` from `compose` f `compose` MLM `compose` This `compose` That
						MLM (That x) -> day @Straight @Arrow @(R_U_I_T_I LM t) @LM @MLM identity (from `compose` f) x
					)
						(These e ee)
				)

-- TODO: try to avoid mapping twice datastructure here
instance
	( Covariant Endo Semi Functor (->) t
	, Mapping Straight Straight (->) (->) (Day Straight (->) LM MLM t t (Recursive (U_I_T_II t LM e)) (Recursive (U_I_T_II t LM ee))) t
	) => Mapping Straight Straight (->) (->) (Day Straight (->) LM MLM (R_U_I_T_I LM t) (R_U_I_T_I LM t) e ee) (R_U_I_T_I LM t)
	where mapping = rwr / \from -> rwr / \case
		These (These e ee) (Straight f) ->
			let These e_ e__ = rw_rw_rw e in
			let These ee_ ee__ = rw_rw_rw ee in
			Recursive `compose` U_I_T_II / These
				(from `compose` f `compose` MLM `compose` That / These e_ ee_)
				(day @Straight @Arrow @t @LM @MLM identity
					(unwrap `compose` \case
						MLM (This (This x)) -> R_U_I_T_I x `yo` from `compose` f `compose` MLM `compose` This `compose` This
						MLM (This (That x)) -> R_U_I_T_I x `yo` from `compose` f `compose` MLM `compose` This `compose` That
						MLM (That (These x xx)) -> day @Straight @Arrow @(R_U_I_T_I LM t) @LM @MLM identity (from `compose` f)
							(These (R_U_I_T_I x) (R_U_I_T_I xx))
					)
					/ These e__ ee__)

instance Monoidal Straight Functor (->) LM ML t =>
	Mapping Straight Straight (->) (->) (Straight (->) Void) (t `T_TT_I` R_U_I_T_I LM tt)
	where mapping = rwr / \_ _ -> T_TT_I (empty @t `yo` absurd)

-- TODO: generalize this instance
instance Mapping Opposite Straight (W_I_II_II (U_I_UU_III_U_II_I (->) LM ))(->)
	(Opposite (W_I_I_II (U_I_UU_II_III (->) LM)) e)
	(Opposite (W_I_I_II (U_I_UU_II_III (->) LM)) e)
	where mapping = rwr / \(W_I_II_II (U_I_UU_III_U_II_I from)) -> 
		wrap @(->) @(Opposite _ _ _)
		`compose` wrap @(->) @(W_I_I_II _ _ _)
		`compose` wrap @(->) @(U_I_UU_II_III (->) _ _ _ _)
		`compose` (\state old -> let (These new f) = from old in f `foi` state new)
		`compose` rw @(->) @(U_I_UU_II_III (->) _ _ _ _)
		`compose` rw @(->) @(W_I_I_II _ _ _) 
		`compose` rw @(->) @(Opposite _ _ _)

instance Mapping Straight Straight (->) (->)
	(T_TT_I
		(Straight (W_I_I_II (U_I_UU_II_III (->) LM)) e)
		(Straight (W_I_I_II (U_I_UU_II_III (->) LM)) e)
	)
	(Straight (W_I_I_II (U_I_UU_II_III (->) LM)) e)
	where mapping = rwr / \from -> rwr `i_i_i` rwr `i_i` rwr `i` \(U_I_UU_II_III state) old ->
		(\(These s (Straight f)) -> from `fio` f `rw_rw` s) (state old)

instance Covariant Endo Semi Functor (->) t
	=> Mapping Straight Straight (->) (->) t (T_TTT_TT_I (Straight (->) e) (Straight LM e) t)
	where mapping = rwr / \from x -> T_TTT_TT_I `compose` Straight `yi` \state ->
		x `yo` from `o` These state `o` Straight

instance Covariant Monoidal Functor (->) LM LM t 
	=> Mapping Straight Straight (->) (->)
		(Straight (W_I_I_II (U_I_UU_II_III (->) LM)) e)
		(T_TTT_TT_I (Straight (->) e) (Straight LM e) t)
	where mapping = rwr / \from (Straight (W_I_I_II (U_I_UU_II_III x))) -> 
		wrap @(->) @(T_TTT_TT_I _ _ _ _)
		`compose` wrap @(->) @(Straight _ _ _)
		`identity` (yu enter
			`compose` map @Straight @Straight from
			`compose` wrap @(->) @(Straight _ _ _)
			`compose` x)

instance  {-# OVERLAPPABLE #-} Component Natural (->) (->) (T_TT_I t tt) t => Mapping Straight Straight (->) (->)
	(T_TT_I (Straight (->) e `T_TT_I` t) tt) (Straight (->) e `T_TT_I` t)
	where mapping = rwr / \from -> rwr `compose` rwr /
		\(Straight f) e -> map @Straight @Straight @(->) @(->) @(t `T_TT_I` tt) @t from (T_TT_I (f e))

instance {-# OVERLAPS #-} Covariant Endo Semi Functor (->) t => Mapping Straight Straight (->) (->)
	(T_TT_I (Straight (->) e `T_TT_I` t) (Straight (->) e)) (Straight (->) e `T_TT_I` t)
	where mapping = rwr / \from -> rwr `compose` rwr /
		\(Straight f) e -> f e `yo` unwrap `o` (`i` e) `o` from

-- NOTE: this version allow different type of states, but it requires providing types to make it compile
instance
	( Covariant Endo Semi Functor (->) t
	, Transformation Natural Functor (->) (->) (T_TT_I t t) t
	) => Mapping Straight Straight (->) (->)
	(T_TT_I
		(T_TTT_TT_I (Straight (->) old) (Straight LM btw) t)
		(T_TTT_TT_I (Straight (->) btw) (Straight LM new) t)
	)
	(T_TTT_TT_I (Straight (->) old) (Straight LM new) t)
	where mapping = rwr / \from (T_TT_I (T_TTT_TT_I (Straight x))) -> 
		wrap @(->) @(T_TTT_TT_I _ _ _ _) `compose` wrap @(->) @(Straight _ _ _)
		`yi` \old -> x old `yokl` \(Straight (These btw (T_TTT_TT_I (Straight f))))
			-> f btw `yo_yo` from

-- TODO: try to use adjunctions here
instance
	( Covariant Monoidal Functor (->) LM LM tt
	, Transformation Natural Functor (->) (->) (T_TT_I tt tt) tt
	) => Mapping Straight Straight (->) (->)
	(T_TT_I
		(T_TTT_TT_I (Straight (->) e) (Straight LM e) tt)
		(Straight (W_I_I_II (U_I_UU_II_III (->) LM)) e)
	)
	(T_TTT_TT_I (Straight (->) e) (Straight LM e) tt)
	where mapping = rwr / \from (T_TT_I (T_TTT_TT_I (Straight x))) -> 
		wrap @(->) @(T_TTT_TT_I _ _ _ _) `compose` wrap @(->) @(Straight _ _ _)
		`yi` \old -> x old `yokl` \(Straight (These btw (Straight (W_I_I_II (U_I_UU_II_III f)))))
			-> yu (enter @tt) / Straight (f btw) `yo` from

instance
	( Covariant Endo Semi Functor (->) t
	, Mapping Straight Straight (->) (->) (t `T_TT_I` t) t
	) => Mapping Straight Straight (->) (->)
		(T_TT_I (T_TTT_TT_I (Straight (->) e) (Straight LM e) t) t)
		(T_TTT_TT_I (Straight (->) e) (Straight LM e) t)
	where mapping = rwr / \from (T_TT_I (T_TTT_TT_I (Straight f))) -> T_TTT_TT_I `compose` Straight / \old ->
		component @Straight @(->) @(->) @(t `T_TT_I` t) @t
			(T_TT_I (f old `yo` (\(Straight (These x y)) -> y `yo` Straight `a` These x `a` from)))

instance Mapping Straight Straight (->) (->) (That LM e `T_TT_I` tt) (That LM e `TT_T_I` tt) =>
	Mapping Straight Straight (->) (->)
		(Straight (W_I_I_II (U_I_UU_II_III (->) LM)) e `T_TT_I` tt)
		(T_TTT_TT_I (Straight (->) e) (Straight LM e) tt)
	where mapping = rwr / \from (T_TT_I (Straight (W_I_I_II (U_I_UU_II_III x)))) -> 
		T_TTT_TT_I `compose` Straight / \old -> wrapped @(->)
			`i` map @Straight @Straight @(->) @(->) @(That LM e `T_TT_I` tt) @(That LM e `TT_T_I` tt) from
			`i_i` Straight (x old)

instance Monoidal Straight Functor (->) LM LM t =>
	Mapping Straight Straight (->) (->) (That (->) ()) (That (->) e `T_TT_I` t)
	where mapping = rwr / \from -> rwr / \f -> Straight / \_ -> yu enter `compose` from `i` f ()

instance Mapping Straight Straight (->) (->) (That (->) ()) (That (W_I_I_II (U_I_UU_II_III (->) LM)) e)
	where mapping = rwr / \from -> rwr / \f -> W_I_I_II `a` U_I_UU_II_III `yi` \e -> These e (f () `u` from)

instance Monoidal Straight Functor (->) LM LM t =>
	Mapping Straight Straight (->) (->) (That (->) ()) (T_TTT_TT_I (That (->) e) (That LM e) t)
	where mapping = rwr / \from (Straight f) -> T_TTT_TT_I `compose` Straight
		/ \old -> yu enter `compose` Straight `compose` These old `compose` from `i_i` f ()

instance
	( Covariant Semi Functor from (->) t
	, forall e . Covariant Semi Functor into (->) (That from e)
	) => Mapping Straight Straight from (->) t (UU_V_U_I_II_T_II Straight into (->) t r)
	where mapping = rwr / \from x -> UU_V_U_I_II_T_II (\(Straight e) -> fo @from (fio @into @(->) e from) x)

instance
	( Covariant Endo Semi Functor (->) t
	, forall e . Covariant Endo Semi Functor (->) (That (->) e)
	) => Mapping Constant Straight (->) (->) t (UU_V_U_I_II_T_II Constant (->) (->) t r)
	where mapping = rwr / \_ x -> UU_V_U_I_II_T_II (\(U_1_I e) -> (\_ -> e ()) `fo` x)

instance
	( Contravariant Semi Functor from (->) t
	, forall e . Contravariant Semi Functor into (->) (Opposite from e)
	) => Mapping Opposite Straight from (->) t (UU_V_U_I_II_T_II Opposite into (->) t r)
	where mapping = rwr / \from x -> UU_V_U_I_II_T_II (\(Opposite e) -> fa @from (fai @into @(->) e from) x)

instance Mapping Straight Straight (->) (->) (That ML e `T_TT_I` That ML e) (That ML e)
	where mapping = rwr / \from -> \case
		T_TT_I (Straight (That (Straight (That x)))) -> Straight (That / from x)
		T_TT_I (Straight (That (Straight (This e)))) -> Straight (This e)
		T_TT_I (Straight (This e)) -> Straight (This e)

instance Covariant Monoidal Functor (->) LM LM t =>
	Mapping Straight Straight (->) (->) (That ML e `T_TT_I` t) (That ML e `TT_T_I` t)
	where mapping = rwr / \from -> rwr / \case
		Straight (This e) -> yu enter (Straight `i` This e)
		Straight (That x) -> x `yo` from `o` That  `o` Straight

instance Mapping Straight Straight (->) (->)
		(Day Straight (->) LM LM
			(That (W_I_I_II (U_I_UU_II_III (->) LM)) e)
			(That (W_I_I_II (U_I_UU_II_III (->) LM)) e) ee eee)
		(That (W_I_I_II (U_I_UU_II_III (->) LM)) e)
	where mapping = rwr / \from -> rwr / \case
		These (These ee eee) (Straight f) -> W_I_I_II `a` U_I_UU_II_III `yi` \old ->
			let These new x = ee `rw_rw_rw` old in
			let These upd y = eee `rw_rw_rw` new in
			These upd (f (These x y) `u` from)

instance
	( Component Natural (->) (->) (t `T_TT_I` t) t
	, Covariant Yoneda Functor (->) (->) t
	) => Mapping Straight Straight (->) (->)
		(Day Straight (->) LM LM (T_TTT_TT_I (That (->) e) (That LM e) t) (T_TTT_TT_I (That (->) e) (That LM e) t) ee eee)
		(T_TTT_TT_I (That (->) e) (That LM e) t)
	where mapping = rwr / \from -> rwr / \case
		These (These (T_TTT_TT_I (Straight x)) (T_TTT_TT_I (Straight y))) (Straight f) ->
			Straight / \old -> x old `yokl` \(Straight (These btw e)) -> from `compose` f `compose` These e `fo_fo` y btw

instance
	( Component Natural (->) (->) (t `T_TT_I` t) t
	, Monoidal Straight Functor (->) LM LM t
	) => Mapping Straight Straight (->) (->)
		(Day Straight (->) LM LM (T_TT_I (That (->) a) t) (That (->) a `T_TT_I` t) ee eee)
		(T_TT_I (That (->) a) t)
	where mapping = rwr / \from -> rwr / \case
		These (These (T_TT_I (Straight f)) (T_TT_I (Straight g))) (Straight h) -> Straight / \a ->
			dp (These (f a) (g a)) `yo` h `o` from

-- TODO: generalize with limits
instance Covariant Monoidal Functor (->) LM LM t =>
	Mapping Straight Straight (->) (->) (That LM e `T_TT_I` t) (That LM e `TT_T_I` t)
	where mapping = rwr / \from -> rwr / \case
		Straight (These e x) -> x `yo` from `o` These e `o` Straight

instance Covariant Endo Semi Functor (->) t =>
	Mapping Straight Straight (->) (->) (t `T_TT_I` That (->) e) (t `TT_T_I` That (->) e)
	where mapping = rwr / \from -> rwr / \x ->
		Straight / \e -> x `yo` (from `compose` (`i` e) `compose` rw)
