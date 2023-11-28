{-# OPTIONS_GHC -fno-warn-orphans #-}
{-# LANGUAGE UndecidableInstances #-}
module Ya.Algebra (module Exports) where

import Ya.Algebra.Abstract as Exports
import Ya.Algebra.Definition as Exports
import Ya.Algebra.Instances as Exports ()
import Ya.Algebra.Operators as Exports

instance
	( Covariant Endo Semi Functor (->) t
	, Monoidal Straight Functor (->) (/\) (/\) tt
	) => Mapping Straight Straight (->) (->) t (t `T'TT'I` tt)
	where mapping = rwr / \from -> wrap `compose` semifunctor @Straight @(->) @(->) (yu enter `compose` from)

instance
	( Covariant Endo Semi Functor (->) tt
	, Monoidal Straight Functor (->) (/\) (/\) t
	) => Mapping Straight Straight (->) (->) tt (t `T'TT'I` tt)
	where mapping = rwr / \from -> wrap `compose` yu enter `compose` semifunctor @Straight @(->) @(->) from

instance
	( Covariant Endo Semi Functor (->) t
	, Covariant Monoidal Functor (->) (/\) (/\) tt
	, Component Natural (->) (->) (t `T'TT'I` tt) (t `TT'T'I` tt)
	) => Mapping Straight Straight (->) (->)
		(T'TT'I (t `T'TT'I` R_U_I_T_I (/\) t) tt)
		(TT'T'I (t `T'TT'I` R_U_I_T_I (/\) t) tt)
	where mapping = rwr / \from -> rwr / \(T'TT'I x) ->
		(wrapped (component @Straight @(->) @(->) @(t `T'TT'I` tt) @(t `TT'T'I` tt))
			/ x `yo` wrapped (map @Straight @Straight @(->) @(->)
				@(R_U_I_T_I (/\) t `T'TT'I` tt)
				@(R_U_I_T_I (/\) t `TT'T'I` tt) from)
			) `yo` wrap @(->) @(T'TT'I _ _ _)

-- TODO: I need to reduce transformations here
instance
	( Covariant Endo Semi Functor (->) t
	, Covariant Endo Semi Functor (->) tt
	, Covariant Monoidal Functor (->) (/\) (/\) tt
	, Transformation Straight Functor (->) (->) (T'TT'I t tt) (TT'T'I t tt)
	) => Mapping Straight Straight (->) (->) (R_U_I_T_I (/\) t `T'TT'I` tt) (R_U_I_T_I (/\) t `TT'T'I` tt)
	where mapping = rwr / \from -> rwr `yi` \(R_U_I_T_I (Recursive (U_I_T_II (These x xs)))) ->
		(pp (These
			/ x `yo` from
			/ wrapped (component @Straight @(->) @(->) @(t `T'TT'I` tt) @(t `TT'T'I` tt))
				(xs `yo`wrapped
					(map @Straight @Straight @(->) @(->) @(R_U_I_T_I (/\) t `T'TT'I` tt) @(R_U_I_T_I (/\) t `TT'T'I` tt) from)
						`compose` wrap @(->) @(R_U_I_T_I _ _ _)
					`yo'yo` uw @(->) @(R_U_I_T_I _ _ _)
				)
			)
		) `yo` wrap @(->) @(R_U_I_T_I _ _ _)
			`compose` wrap @(->) @(Recursive _)
			`compose` U_I_T_II

-- instance Mapping Straight Straight (->) (->)
	-- ((t `T'TT'I` R_U_I_T_I (/\) t) `T'TT'I` (t `T'TT'I` R_U_I_T_I (/\) t))
	-- (t `T'TT'I` R_U_I_T_I (/\) t)
	-- where mapping = rwr / \from (T'TT'I x) -> x

instance Mapping Straight Straight (->) (->) (U_I_II (/\) e `T'TT'I` U_I_II (->) e) I
	where mapping = rwr / \from -> rwr / \(U_I_II (These e (U_I_II f))) -> from `i` f e

instance Mapping Straight Straight (->) (->) I (U_I_II (->) e `T'TT'I` U_I_II (/\) e)
	where mapping = rwr / \from -> rwr / \x -> U_I_II `i` \e -> U_I_II `i` These e (from x)

-- TODO: generalize this instance
instance Mapping Opposite Straight (W_I_II_II (U_I_UU_III_U_II_I (->) (/\))) (->)
	(U_II_I (W_I_I_II (U_I_UU_II_III (->) (/\))) e)
	(U_II_I (W_I_I_II (U_I_UU_II_III (->) (/\))) e)
	where mapping = rwr / \(W_I_II_II (U_I_UU_III_U_II_I from)) -> 
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
	where mapping = rwr / \from -> rwr `i'i'i` rwr `i'i` rwr `i` \(U_I_UU_II_III state) old ->
		(\(These s (U_I_II f)) -> from `_fo` f `uw'uw` s) (state old)

instance Covariant Endo Semi Functor (->) t
	=> Mapping Straight Straight (->) (->) t (T_TT_TTT_I (U_I_II (->) e) t (U_I_II (/\) e))
	where mapping = rwr / \from x -> T_TT_TTT_I `compose` U_I_II `yi` \state ->
		x `yo` from `o` These state `o` U_I_II

instance Covariant Monoidal Functor (->) (/\) (/\) t 
	=> Mapping Straight Straight (->) (->)
		(U_I_II (W_I_I_II (U_I_UU_II_III (->) (/\))) e)
		(T_TT_TTT_I (U_I_II (->) e) t (U_I_II (/\) e))
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
		(T_TT_TTT_I (U_I_II (->) old) t (U_I_II (/\) btw))
		(T_TT_TTT_I (U_I_II (->) btw) t (U_I_II (/\) new))
	)
	(T_TT_TTT_I (U_I_II (->) old) t (U_I_II (/\) new))
	where mapping = rwr / \from (T'TT'I (T_TT_TTT_I (U_I_II x))) -> 
		wrap @(->) @(T_TT_TTT_I _ _ _ _) `compose` wrap @(->) @(U_I_II _ _ _)
		`yi` \old -> x old `yokl` \(U_I_II (These btw (T_TT_TTT_I (U_I_II f))))
			-> f btw `yo'yo` from

-- TODO: try to use adjunctions here
instance
	( Covariant Monoidal Functor (->) (/\) (/\) tt
	, Transformation Natural Functor (->) (->) (T'TT'I tt tt) tt
	) => Mapping Straight Straight (->) (->)
	(T'TT'I
		(T_TT_TTT_I (U_I_II (->) e) tt (U_I_II (/\) e))
		(U_I_II (W_I_I_II (U_I_UU_II_III (->) (/\))) e)
	)
	(T_TT_TTT_I (U_I_II (->) e) tt (U_I_II (/\) e))
	where mapping = rwr / \from (T'TT'I (T_TT_TTT_I (U_I_II x))) -> 
		wrap @(->) @(T_TT_TTT_I _ _ _ _) `compose` wrap @(->) @(U_I_II _ _ _)
		`yi` \old -> x old `yokl` \(U_I_II (These btw (U_I_II (W_I_I_II (U_I_UU_II_III f)))))
			-> yu (enter @tt) / U_I_II (f btw) `yo` from

instance
	( Covariant Endo Semi Functor (->) t
	, Mapping Straight Straight (->) (->) (t `T'TT'I` t) t
	) => Mapping Straight Straight (->) (->)
		(T'TT'I (T_TT_TTT_I (Straight (->) e) t (Straight (/\) e)) t)
		(T_TT_TTT_I (Straight (->) e) t (Straight (/\) e))
	where mapping = rwr / \from (T'TT'I (T_TT_TTT_I (U_I_II f))) -> T_TT_TTT_I `compose` U_I_II / \old ->
		component @Straight @(->) @(->) @(t `T'TT'I` t) @t
			(T'TT'I (f old `yo` (\(U_I_II (These x y)) -> y `yo` U_I_II `a` These x `a` from)))

instance Mapping Straight Straight (->) (->) (U_I_II (/\) e `T'TT'I` tt) (U_I_II (/\) e `TT'T'I` tt) =>
	Mapping Straight Straight (->) (->)
		(U_I_II (W_I_I_II (U_I_UU_II_III (->) (/\))) e `T'TT'I` tt)
		(T_TT_TTT_I (U_I_II (->) e) tt (U_I_II (/\) e))
	where mapping = rwr / \from (T'TT'I (U_I_II (W_I_I_II (U_I_UU_II_III x)))) -> 
		T_TT_TTT_I `compose` U_I_II / \old -> wrapped @(->)
			`i` map @Straight @Straight @(->) @(->) @(U_I_II (/\) e `T'TT'I` tt) @(U_I_II (/\) e `TT'T'I` tt) from
			`i'i` U_I_II (x old)

instance Mapping Straight Straight (->) (->) (Straight (->) Unit) I
	where mapping = rwr / \from (U_I_II f) -> I (from (f Unit))

instance Monoidal Straight Functor (->) (/\) (/\) t =>
	Mapping Straight Straight (->) (->) (That (->) Unit) (That (->) e `T'TT'I` t)
	where mapping = rwr / \from -> rwr / \f -> U_I_II / \_ -> yu enter `compose` from `i` f Unit

instance Mapping Straight Straight (->) (->) (That (->) Unit) (U_I_II (W_I_I_II (U_I_UU_II_III (->) (/\))) e)
	where mapping = rwr / \from -> rwr / \f -> W_I_I_II `a` U_I_UU_II_III `yi` \e -> These e (f Unit `u` from)

instance Monoidal Straight Functor (->) (/\) (/\) t =>
	Mapping Straight Straight (->) (->) (That (->) Unit) (T_TT_TTT_I (That (->) e) t (That (/\) e))
	where mapping = rwr / \from (U_I_II f) -> T_TT_TTT_I `compose` U_I_II
		/ \old -> yu enter `compose` U_I_II `compose` These old `compose` from `i'i` f Unit

instance
	( Covariant Semi Functor from (->) t
	, forall e . Covariant Semi Functor into (->) (U_I_II from e)
	) => Mapping Straight Straight from (->) t (UU_V_U_I_II_T_II Straight into (->) t r)
	where mapping = rwr / \from x -> UU_V_U_I_II_T_II (\(U_I_II e) -> e `_fo` from `fo'fi` x)

instance
	( Covariant Endo Semi Functor (->) t
	, forall e . Covariant Endo Semi Functor (->) (U_I_II (->) e)
	) => Mapping Constant Straight (->) (->) t (UU_V_U_I_II_T_II Constant (->) (->) t r)
	where mapping = rwr / \_ x -> UU_V_U_I_II_T_II (\(U_1_I e) -> (\_ -> e Unit) `fo'fi` x)

instance
	( Contravariant Semi Functor from (->) t
	, forall e . Contravariant Semi Functor into (->) (U_II_I from e)
	) => Mapping Opposite Straight from (->) t (UU_V_U_I_II_T_II Opposite into (->) t r)
	where mapping = rwr / \from x -> UU_V_U_I_II_T_II (\(U_II_I e) -> e `fa_` from `fa'fi` x)

instance Mapping Straight Straight (->) (->) (U_I_II (\/) e `T'TT'I` U_I_II (\/) e) (U_I_II (\/) e)
	where mapping = rwr / \from -> \case
		T'TT'I (U_I_II (That (U_I_II (That x)))) -> U_I_II (That / from x)
		T'TT'I (U_I_II (That (U_I_II (This e)))) -> U_I_II (This e)
		T'TT'I (U_I_II (This e)) -> U_I_II (This e)

instance Covariant Monoidal Functor (->) (/\) (/\) t =>
	Mapping Straight Straight (->) (->) (U_I_II (\/) e `T'TT'I` t) (U_I_II (\/) e `TT'T'I` t)
	where mapping = rwr / \from -> rwr / \case
		U_I_II (This e) -> yu enter (U_I_II `i` This e)
		U_I_II (That x) -> x `yo` from `o` That  `o` U_I_II

instance Mapping Straight Straight (->) (->) (Day Straight (->) (/\) (/\) I I e ee) I
	where mapping = rwr / \from -> rwr / \case
		These (These (I e) (I ee)) (U_I_II f) -> from (f (These e ee))

instance Mapping Straight Straight (->) (->) (Day Straight (->) (/\) (/\) (U_I_II (\/) e) (U_I_II (\/) e) ee eee) (U_I_II (\/) e)
	where mapping = rwr / \from -> rwr / \case
		These (These (U_I_II (That ee)) (U_I_II (That eee))) (U_I_II f) -> That (from (f (These ee eee)))
		These (These (U_I_II (This e)) _) (U_I_II _) -> This e
		These (These _ (U_I_II (This e))) (U_I_II _) -> This e

instance Mapping Straight Straight (->) (->) (Day Straight (->) (/\) (\/) (U_I_II (\/) e) (U_I_II (\/) e) ee eee) (U_I_II (\/) e)
	where mapping = rwr / \from -> rwr / \case
		These (These (U_I_II (That ee)) _) (U_I_II f) -> That (from (f (This ee)))
		These (These _ (U_I_II (That eee))) (U_I_II f) -> That (from (f (That eee)))
		These (These _ (U_I_II (This eee))) (U_I_II _) -> This eee

instance Mapping Straight Straight (->) (->) (Day Straight (->) (/\) (/\) (U_II_I (\/) e) (U_II_I (\/) e) ee eee) (U_II_I (\/) e)
	where mapping = rwr / \from -> rwr `i` \case
		These (These (U_II_I (This ee)) (U_II_I (This eee))) (U_I_II f) -> This (from (f (These ee eee)))
		These (These (U_II_I (That e)) _) _ -> That e

instance Mapping Straight Straight (->) (->) (Day Straight (->) (/\) (\/) (U_II_I (\/) e) (U_II_I (\/) e) ee eee) (U_II_I (\/) e)
	where mapping = rwr / \from -> rwr `i` \case
		These (These (U_II_I (This ee)) _) (U_I_II f) -> This (from (f (This ee)))
		These (These _ (U_II_I (This eee))) (U_I_II f) -> This (from (f (That eee)))
		These (These _ (U_II_I (That eee))) _ -> That eee

instance Mapping Straight Straight (->) (->)
	(Day Straight (->) (/\) (/\)
		(U_I_II (W_I_I_II (U_I_UU_II_III (->) (/\))) e)
		(U_I_II (W_I_I_II (U_I_UU_II_III (->) (/\))) e) ee eee)
	(U_I_II (W_I_I_II (U_I_UU_II_III (->) (/\))) e)
	where mapping = rwr / \from -> rwr / \case
		These (These ee eee) (U_I_II f) -> W_I_I_II `a` U_I_UU_II_III `yi` \old ->
			let These new x = ee `uw'uw'uw` old in
			let These upd y = eee `uw'uw'uw` new in
			These upd (f (These x y) `u` from)

instance
	( Component Natural (->) (->) (t `T'TT'I` t) t
	, Covariant Yoneda Functor (->) (->) t
	) => Mapping Straight Straight (->) (->)
		(Day Straight (->) (/\) (/\) (T_TT_TTT_I (U_I_II (->) e) t (U_I_II (/\) e)) (T_TT_TTT_I (U_I_II (->) e) t (U_I_II (/\) e)) ee eee)
		(T_TT_TTT_I (U_I_II (->) e) t (U_I_II (/\) e))
	where mapping = rwr / \from -> rwr / \case
		These (These (T_TT_TTT_I (U_I_II x)) (T_TT_TTT_I (U_I_II y))) (U_I_II f) ->
			U_I_II / \old -> x old `yokl` \(U_I_II (These btw e)) -> from `compose` f `compose` These e `fo'fo` y btw

instance
	( Component Natural (->) (->) (T'TT'I t t) t
	, Monoidal Straight Functor (->) (/\) (/\) t
	) => Mapping Straight Straight (->) (->)
		(Day Straight (->) (/\) (/\) (T'TT'I (That (->) e) t) (T'TT'I (That (->) e) t) ee eee)
		(T'TT'I (That (->) e) t)
	where mapping = rwr / \from -> rwr / \case
		These (These (T'TT'I (U_I_II f)) (T'TT'I (U_I_II g))) (U_I_II h) -> U_I_II / \e ->
			pp (These (f e) (g e)) `yo` h `o` from

instance Mapping Straight Straight (->) (->) (Straight (->) Unit) (U_II_I (\/) e)
	where mapping = rwr / \from (U_I_II f) -> U_II_I (This (from (f Unit)))

instance Mapping Straight Straight (->) (->) (Straight (->) Unit) (U_I_II (\/) e)
	where mapping = rwr / \from (U_I_II f) -> U_I_II (That (from (f Unit)))

instance Mapping Straight Straight (->) (->) (Straight (->) Void) (U_I_II (\/) Unit)
	where mapping = rwr / \_ _ -> U_I_II (This Unit)

instance Mapping Straight Straight (->) (->) (Straight (->) Void) (U_II_I (\/) Unit)
	where mapping = rwr / \_ _ -> U_II_I (That Unit)

-- TODO: generalize with limits
instance Covariant Monoidal Functor (->) (/\) (/\) t =>
	Mapping Straight Straight (->) (->) (U_I_II (/\) e `T'TT'I` t) (U_I_II (/\) e `TT'T'I` t)
	where mapping = rwr / \from -> rwr / \case
		U_I_II (These e x) -> x `yo` from `o` These e `o` U_I_II

instance Covariant Endo Semi Functor (->) t =>
	Mapping Straight Straight (->) (->) (t `T'TT'I` U_I_II (->) e) (t `TT'T'I` U_I_II (->) e)
	where mapping = rwr / \from -> rwr / \x ->
		U_I_II / \e -> x `yo` (from `compose` (`i` e) `compose` uw)
