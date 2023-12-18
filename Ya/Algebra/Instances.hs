{-# OPTIONS_GHC -fno-warn-orphans #-}
{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE UndecidableInstances #-}
module Ya.Algebra.Instances where

import Ya.Algebra.Abstract
import Ya.Algebra.Definition

instance
	( Precategory into
	, forall e . Wrapper into (I e)
	) => Mapping Straight Straight into into I I
	where mapping = rwr rwr

instance
	( forall e . Wrapper into (I e)
	, forall e . Wrapper into (TT'T'I I t e)
	, forall e . Wrapper into (T'TT'I I t e)
	, Covariant Endo Semi Functor into t
	) => Mapping Straight Straight into into (T'TT'I I t) (TT'T'I I t)
	where mapping = rwr / \from -> rwr /
		semifunctor @Straight @into @into (wrap `compose` from) `compose` rw @into

instance
	( Covariant Semi Functor from into tt
	, Covariant Endo Semi Functor into t
	, forall e . Wrapper into (T'TT'I t tt e)
	) => Mapping Straight Straight from into (T'TT'I t tt) (T'TT'I t tt)
	where mapping = rwr / \from -> wrap @into
		`compose` (semifunctor @Straight @into @into
			`compose` semifunctor @Straight @from @into
			) from
		`compose` rw @into

instance
	( Covariant Semi Functor from into t
	, Covariant Endo Semi Functor into tt
	, forall e . Wrapper into (TT'T'I t tt e)
	) => Mapping Straight Straight from into (TT'T'I t tt) (TT'T'I t tt)
	where mapping = rwr / \from -> wrap @into
		`compose` (semifunctor @Straight @into @into
			`compose` semifunctor @Straight @from @into
			) from
		`compose` rw @into

instance
	( Covariant Semi Functor from into t
	, forall e . Wrapper into (T'_'I l t e)
	) => Mapping Straight Straight from into (T'_'I l t) (T'_'I l t)
	where mapping = rwr / \from -> wrap @into @(T'_'I _ t _)
		`compose` semifunctor @Straight @from @into @t from
		`compose` rw @into @(T'_'I _ t _)

instance
	( Covariant Semi Functor from into t
	, forall ee . Covariant Endo Semi Functor into (U_I_II u ee)
	, forall ee . Wrapper into (U_I_II (U_I_T_II t u) e ee)
	, forall ee . Wrapper into (U_I_T_II t u e ee)
	, forall ee . Wrapper into (U_I_II u e (t ee))
	) => Mapping Straight Straight from into (U_I_II (U_I_T_II t u) e) (U_I_II (U_I_T_II t u) e)
	where mapping = rwr / \from ->
		wrap @into @(U_I_II _ _ _)
		`compose` wrap @into @(U_I_T_II _ _ _ _)
		`compose` rw @into @(U_I_II _ _ _)
		`compose` semifunctor @Straight @into @into (semifunctor @Straight @from @into from)
		`compose` wrap @into @(U_I_II _ _ _)
		`compose` rw @into @(U_I_T_II _ _ _ _)
		`compose` rw @into @(U_I_II _ _ _)

instance
	( forall ee . Covariant Semi Functor from into (U_II_I u ee)
	, forall ee . Wrapper into (U_II_I (U_I_T_II t u) e ee)
	, forall ee . Wrapper into (U_I_T_II t u ee e)
	, forall ee . Wrapper into (U_II_I u (t e) ee)
	) => Mapping Straight Straight from into (U_II_I (U_I_T_II t u) e) (U_II_I (U_I_T_II t u) e)
	where mapping = rwr / \from -> 
		wrap @into @(U_II_I _ _ _)
		`compose` wrap @into @(U_I_T_II _ _ _ _)
		`compose` rw @into @(U_II_I _ _ _)
		`compose` semifunctor @Straight @from @into from
		`compose` wrap @into @(U_II_I _ _ _)
		`compose` rw @into @(U_I_T_II _ _ _ _)
		`compose` rw @into @(U_II_I _ _ _)

instance
	( Covariant Semi Functor from into h
	, Covariant Endo Semi Functor into tt
	, Covariant Endo Semi Functor into t
	, forall e . Wrapper into (T_TT_TTT_I t tt h e)
	) => Mapping Straight Straight from into (T_TT_TTT_I t tt h) (T_TT_TTT_I t tt h)
	where mapping = rwr / \from -> wrap @into
		`compose` (semifunctor @Straight @into @into
			`compose` semifunctor @Straight @into @into
			`compose` semifunctor @Straight @from @into
			) from
		`compose` rw @into

instance
	( forall e . Covariant Endo Semi Functor into (U_I_II u (t e))
	, forall e . Covariant Endo Semi Functor into (U_II_I u (tt e))
	, Covariant Semi Functor from into tt
	, Covariant Semi Functor from into t
	, forall e . Wrapper into (U_T_I_TT_I u t tt e)
	, forall e ee . Wrapper into (U_I_II u (t e) (tt ee))
	, forall e ee . Wrapper into (U_II_I u (tt e) (t ee))
	) => Mapping Straight Straight from into (U_T_I_TT_I u t tt) (U_T_I_TT_I u t tt)
	where mapping = rwr / \from -> rwr /
		wrapped @into (semifunctor @Straight @into @into @(U_II_I u _) `compose` semifunctor @Straight @from @into / from) `compose`
		wrapped @into (semifunctor @Straight @into @into @(U_I_II u _) `compose` semifunctor @Straight @from @into / from)

instance
	( forall e . Covariant Endo Semi Functor (->) (U_I_II u e)
	, forall e . Covariant Endo Semi Functor (->) (U_II_I u e)
	, Covariant Monoidal Functor from u u ttt
	, Component Natural from (->) (t `T'TT'I` ttt) (t `TT'T'I` ttt)
	, Component Natural from (->) (tt `T'TT'I` ttt) (tt `TT'T'I` ttt)
	, forall e . Wrapper from (U_T_I_TT_I u t tt e)
	, forall e . Wrapper (->) (TT'T'I (U_T_I_TT_I u t tt) ttt e)
	, forall e . Wrapper (->) (T'TT'I (U_T_I_TT_I u t tt) ttt e)
	) => Mapping Straight Straight from (->) (U_T_I_TT_I u t tt `T'TT'I` ttt) (U_T_I_TT_I u t tt `TT'T'I` ttt)
	where mapping = rwr / \from -> rwr /
		monoidal @Straight @from @ttt @u @u (wrap @_ @(U_T_I_TT_I u t tt _)) identity `compose`
			wrapped (semifunctor @Straight @(->) @(->) @(U_II_I u _)
				(wrapped (map @Straight @Straight @from @(->) @(t `T'TT'I` ttt) @(t `TT'T'I` ttt) from))) `compose`
			wrapped (semifunctor @Straight @(->) @(->) @(U_I_II u _)
				(wrapped (map @Straight @Straight @from @(->) @(tt `T'TT'I` ttt) @(tt `TT'T'I` ttt) from))) `compose`
			rw @(->) @(U_T_I_TT_I u t tt _)

-- TODO: here should be a generalized version of an instance above
-- instance
	-- ( forall e . Covariant Endo Semi Functor into (U_I_II (u :: * -> * -> *) (t e))
	-- , forall e . Wrapper into (U_T_I_TT_I u t tt e)
	-- , forall e . Wrapper into (TT'T'I (U_T_I_TT_I u t tt) ttt e)
	-- , forall e . Wrapper into (T'TT'I (U_T_I_TT_I u t tt) ttt e)
	-- ) => Mapping Straight Straight from into (U_T_I_TT_I u t tt `T'TT'I` ttt) (U_T_I_TT_I u t tt `TT'T'I` ttt)
	-- where mapping = rwr / \from -> rwr /
		-- monoidal' @Straight @from @from @ttt @u @u (wrap @_ @(U_T_I_TT_I u t tt _)) identity `compose`
			-- wrapped (semifunctor @Straight @into @into @(U_II_I u _)
				-- (wrapped (map @Straight @Straight @from @into @(t `T'TT'I` ttt) @(t `TT'T'I` ttt) from))) `compose`
			-- wrapped (semifunctor @Straight @into @into @(U_I_II u _)
				-- (wrapped (map @Straight @Straight @from @into @(tt `T'TT'I` ttt) @(tt `TT'T'I` ttt) from))) `compose`
			-- rw @into @(U_T_I_TT_I u t tt _)

instance Mapping Straight Straight (->) (->) (U_I_II LM e `T'TT'I` U_I_II (->) e) I
	where mapping = rwr / \from -> rwr / \(U_I_II (These e (U_I_II f))) -> from (f e)

instance Mapping Straight Straight (->) (->) I (U_I_II (->) e `T'TT'I` U_I_II LM e)
	where mapping = rwr / \from -> rwr / \x -> U_I_II / \e -> U_I_II (These e (from x))

instance Mapping Straight Straight Arrow Arrow (That LM e) (That LM e)
	where mapping = rwr / \from -> rwr / \case
		These e x -> These e (from x)

instance Mapping Straight Straight Arrow Arrow (This LM o) (This LM o)
	where mapping = rwr / \from -> rwr / \case
		These x e -> These (from x) e

instance Mapping Straight Straight Arrow Arrow (That ML o) (That ML o)
	where mapping = rwr / \from -> rwr / \case
		That x -> That (from x)
		This e -> This e

instance Mapping Straight Straight Arrow Arrow (This ML o) (This ML o)
	where mapping = rwr / \from -> rwr / \case
		This x -> This (from x)
		That e -> That e

instance
	( Covariant Semi Functor from Arrow t
	, Covariant Functor from from (U_I_I u)
	, Covariant Monoidal Functor from u u t
	, forall e . Castable Opposite from (Both u e)
	) => Mapping Straight Straight from Arrow (U_I_I u `T'TT'I` t) (U_I_I u `TT'T'I` t)
	where mapping = rwr / \from -> rwr /
		monoidal @Straight @from @t @u @u
			(semifunctor @Straight from `compose` wrap @from @(Both _ _)) identity
		`compose` rw @Arrow @(U_I_I u _)

instance
	( Covariant Semi Functor Arrow Arrow t
	, Covariant Functor Arrow Arrow (U_I_I u)
	, Covariant Monoidal Functor Arrow u u tt
	, Mapping Straight Straight Arrow Arrow (T'TT'I t tt) (TT'T'I t tt)
	) => Mapping Straight Straight Arrow Arrow
		((U_I_I u `T'TT'I` t) `T'TT'I` tt)
		((U_I_I u `T'TT'I` t) `TT'T'I` tt)
	where mapping = rwr / \from -> rwr /
		semifunctor @Straight @Arrow @Arrow (wrap @Arrow @(T'TT'I (U_I_I u) t _)) `compose`
		wrapped (component @Straight @Arrow @Arrow @(T'TT'I (U_I_I u) tt) @(TT'T'I (U_I_I u) tt)) `compose`
		semifunctor @Straight @Arrow @Arrow @(U_I_I u)
			(wrapped / map @Straight @Straight @Arrow @Arrow @(T'TT'I t tt) @(TT'T'I t tt) from) `compose`
		rw @Arrow

instance Covariant Yoneda Functor Arrow Arrow tt =>
	Mapping Straight Straight Arrow Arrow (This LM e `T'TT'I` tt) (This LM e `TT'T'I` tt)
	where mapping = rwr / \from -> rwr / \(U_II_I (These x e)) ->
		yoneda @Straight @Functor x (U_II_I `compose` (\x' -> These (from x') e))

instance
	( Covariant Semi Functor into into (U_I_II u e)
	, Covariant Semi Functor from into (U_I_II uu e)
	, forall ee . Wrapper into (U_I_II (W_I_I_II (U_I_UU_II_III u uu)) e ee)
	, forall ee . Wrapper into (W_I_I_II (U_I_UU_II_III u uu) e ee)
	, forall ee . Wrapper into (U_I_UU_II_III u uu e e ee)
	, forall ee . Wrapper into (U_I_II u e ee)
	, forall ee . Wrapper into (U_I_II uu e ee)
	) => Mapping Straight Straight from into
	(U_I_II (W_I_I_II (U_I_UU_II_III u uu)) e)
	(U_I_II (W_I_I_II (U_I_UU_II_III u uu)) e)
	where mapping = rwr / \from ->
		wrap @into @(U_I_II _ _ _)
		`compose` wrap @into @(W_I_I_II _ _ _)
		`compose` wrap @into @(U_I_UU_II_III _ _ _ _ _)
		`compose` rw @into @(U_I_II u _ _)
		`compose` semifunctor @Straight @into @into
			(rw @into @(U_I_II uu _ _)
			`compose` semifunctor @Straight @from @into from
			`compose` wrap @into @(U_I_II uu _ _))
		`compose` wrap @into @(U_I_II u _ _)
		`compose` rw @into @(U_I_UU_II_III _ _ _ _ _)
		`compose` rw @into @(W_I_I_II _ _ _)
		`compose` rw @into @(U_I_II _ _ _)

instance Mapping Straight Straight Arrow Arrow
	(UU_V_U_I_II_T_II Straight Arrow Arrow t e)
	(UU_V_U_I_II_T_II Straight Arrow Arrow t e)
	where mapping = rwr / \from -> rwr (`compose` (rwr (`compose` from)))

instance Mapping Opposite Straight Arrow Arrow
	(UU_V_U_I_II_T_II Opposite Arrow Arrow t e)
	(UU_V_U_I_II_T_II Opposite Arrow Arrow t e)
	where mapping = rwr / \from -> rwr (`compose` (rwr (compose from)))

-- TODO: implement `mapping` method
instance Mapping Straight Straight (W_I_II_II (U_I_UU_III_U_II_I (->) LM)) (->)
	(UU_V_U_I_II_T_II Straight (W_I_II_II (U_I_UU_III_U_II_I (->) LM)) (->) (Straight (W_I_II_II (U_I_UU_III_U_II_I (->) LM)) ee) e)
	(UU_V_U_I_II_T_II Straight (W_I_II_II (U_I_UU_III_U_II_I (->) LM)) (->) (Straight (W_I_II_II (U_I_UU_III_U_II_I (->) LM)) ee) e)

-- TODO: implement `mapping` method
instance Mapping Opposite Straight (W_I_II_II (U_I_UU_III_U_II_I (->) LM)) (->)
	(UU_V_U_I_II_T_II U_II_I (W_I_II_II (U_I_UU_III_U_II_I (->) LM)) (->) (U_II_I (W_I_I_II (U_I_UU_II_III (->) LM)) ee) e)
	(UU_V_U_I_II_T_II U_II_I (W_I_II_II (U_I_UU_III_U_II_I (->) LM)) (->) (U_II_I (W_I_I_II (U_I_UU_II_III (->) LM)) ee) e)

instance
	( forall e . Covariant Semi Functor from into (U_I_II (U_I_T_II t u) e)
	, forall e . Covariant Semi Functor from into (U_II_I (U_I_T_II t u) e)
	, forall e . Covariant Endo Semi Functor from (U_I_II (U_I_T_II t u) e)
	, forall e . Covariant Endo Semi Functor from (U_II_I (U_I_T_II t u) e)
	, forall e . Wrapper from (R_U_I_T_I u t e)
	, forall e . Wrapper into (R_U_I_T_I u t e)
	, forall e . Wrapper from (Recursive (U_I_T_II t u e))
	, forall e . Wrapper into (Recursive (U_I_T_II t u e))
	, forall e ee . Wrapper from (U_II_I (U_I_T_II t u) e ee)
	, forall e ee . Wrapper into (U_II_I (U_I_T_II t u) e ee)
	, forall e ee . Wrapper from (U_I_II (U_I_T_II t u) e ee)
	, forall e ee . Wrapper into (U_I_II (U_I_T_II t u) e ee)
	) => Mapping Straight Straight from into (R_U_I_T_I u t) (R_U_I_T_I u t)
	where mapping = rwr / \from ->
		wrap @into @(R_U_I_T_I u t _)
		`compose` wrap @into @(Recursive _)
		`compose` rw @into @(U_II_I _ _ _)
		`compose` semifunctor @Straight from
		`compose` wrap @into @(U_II_I _ _ _)
		`compose` rw @into @(U_I_II _ _ _)
		`compose` semifunctor @Straight
			(rw @from
			`compose` semifunctor @Straight @from from
			`compose` wrap @from @(R_U_I_T_I u t _))
		`compose` wrap @into @(U_I_II _ _ _)
		`compose` rw @into @(Recursive _)
		`compose` rw @into @(R_U_I_T_I u t _)

instance Mapping Straight Straight Arrow Arrow (Straight Arrow a) (Straight Arrow a)
	where mapping (U_I_II from) = U_I_II / \(U_I_II between) -> U_I_II (\x -> from (between x))

instance Mapping Opposite Straight Arrow Arrow (Opposite Arrow o) (Opposite Arrow o)
	where mapping (U_II_I from) = U_I_II / \(U_II_I between) -> U_II_I (\x -> between (from x))

instance Category Arrow where
	identity = \x -> x

instance Mapping Straight Straight Arrow into t tt
	=> Mapping Constant Straight Arrow into t tt
	where mapping (U_1_I x) = mapping (U_I_II (\_ -> x Unit))

instance Mapping Straight Straight Arrow Arrow (U_1_I (->) e) (U_1_I (->) e)
	where mapping = rwr / \from (U_1_I x) -> U_1_I / \_ -> from / x Unit

instance Mapping Straight Straight Arrow Arrow I (Both LM)
	where mapping (U_I_II from) = U_I_II / \(I x) -> U_I_I (These (from x) (from x))

-- TODO: redefine using limits
instance Mapping Straight Straight Arrow Arrow (Both LM) (Both LM)
	where mapping (U_I_II from) = U_I_II / \(U_I_I (These x y)) -> U_I_I (These (from x) (from y))

instance Mapping Straight Straight Arrow Arrow (U_I_II LM e) I
	where mapping (U_I_II from) = U_I_II / \(U_I_II (These _ x)) -> I (from x)

instance Mapping Straight Straight Arrow Arrow (U_II_I LM e) I
	where mapping (U_I_II from) = U_I_II / \(U_II_I (These x _)) -> I (from x)

instance Mapping Straight Straight Arrow Arrow (Both ML) I
	where mapping (U_I_II from) = U_I_II / \case
		U_I_I (This x) -> I (from x)
		U_I_I (That x) -> I (from x)

instance Mapping Straight Straight Arrow Arrow I (U_I_II ML e)
	where mapping (U_I_II from) = U_I_II / \(I x) -> U_I_II (That (from x))

instance Mapping Straight Straight Arrow Arrow I (U_II_I ML e)
	where mapping (U_I_II from) = U_I_II / \(I x) -> U_II_I (This (from x))
 
instance Mapping Straight Straight (W_I_II_II (U_I_UU_III_U_II_I (->) LM)) Arrow
	(U_I_II (W_I_II_II (U_I_UU_III_U_II_I (->) LM)) origin)
	(U_I_II (W_I_II_II (U_I_UU_III_U_II_I (->) LM)) origin)
	where mapping = rwr / \into -> rwr `compose` rwr `compose` rwr / \from origin ->
		let These source source_origin = from origin in
		let These target target_source = (rw `compose` rw) into source in
		These target (source_origin `compose` target_source)

instance Mapping Opposite Straight (W_I_II_II (U_I_UU_III_U_II_I (->) LM)) Arrow
	(U_II_I (W_I_II_II (U_I_UU_III_U_II_I (->) LM)) origin)
	(U_II_I (W_I_II_II (U_I_UU_III_U_II_I (->) LM)) origin)
	where mapping = rwr / \from -> rwr `compose` rwr `compose` rwr / \into origin ->
		let These source source_origin = (rw `compose` rw) from origin in
		let These target target_source = into source in
		These target (source_origin `compose` target_source)

instance Category (W_I_II_II (U_I_UU_III_U_II_I (->) LM)) where
	identity = W_I_II_II `compose` U_I_UU_III_U_II_I / \x -> These x identity

instance Mapping Straight Straight
	(W_I_II_II (U_I_UU_III_U_II_I (->) LM))
	(W_I_II_II (U_I_UU_III_U_II_I (->) LM))
	(This LM e) I
	where mapping = rwr `compose` rwr `compose` rwr /
		\from (U_II_I (These old e)) -> These 
			(I (wrapped (left @Straight @(->) identity) (from old)))
			(\(I new) -> U_II_I (These ((wrapped (right @Straight @(->) identity) (from old)) new) e))

instance Mapping Straight Straight
	(W_I_II_II (U_I_UU_III_U_II_I (->) LM))
	(W_I_II_II (U_I_UU_III_U_II_I (->) LM))
	(That LM e) I
	where mapping = rwr `compose` rwr `compose` rwr /
		\from (U_I_II (These e old)) -> These 
			/ I (wrapped (left @Straight @(->) identity) (from old))
			/ \(I new) -> U_I_II (These e ((wrapped (right @Straight @(->) identity) (from old)) new))

instance Mapping Straight Straight (W_I_II_II (U_I_UU_III_U_II_I (->) LM)) (->) I (Both LM)
	where mapping = rwr / \(W_I_II_II (U_I_UU_III_U_II_I from)) (I old) -> U_I_I / These
		(wrapped (left @Straight @(->) identity) (from old))
		(wrapped (left @Straight @(->) identity) (from old))

instance Mapping Opposite Straight (W_I_II_II (U_I_UU_III_U_II_I (->) LM)) (->) (This (->) e) (This (->) e)
	where mapping = rwr / \(W_I_II_II (U_I_UU_III_U_II_I from)) ->
		map @Opposite @Straight / (\(These x _) -> x) `compose` from

instance Mapping Straight Straight (->) (->)
		(Day Straight (->) LM LM I I e ee) I
	where mapping = rwr / \from -> rwr / \case
		These (These (I e) (I ee)) (U_I_II f) -> from (f (These e ee))

instance Mapping Straight Straight (->) (->) (Straight (->) Unit) I
	where mapping = rwr / \from (U_I_II f) -> I (from (f Unit))

-- TODO: instance Mapping Straight Straight (->) (->) (Day Straight (->) LM ML I I e ee) I
-- TODO: instance Mapping Straight Straight (->) (->) (Straight (->) Void) I

instance Mapping Straight Straight (->) (->)
		(Day Straight (->) LM LM (That ML e) (That ML e) ee eee) (That ML e)
	where mapping = rwr / \from -> rwr / \case
		These (These (U_I_II (That ee)) (U_I_II (That eee))) (U_I_II f) -> That (from (f (These ee eee)))
		These (These (U_I_II (This e)) _) (U_I_II _) -> This e
		These (These _ (U_I_II (This e))) (U_I_II _) -> This e

instance Mapping Straight Straight (->) (->)
		(Day Straight (->) LM ML (That ML e) (That ML e) ee eee) (That ML e)
	where mapping = rwr / \from -> rwr / \case
		These (These (U_I_II (That ee)) _) (U_I_II f) -> That (from (f (This ee)))
		These (These _ (U_I_II (That eee))) (U_I_II f) -> That (from (f (That eee)))
		These (These _ (U_I_II (This eee))) (U_I_II _) -> This eee

instance Mapping Straight Straight (->) (->)
		(Day Straight (->) LM LM (This ML e) (This ML e) ee eee) (This ML e)
	where mapping = rwr / \from -> rwr / \case
		These (These (U_II_I (This ee)) (U_II_I (This eee))) (U_I_II f) -> This (from (f (These ee eee)))
		These (These (U_II_I (That e)) _) _ -> That e

instance Mapping Straight Straight (->) (->)
		(Day Straight (->) LM ML (This ML e) (This ML e) ee eee) (This ML e)
	where mapping = rwr / \from -> rwr / \case
		These (These (U_II_I (This ee)) _) (U_I_II f) -> This (from (f (This ee)))
		These (These _ (U_II_I (This eee))) (U_I_II f) -> This (from (f (That eee)))
		These (These _ (U_II_I (That eee))) _ -> That eee
