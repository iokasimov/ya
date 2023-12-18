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
	, forall ee . Covariant Endo Semi Functor into (Straight u ee)
	, forall ee . Wrapper into (Straight (U_I_T_II t u) e ee)
	, forall ee . Wrapper into (U_I_T_II t u e ee)
	, forall ee . Wrapper into (Straight u e (t ee))
	) => Mapping Straight Straight from into (Straight (U_I_T_II t u) e) (Straight (U_I_T_II t u) e)
	where mapping = rwr / \from ->
		wrap @into @(Straight _ _ _)
		`compose` wrap @into @(U_I_T_II _ _ _ _)
		`compose` rw @into @(Straight _ _ _)
		`compose` semifunctor @Straight @into @into (semifunctor @Straight @from @into from)
		`compose` wrap @into @(Straight _ _ _)
		`compose` rw @into @(U_I_T_II _ _ _ _)
		`compose` rw @into @(Straight _ _ _)

instance
	( forall ee . Covariant Semi Functor from into (Opposite u ee)
	, forall ee . Wrapper into (Opposite (U_I_T_II t u) e ee)
	, forall ee . Wrapper into (U_I_T_II t u ee e)
	, forall ee . Wrapper into (Opposite u (t e) ee)
	) => Mapping Straight Straight from into (Opposite (U_I_T_II t u) e) (Opposite (U_I_T_II t u) e)
	where mapping = rwr / \from -> 
		wrap @into @(Opposite _ _ _)
		`compose` wrap @into @(U_I_T_II _ _ _ _)
		`compose` rw @into @(Opposite _ _ _)
		`compose` semifunctor @Straight @from @into from
		`compose` wrap @into @(Opposite _ _ _)
		`compose` rw @into @(U_I_T_II _ _ _ _)
		`compose` rw @into @(Opposite _ _ _)

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
	( forall e . Covariant Endo Semi Functor into (Straight u (t e))
	, forall e . Covariant Endo Semi Functor into (Opposite u (tt e))
	, Covariant Semi Functor from into tt
	, Covariant Semi Functor from into t
	, forall e . Wrapper into (U_T_I_TT_I u t tt e)
	, forall e ee . Wrapper into (Straight u (t e) (tt ee))
	, forall e ee . Wrapper into (Opposite u (tt e) (t ee))
	) => Mapping Straight Straight from into (U_T_I_TT_I u t tt) (U_T_I_TT_I u t tt)
	where mapping = rwr / \from -> rwr /
		wrapped @into (semifunctor @Straight @into @into @(Opposite u _) `compose` semifunctor @Straight @from @into / from) `compose`
		wrapped @into (semifunctor @Straight @into @into @(Straight u _) `compose` semifunctor @Straight @from @into / from)

instance
	( forall e . Covariant Endo Semi Functor (->) (Straight u e)
	, forall e . Covariant Endo Semi Functor (->) (Opposite u e)
	, Covariant Monoidal Functor from u u ttt
	, Component Natural from (->) (t `T'TT'I` ttt) (t `TT'T'I` ttt)
	, Component Natural from (->) (tt `T'TT'I` ttt) (tt `TT'T'I` ttt)
	, forall e . Wrapper from (U_T_I_TT_I u t tt e)
	, forall e . Wrapper (->) (TT'T'I (U_T_I_TT_I u t tt) ttt e)
	, forall e . Wrapper (->) (T'TT'I (U_T_I_TT_I u t tt) ttt e)
	) => Mapping Straight Straight from (->) (U_T_I_TT_I u t tt `T'TT'I` ttt) (U_T_I_TT_I u t tt `TT'T'I` ttt)
	where mapping = rwr / \from -> rwr /
		monoidal @Straight @from @ttt @u @u (wrap @_ @(U_T_I_TT_I u t tt _)) identity `compose`
			wrapped (semifunctor @Straight @(->) @(->) @(Opposite u _)
				(wrapped (map @Straight @Straight @from @(->) @(t `T'TT'I` ttt) @(t `TT'T'I` ttt) from))) `compose`
			wrapped (semifunctor @Straight @(->) @(->) @(Straight u _)
				(wrapped (map @Straight @Straight @from @(->) @(tt `T'TT'I` ttt) @(tt `TT'T'I` ttt) from))) `compose`
			rw @(->) @(U_T_I_TT_I u t tt _)

-- TODO: here should be a generalized version of an instance above
-- instance
	-- ( forall e . Covariant Endo Semi Functor into (Straight (u :: * -> * -> *) (t e))
	-- , forall e . Wrapper into (U_T_I_TT_I u t tt e)
	-- , forall e . Wrapper into (TT'T'I (U_T_I_TT_I u t tt) ttt e)
	-- , forall e . Wrapper into (T'TT'I (U_T_I_TT_I u t tt) ttt e)
	-- ) => Mapping Straight Straight from into (U_T_I_TT_I u t tt `T'TT'I` ttt) (U_T_I_TT_I u t tt `TT'T'I` ttt)
	-- where mapping = rwr / \from -> rwr /
		-- monoidal' @Straight @from @from @ttt @u @u (wrap @_ @(U_T_I_TT_I u t tt _)) identity `compose`
			-- wrapped (semifunctor @Straight @into @into @(Opposite u _)
				-- (wrapped (map @Straight @Straight @from @into @(t `T'TT'I` ttt) @(t `TT'T'I` ttt) from))) `compose`
			-- wrapped (semifunctor @Straight @into @into @(Straight u _)
				-- (wrapped (map @Straight @Straight @from @into @(tt `T'TT'I` ttt) @(tt `TT'T'I` ttt) from))) `compose`
			-- rw @into @(U_T_I_TT_I u t tt _)

instance Mapping Straight Straight (->) (->) (Straight LM e `T'TT'I` Straight (->) e) I
	where mapping = rwr / \from -> rwr / \(Straight (These e (Straight f))) -> from (f e)

instance Mapping Straight Straight (->) (->) I (Straight (->) e `T'TT'I` Straight LM e)
	where mapping = rwr / \from -> rwr / \x -> Straight / \e -> Straight (These e (from x))

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
	where mapping = rwr / \from -> rwr / \(Opposite (These x e)) ->
		yoneda @Straight @Functor x (Opposite `compose` (\x' -> These (from x') e))

instance
	( Covariant Semi Functor into into (Straight u e)
	, Covariant Semi Functor from into (Straight uu e)
	, forall ee . Wrapper into (Straight (W_I_I_II (U_I_UU_II_III u uu)) e ee)
	, forall ee . Wrapper into (W_I_I_II (U_I_UU_II_III u uu) e ee)
	, forall ee . Wrapper into (U_I_UU_II_III u uu e e ee)
	, forall ee . Wrapper into (Straight u e ee)
	, forall ee . Wrapper into (Straight uu e ee)
	) => Mapping Straight Straight from into
	(Straight (W_I_I_II (U_I_UU_II_III u uu)) e)
	(Straight (W_I_I_II (U_I_UU_II_III u uu)) e)
	where mapping = rwr / \from ->
		wrap @into @(Straight _ _ _)
		`compose` wrap @into @(W_I_I_II _ _ _)
		`compose` wrap @into @(U_I_UU_II_III _ _ _ _ _)
		`compose` rw @into @(Straight u _ _)
		`compose` semifunctor @Straight @into @into
			(rw @into @(Straight uu _ _)
			`compose` semifunctor @Straight @from @into from
			`compose` wrap @into @(Straight uu _ _))
		`compose` wrap @into @(Straight u _ _)
		`compose` rw @into @(U_I_UU_II_III _ _ _ _ _)
		`compose` rw @into @(W_I_I_II _ _ _)
		`compose` rw @into @(Straight _ _ _)

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
	(UU_V_U_I_II_T_II Opposite (W_I_II_II (U_I_UU_III_U_II_I (->) LM)) (->) (Opposite (W_I_I_II (U_I_UU_II_III (->) LM)) ee) e)
	(UU_V_U_I_II_T_II Opposite (W_I_II_II (U_I_UU_III_U_II_I (->) LM)) (->) (Opposite (W_I_I_II (U_I_UU_II_III (->) LM)) ee) e)

instance
	( forall e . Covariant Semi Functor from into (Straight (U_I_T_II t u) e)
	, forall e . Covariant Semi Functor from into (Opposite (U_I_T_II t u) e)
	, forall e . Covariant Endo Semi Functor from (Straight (U_I_T_II t u) e)
	, forall e . Covariant Endo Semi Functor from (Opposite (U_I_T_II t u) e)
	, forall e . Wrapper from (R_U_I_T_I u t e)
	, forall e . Wrapper into (R_U_I_T_I u t e)
	, forall e . Wrapper from (Recursive (U_I_T_II t u e))
	, forall e . Wrapper into (Recursive (U_I_T_II t u e))
	, forall e ee . Wrapper from (Opposite (U_I_T_II t u) e ee)
	, forall e ee . Wrapper into (Opposite (U_I_T_II t u) e ee)
	, forall e ee . Wrapper from (Straight (U_I_T_II t u) e ee)
	, forall e ee . Wrapper into (Straight (U_I_T_II t u) e ee)
	) => Mapping Straight Straight from into (R_U_I_T_I u t) (R_U_I_T_I u t)
	where mapping = rwr / \from ->
		wrap @into @(R_U_I_T_I u t _)
		`compose` wrap @into @(Recursive _)
		`compose` rw @into @(Opposite _ _ _)
		`compose` semifunctor @Straight from
		`compose` wrap @into @(Opposite _ _ _)
		`compose` rw @into @(Straight _ _ _)
		`compose` semifunctor @Straight
			(rw @from
			`compose` semifunctor @Straight @from from
			`compose` wrap @from @(R_U_I_T_I u t _))
		`compose` wrap @into @(Straight _ _ _)
		`compose` rw @into @(Recursive _)
		`compose` rw @into @(R_U_I_T_I u t _)

instance Mapping Straight Straight Arrow Arrow (Straight Arrow a) (Straight Arrow a)
	where mapping (Straight from) = Straight / \(Straight between) -> Straight (\x -> from (between x))

instance Mapping Opposite Straight Arrow Arrow (Opposite Arrow o) (Opposite Arrow o)
	where mapping (Opposite from) = Straight / \(Opposite between) -> Opposite (\x -> between (from x))

instance Category Arrow where
	identity = \x -> x

instance Mapping Straight Straight Arrow into t tt
	=> Mapping Constant Straight Arrow into t tt
	where mapping (U_1_I x) = mapping (Straight (\_ -> x Unit))

instance Mapping Straight Straight Arrow Arrow (U_1_I (->) e) (U_1_I (->) e)
	where mapping = rwr / \from (U_1_I x) -> U_1_I / \_ -> from / x Unit

instance Mapping Straight Straight Arrow Arrow I (Both LM)
	where mapping (Straight from) = Straight / \(I x) -> U_I_I (These (from x) (from x))

-- TODO: redefine using limits
instance Mapping Straight Straight Arrow Arrow (Both LM) (Both LM)
	where mapping (Straight from) = Straight / \(U_I_I (These x y)) -> U_I_I (These (from x) (from y))

instance Mapping Straight Straight Arrow Arrow (Straight LM e) I
	where mapping (Straight from) = Straight / \(Straight (These _ x)) -> I (from x)

instance Mapping Straight Straight Arrow Arrow (Opposite LM e) I
	where mapping (Straight from) = Straight / \(Opposite (These x _)) -> I (from x)

instance Mapping Straight Straight Arrow Arrow (Both ML) I
	where mapping (Straight from) = Straight / \case
		U_I_I (This x) -> I (from x)
		U_I_I (That x) -> I (from x)

instance Mapping Straight Straight Arrow Arrow I (Straight ML e)
	where mapping (Straight from) = Straight / \(I x) -> Straight (That (from x))

instance Mapping Straight Straight Arrow Arrow I (Opposite ML e)
	where mapping (Straight from) = Straight / \(I x) -> Opposite (This (from x))
 
instance Mapping Straight Straight (W_I_II_II (U_I_UU_III_U_II_I (->) LM)) Arrow
	(Straight (W_I_II_II (U_I_UU_III_U_II_I (->) LM)) origin)
	(Straight (W_I_II_II (U_I_UU_III_U_II_I (->) LM)) origin)
	where mapping = rwr / \into -> rwr `compose` rwr `compose` rwr / \from origin ->
		let These source source_origin = from origin in
		let These target target_source = (rw `compose` rw) into source in
		These target (source_origin `compose` target_source)

instance Mapping Opposite Straight (W_I_II_II (U_I_UU_III_U_II_I (->) LM)) Arrow
	(Opposite (W_I_II_II (U_I_UU_III_U_II_I (->) LM)) origin)
	(Opposite (W_I_II_II (U_I_UU_III_U_II_I (->) LM)) origin)
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
		\from (Opposite (These old e)) -> These 
			(I (wrapped (left @Straight @(->) identity) (from old)))
			(\(I new) -> Opposite (These ((wrapped (right @Straight @(->) identity) (from old)) new) e))

instance Mapping Straight Straight
	(W_I_II_II (U_I_UU_III_U_II_I (->) LM))
	(W_I_II_II (U_I_UU_III_U_II_I (->) LM))
	(That LM e) I
	where mapping = rwr `compose` rwr `compose` rwr /
		\from (Straight (These e old)) -> These 
			/ I (wrapped (left @Straight @(->) identity) (from old))
			/ \(I new) -> Straight (These e ((wrapped (right @Straight @(->) identity) (from old)) new))

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
		These (These (I e) (I ee)) (Straight f) -> from (f (These e ee))

instance Mapping Straight Straight (->) (->) (Straight (->) Unit) I
	where mapping = rwr / \from (Straight f) -> I (from (f Unit))

-- TODO: instance Mapping Straight Straight (->) (->) (Day Straight (->) LM ML I I e ee) I
-- TODO: instance Mapping Straight Straight (->) (->) (Straight (->) Void) I

instance Mapping Straight Straight (->) (->)
		(Day That (->) LM LM (This ML e) (This ML e) ee eee) (This ML e)
	where mapping = rwr / \from -> rwr / \case
		These (These (Opposite (This ee)) (Opposite (This eee))) (Straight f) -> This (from (f (These ee eee)))
		These (These (Opposite (That e)) _) _ -> That e

instance Mapping Straight Straight (->) (->) (That (->) Unit) (This ML e)
	where mapping = rwr / \from (Straight f) -> Opposite (This (from (f Unit)))

instance Mapping Straight Straight (->) (->)
		(Day That (->) LM LM (That ML e) (That ML e) ee eee) (That ML e)
	where mapping = rwr / \from -> rwr / \case
		These (These (Straight (That ee)) (Straight (That eee))) (Straight f) -> That (from (f (These ee eee)))
		These (These (Straight (This e)) _) (Straight _) -> This e
		These (These _ (Straight (This e))) (Straight _) -> This e

instance Mapping Straight Straight (->) (->) (That (->) Unit) (That ML e)
	where mapping = rwr / \from (Straight f) -> Straight (That (from (f Unit)))

instance Mapping Straight Straight (->) (->)
		(Day That (->) LM ML (That ML e) (That ML e) ee eee) (That ML e)
	where mapping = rwr / \from -> rwr / \case
		These (These (Straight (That ee)) _) (Straight f) -> That (from (f (This ee)))
		These (These _ (Straight (That eee))) (Straight f) -> That (from (f (That eee)))
		These (These _ (Straight (This eee))) (Straight _) -> This eee

instance Mapping Straight Straight (->) (->) (That (->) Void) (This ML Unit)
	where mapping = rwr / \_ _ -> Opposite (That Unit)

instance Mapping Straight Straight (->) (->)
		(Day That (->) LM ML (This ML e) (This ML e) ee eee) (This ML e)
	where mapping = rwr / \from -> rwr / \case
		These (These (Opposite (This ee)) _) (Straight f) -> This (from (f (This ee)))
		These (These _ (Opposite (This eee))) (Straight f) -> This (from (f (That eee)))
		These (These _ (Opposite (That eee))) _ -> That eee

instance Mapping Straight Straight (->) (->) (That (->) Void) (That ML Unit)
	where mapping = rwr / \_ _ -> Straight (This Unit)
