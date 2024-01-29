{-# OPTIONS_GHC -fno-warn-orphans #-}
{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE UndecidableInstances #-}
module Ya.Algebra.Instances where

import Ya.Algebra.Abstract
import Ya.Algebra.Definition

instance (Precategory into, forall e . Wrapper into (Identity e)) 
	=> Mapping Straight Straight into into Identity Identity
	where mapping = rwr rwr

instance
	( forall e . Wrapper into (Identity e)
	, forall e . Wrapper into (TT_T_I Identity t e)
	, forall e . Wrapper into (T_TT_I Identity t e)
	, Covariant Endo Semi Functor into t
	) => Mapping Straight Straight into into (T_TT_I Identity t) (TT_T_I Identity t)
	where mapping = rwr / \from -> rwr /
		map @Straight @Straight @into @into (wr `compose` from) `compose` rw @into

instance
	( Covariant Semi Functor from into tt
	, Covariant Endo Semi Functor into t
	, forall e . Wrapper into (T_TT_I t tt e)
	) => Mapping Straight Straight from into (T_TT_I t tt) (T_TT_I t tt)
	where mapping = rwr / \from -> wr @into
		`compose` (map @Straight @Straight @into @into
			`compose` map @Straight @Straight @from @into
			) from
		`compose` rw @into

instance
	( Covariant Semi Functor from into t
	, Covariant Endo Semi Functor into tt
	, forall e . Wrapper into (TT_T_I t tt e)
	) => Mapping Straight Straight from into (TT_T_I t tt) (TT_T_I t tt)
	where mapping = rwr / \from -> wr @into
		`compose` (map @Straight @Straight @into @into
			`compose` map @Straight @Straight @from @into
			) from
		`compose` rw @into

instance
	( Covariant Semi Functor from into t
	, forall e . Wrapper into (T_'_I l t e)
	) => Mapping Straight Straight from into (T_'_I l t) (T_'_I l t)
	where mapping = rwr / \from -> wr @into @(T_'_I _ t _)
		`compose` map @Straight @Straight @from @into @t from
		`compose` rw @into @(T_'_I _ t _)

instance
	( Covariant Semi Functor from into t
	, forall ee . Covariant Endo Semi Functor into (Straight u ee)
	, forall ee . Wrapper into (Straight (U_I_T_II t u) e ee)
	, forall ee . Wrapper into (U_I_T_II t u e ee)
	, forall ee . Wrapper into (Straight u e (t ee))
	) => Mapping Straight Straight from into (Straight (U_I_T_II t u) e) (Straight (U_I_T_II t u) e)
	where mapping = rwr / \from ->
		wr @into @(Straight _ _ _)
		`compose` wr @into @(U_I_T_II _ _ _ _)
		`compose` rw @into @(Straight _ _ _)
		`compose` map @Straight @Straight @into @into (map @Straight @Straight @from @into from)
		`compose` wr @into @(Straight _ _ _)
		`compose` rw @into @(U_I_T_II _ _ _ _)
		`compose` rw @into @(Straight _ _ _)

instance
	( forall ee . Covariant Semi Functor from into (Opposite u ee)
	, forall ee . Wrapper into (Opposite (U_I_T_II t u) e ee)
	, forall ee . Wrapper into (U_I_T_II t u ee e)
	, forall ee . Wrapper into (Opposite u (t e) ee)
	) => Mapping Straight Straight from into (Opposite (U_I_T_II t u) e) (Opposite (U_I_T_II t u) e)
	where mapping = rwr / \from -> 
		wr @into @(Opposite _ _ _)
		`compose` wr @into @(U_I_T_II _ _ _ _)
		`compose` rw @into @(Opposite _ _ _)
		`compose` map @Straight @Straight @from @into from
		`compose` wr @into @(Opposite _ _ _)
		`compose` rw @into @(U_I_T_II _ _ _ _)
		`compose` rw @into @(Opposite _ _ _)

instance
	( Covariant Semi Functor from into h
	, Covariant Endo Semi Functor into tt
	, Covariant Endo Semi Functor into t
	, forall e . Wrapper into (T_TTT_TT_I t h tt e)
	) => Mapping Straight Straight from into (T_TTT_TT_I t h tt) (T_TTT_TT_I t h tt)
	where mapping = rwr / \from -> wr @into
		`compose` (map @Straight @Straight @into @into
			`compose` map @Straight @Straight @into @into
			`compose` map @Straight @Straight @from @into
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
		i_ (map @Straight @Straight @into @into `compose` map @Straight @Straight @from @into @t @t / from) `compose`
		_i (map @Straight @Straight @into @into `compose` map @Straight @Straight @from @into @tt @tt / from)

instance
	( forall e . Covariant Endo Semi Functor (->) (Straight u e)
	, forall e . Covariant Endo Semi Functor (->) (Opposite u e)
	, Covariant Monoidal Functor from u u ttt
	, Component Natural from (->) (t `T_TT_I` ttt) (t `TT_T_I` ttt)
	, Component Natural from (->) (tt `T_TT_I` ttt) (tt `TT_T_I` ttt)
	, forall e . Wrapper from (U_T_I_TT_I u t tt e)
	, forall e . Wrapper (->) (TT_T_I (U_T_I_TT_I u t tt) ttt e)
	, forall e . Wrapper (->) (T_TT_I (U_T_I_TT_I u t tt) ttt e)
	) => Mapping Straight Straight from (->) (U_T_I_TT_I u t tt `T_TT_I` ttt) (U_T_I_TT_I u t tt `TT_T_I` ttt)
	where mapping = rwr / \from -> rwr /
		day @Straight @from @ttt @u @u (wr @_ @(U_T_I_TT_I u t tt _)) identity `compose`
			i_ (map @Straight @Straight @(->) @(->)
				(wrapped (map @Straight @Straight @from @(->) @(t `T_TT_I` ttt) @(t `TT_T_I` ttt) from))) `compose`
			_i (map @Straight @Straight @(->) @(->)
				(wrapped (map @Straight @Straight @from @(->) @(tt `T_TT_I` ttt) @(tt `TT_T_I` ttt) from))) `compose`
			rw @(->) @(U_T_I_TT_I u t tt _)

-- TODO: here should be a generalized version of an instance above
-- instance
	-- ( forall e . Covariant Endo Semi Functor into (Straight (u :: * -> * -> *) (t e))
	-- , forall e . Wrapper into (U_T_I_TT_I u t tt e)
	-- , forall e . Wrapper into (TT_T_I (U_T_I_TT_I u t tt) ttt e)
	-- , forall e . Wrapper into (T_TT_I (U_T_I_TT_I u t tt) ttt e)
	-- ) => Mapping Straight Straight from into (U_T_I_TT_I u t tt `T_TT_I` ttt) (U_T_I_TT_I u t tt `TT_T_I` ttt)
	-- where mapping = rwr / \from -> rwr /
		-- day_ @Straight @from @from @ttt @u @u (wrap @_ @(U_T_I_TT_I u t tt _)) identity `compose`
			-- wrapped (map @Straight @into @into @(Opposite u _)
				-- (wrapped (map @Straight @Straight @from @into @(t `T_TT_I` ttt) @(t `TT_T_I` ttt) from))) `compose`
			-- wrapped (map @Straight @into @into @(Straight u _)
				-- (wrapped (map @Straight @Straight @from @into @(tt `T_TT_I` ttt) @(tt `TT_T_I` ttt) from))) `compose`
			-- rw @into @(U_T_I_TT_I u t tt _)

instance Mapping Straight Straight (->) (->) (Straight LM e `T_TT_I` Straight (->) e) Identity
	where mapping = rwr / \from -> rwr / \(Straight (These e (Straight f))) -> from (f e)

instance Mapping Straight Straight (->) (->) Identity (Straight (->) e `T_TT_I` Straight LM e)
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
	) => Mapping Straight Straight from Arrow (U_I_I u `T_TT_I` t) (U_I_I u `TT_T_I` t)
	where mapping = rwr / \from -> rwr /
		day @Straight @from @t @u @u
			(map @Straight @Straight from `compose` wr @from @(Both _ _)) identity
		`compose` rw @Arrow @(U_I_I u _)

instance
	( Covariant Semi Functor Arrow Arrow t
	, Covariant Functor Arrow Arrow (U_I_I u)
	, Covariant Monoidal Functor Arrow u u tt
	, Mapping Straight Straight Arrow Arrow (T_TT_I t tt) (TT_T_I t tt)
	) => Mapping Straight Straight Arrow Arrow
		((U_I_I u `T_TT_I` t) `T_TT_I` tt)
		((U_I_I u `T_TT_I` t) `TT_T_I` tt)
	where mapping = rwr / \from -> rwr /
		map @Straight @Straight @Arrow @Arrow (wrap @(T_TT_I (U_I_I u) t _)) `compose`
		wrapped (component @Straight @Arrow @Arrow @(T_TT_I (U_I_I u) tt) @(TT_T_I (U_I_I u) tt)) `compose`
		map @Straight @Straight @Arrow @Arrow @(U_I_I u)
			(wrapped / map @Straight @Straight @Arrow @Arrow @(T_TT_I t tt) @(TT_T_I t tt) from) `compose`
		rw @Arrow

instance Covariant Yoneda Arrow Arrow tt =>
	Mapping Straight Straight Arrow Arrow (This LM e `T_TT_I` tt) (This LM e `TT_T_I` tt)
	where mapping = rwr / \from -> rwr / \(U_II_I (These x e)) ->
		yoneda @Straight x (U_II_I `compose` (\x_ -> These (from x_) e))

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
	where mapping = rwr / \from -> rwr `compose` rwr `compose` rwr /
		_i (map @Straight @Straight @into @into (_i (map @Straight @Straight @from @into from)))

-- TODO: generalize as an instance above
instance Mapping Straight Straight (->) (->)
	(Straight (W_I_II_I (U_I_UU_II_III (->) LM)) e)
	(Straight (W_I_II_I (U_I_UU_II_III (->) LM)) e)
	where mapping = rwr / \from -> rwr `compose` rwr `compose` rwr / \f x ->
		i_ (map @Straight @Straight from) (f x)

-- TODO: I need to test it, not sure it's correct
instance Mapping Straight Straight
	(W_I_II_I (U_I_UU_II_III (->) LM)) (->)
	(Straight (W_I_II_I (U_I_UU_II_III (->) LM)) e)
	(Straight (W_I_II_I (U_I_UU_II_III (->) LM)) e)
	where mapping = rwr / \(W_I_II_I (U_I_UU_II_III from))
		-> rwr `compose` rwr `compose` rwr / \trstn e ->
			let These old e' = trstn e in
			let These new _ = from old in
			These new e'

-- TODO: I need to test it, not sure it's correct
instance Mapping Opposite Straight
	(W_I_II_I (U_I_UU_II_III (->) LM)) (->)
	(Opposite (W_I_II_I (U_I_UU_II_III (->) LM)) e)
	(Opposite (W_I_II_I (U_I_UU_II_III (->) LM)) e)
	where mapping = rwr / \(W_I_II_I (U_I_UU_II_III from))
		-> rwr `compose` rwr `compose` rwr / \trstn new ->
			let These old new' = from new in
			let These e old' = trstn old in
			These e new'

instance Category (W_I_II_I (U_I_UU_II_III (->) LM))
	where identity = W_I_II_I (U_I_UU_II_III (\e -> These e e))

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
		wr @into @(R_U_I_T_I u t _)
		`compose` wr @into @(Recursive _)
		`compose` rw @into @(Opposite _ _ _)
		`compose` map @Straight @Straight @_ @_ from
		`compose` wr @into @(Opposite _ _ _)
		`compose` rw @into @(Straight _ _ _)
		`compose` map @Straight @Straight @from @into @(U_I_II (U_I_T_II t u) _) @(U_I_II (U_I_T_II t u) _)
			(rw @from
			`compose` map @Straight @Straight @from @_ @(R_U_I_T_I u t) @(R_U_I_T_I u t) from
			`compose` wr @from @(R_U_I_T_I u t _))
		`compose` wr @into @(Straight _ _ _)
		`compose` rw @into @(Recursive _)
		`compose` rw @into @(R_U_I_T_I u t _)

instance Mapping Straight Straight Arrow Arrow (Straight Arrow a) (Straight Arrow a)
	where mapping (Straight from) = Straight / \(Straight between) -> Straight (\x -> from (between x))

instance Mapping Opposite Straight Arrow Arrow (Opposite Arrow o) (Opposite Arrow o)
	where mapping (U_II_I from) = Straight / \(U_II_I between) -> U_II_I (\x -> between (from x))

instance Category Arrow where
	identity = \x -> x

instance Mapping Straight Straight Arrow into t tt
	=> Mapping Constant Straight Arrow into t tt
	where mapping (U_1_I x) = mapping (Straight (\_ -> x ()))

instance Mapping Straight Straight Arrow Arrow (U_1_I (->) e) (U_1_I (->) e)
	where mapping = rwr / \from (U_1_I x) -> U_1_I / \_ -> from / x ()

instance Mapping Straight Straight Arrow Arrow Identity (Both LM)
	where mapping (Straight from) = Straight / \(Identity x) -> U_I_I (These (from x) (from x))

-- TODO: redefine using limits
instance Mapping Straight Straight Arrow Arrow (Both LM) (Both LM)
	where mapping (Straight from) = Straight / \(U_I_I (These x y)) -> U_I_I (These (from x) (from y))

instance Mapping Straight Straight Arrow Arrow (Straight LM e) Identity
	where mapping (Straight from) = Straight / \(Straight (These _ x)) -> Identity (from x)

instance Mapping Straight Straight Arrow Arrow (Opposite LM e) Identity
	where mapping (Straight from) = Straight / \(U_II_I (These x _)) -> Identity (from x)

instance Mapping Straight Straight Arrow Arrow (Both ML) Identity
	where mapping (Straight from) = Straight / \case
		U_I_I (This x) -> Identity (from x)
		U_I_I (That x) -> Identity (from x)

instance Mapping Straight Straight Arrow Arrow Identity (Straight ML e)
	where mapping (Straight from) = Straight / \(Identity x) -> Straight (That (from x))

instance Mapping Straight Straight Arrow Arrow Identity (Opposite ML e)
	where mapping (Straight from) = Straight / \(Identity x) -> U_II_I (This (from x))
 
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
	(This LM e) Identity
	where mapping = rwr `compose` rwr `compose` rwr /
		\from (U_II_I (These old e)) -> These 
			(Identity (wrapped (left @Straight @(->) identity) (from old)))
			(\(Identity new) -> U_II_I (These ((wrapped (right @Straight @(->) identity) (from old)) new) e))

instance Mapping Straight Straight
	(W_I_II_II (U_I_UU_III_U_II_I (->) LM))
	(W_I_II_II (U_I_UU_III_U_II_I (->) LM))
	(That LM e) Identity
	where mapping = rwr `compose` rwr `compose` rwr /
		\from (Straight (These e old)) -> These 
			/ Identity (wrapped (left @Straight @(->) identity) (from old))
			/ \(Identity new) -> Straight (These e ((wrapped (right @Straight @(->) identity) (from old)) new))

instance Mapping Straight Straight (W_I_II_II (U_I_UU_III_U_II_I (->) LM)) (->) Identity (Both LM)
	where mapping = rwr / \(W_I_II_II (U_I_UU_III_U_II_I from)) (Identity old) -> U_I_I / These
		(wrapped (left @Straight @(->) identity) (from old))
		(wrapped (left @Straight @(->) identity) (from old))

instance Mapping Opposite Straight (W_I_II_II (U_I_UU_III_U_II_I (->) LM)) (->) (This (->) e) (This (->) e)
	where mapping = rwr / \(W_I_II_II (U_I_UU_III_U_II_I from)) ->
		map @Opposite @Straight / (\(These x _) -> x) `compose` from

instance Mapping Straight Straight (->) (->)
		(Day Straight (->) LM LM Identity Identity e ee) Identity
	where mapping = rwr / \from -> rwr / \case
		These (These (Identity e) (Identity ee)) (Straight f) -> from (f (These e ee))

instance Mapping Straight Straight (->) (->) (Straight (->) ()) Identity
	where mapping = rwr / \from (Straight f) -> Identity (from (f ()))

instance Mapping Straight Straight (->) (->)
		(Day Straight (->) LM LM (This ML e) (This ML e) ee eee) (This ML e)
	where mapping = rwr / \from -> rwr / \case
		These (These (U_II_I (This ee)) (U_II_I (This eee))) (Straight f) -> This (from (f (These ee eee)))
		These (These (U_II_I (That e)) _) _ -> That e

instance Mapping Straight Straight (->) (->) (Straight (->) ()) (This ML e)
	where mapping = rwr / \from (Straight f) -> U_II_I (This (from (f ())))

instance Mapping Straight Straight (->) (->)
		(Day Straight (->) LM LM (Straight ML e) (Straight ML e) ee eee) (Straight ML e)
	where mapping = rwr / \from -> rwr / \case
		These (These (Straight (That ee)) (Straight (That eee))) (Straight f) -> That (from (f (These ee eee)))
		These (These (Straight (This e)) _) (Straight _) -> This e
		These (These _ (Straight (This e))) (Straight _) -> This e

instance Mapping Straight Straight (->) (->)
		(Day Straight (->) LM MLM (Straight ML e) (Straight ML e) ee eee) (Straight ML e)
	where mapping = rwr / \from -> rwr / \case
		These (These (Straight (That ee)) (Straight (That eee))) (Straight f) ->
			That `compose` from `compose` f `compose` U_U_I_II_UU_I_II `compose` That / These ee eee
		These (These (Straight (That ee)) _) (Straight f) ->
			That `compose` from `compose` f `compose` U_U_I_II_UU_I_II `compose` This / This ee
		These (These (Straight (This _)) (Straight (That eee))) (Straight f) ->
			That `compose` from `compose` f `compose` U_U_I_II_UU_I_II `compose` This / That eee
		These (These (Straight (This e)) (Straight (This _))) (Straight _) ->
			This e

instance Mapping Straight Straight (->) (->) (Straight (->) ()) (Straight ML e)
	where mapping = rwr / \from (Straight f) -> Straight (That (from (f ())))

instance Mapping Straight Straight (->) (->)
		(Day Straight (->) LM ML (Straight ML e) (Straight ML e) ee eee) (Straight ML e)
	where mapping = rwr / \from -> rwr / \case
		These (These (Straight (That ee)) _) (Straight f) -> That (from (f (This ee)))
		These (These _ (Straight (That eee))) (Straight f) -> That (from (f (That eee)))
		These (These _ (Straight (This eee))) (Straight _) -> This eee

instance Mapping Straight Straight (->) (->) (Straight (->) Void) (This ML ())
	where mapping = rwr / \_ _ -> U_II_I (That ())

instance Mapping Straight Straight (->) (->)
		(Day Straight (->) LM ML (This ML e) (This ML e) ee eee) (This ML e)
	where mapping = rwr / \from -> rwr / \case
		These (These (U_II_I (This ee)) _) (Straight f) -> This (from (f (This ee)))
		These (These _ (U_II_I (This eee))) (Straight f) -> This (from (f (That eee)))
		These (These _ (U_II_I (That eee))) _ -> That eee

instance Mapping Straight Straight (->) (->) (That (->) Void) (That ML ())
	where mapping = rwr / \_ _ -> Straight (This ())

instance Mapping Straight Straight (->) (->) (U_I_II (->) (ML () ())) (U_I_I LM)
	where mapping = rwr / \from -> rwr / \f -> These
		(from `compose` f / This ())
		(from `compose` f / That ())

instance Mapping Straight Straight (->) (->) (U_I_I LM) (U_I_II (->) (ML () ()))
	where mapping = rwr / \from -> rwr / \(These x y) -> \case
		This () -> from x
		That () -> from y

instance Mapping Straight Straight
	(W_I_II_II (U_I_UU_III_U_II_I (->) LM))
	(W_I_II_II (U_I_UU_III_U_II_I (->) LM))
	(U_I_I LM) (U_I_II (->) (ML () ()))
	where mapping = rwr `compose` rwr `compose` rwr / \from (U_I_I (These x y)) -> These
		/ U_I_II (\case { This () -> this (from x); That () -> this (from y) })
		/ \(U_I_II f) -> U_I_I (These
			/ that (from x) (f (This ()))
			/ that (from x) (f (That ()))
			)

instance Mapping Straight Straight
	(W_I_II_II (U_I_UU_III_U_II_I (->) LM))
	(W_I_II_II (U_I_UU_III_U_II_I (->) LM))
	(U_I_II (->) (ML () ())) (U_I_I LM)
	where mapping = rwr `compose` rwr `compose` rwr / \from (U_I_II f) -> These
		/ U_I_I (These / this (from (f (This ()))) / this (from (f (That ()))))
		/ \(U_I_I (These x y)) -> U_I_II / \case
			This () -> that (from (f (This ()))) x
			That () -> that (from (f (That ()))) y

-- TODO: implement
instance Mapping Straight Straight (->) (->)
		(Day That (->) LM ML (U_I_I LM `T_TT_I` t) (U_I_I LM `T_TT_I` t) ee eee) (U_I_I LM `T_TT_I` t)

instance Monoidal Straight Functor (->) LM ML t
	=> Mapping Straight Straight (->) (->) (U_I_II (->) Void) (U_I_I LM `T_TT_I` t)
	where mapping = rwr / \_ _ -> T_TT_I `compose` U_I_I / These
		(map @Straight @Straight @(->) @(->) @t @t absurd empty)
		(map @Straight @Straight @(->) @(->) @t @t absurd empty)

-- instance Mapping Straight Straight
	-- (W_I_II_II (U_I_UU_III_U_II_I (->) LM))
	-- (W_I_II_II (U_I_UU_III_U_II_I (->) LM))
	-- (U_I_I LM) (U_I_I LM)

-- instance Mapping Straight Straight (->)
	-- (W_I_II_II (U_I_UU_III_U_II_I (->) LM))
	-- (U_I_II (->) (ML () ())) (U_I_I LM)

-- instance Mapping Straight Straight (->)
	-- (W_I_II_II (U_I_UU_III_U_II_I (->) LM))
	-- (U_I_I LM) (U_I_II (->) (ML () ()))

-- instance Mapping Straight Straight
	-- (W_I_II_II (U_I_UU_III_U_II_I (->) LM))
	-- (->)
	-- (U_I_II (->) (ML () ()))
	-- (U_I_II (->) (ML () ()))

instance Covariant Endo Semi Functor (->) unknown =>
	Unjointable (U_I_II (W_I_I_II (U_I_UU_II_III (->) LM)) state) unknown where
	unjoint (T_TTT_TT_I x) = \e -> map @Straight @Straight @(->) @(->) unwrap / unwrap x e
