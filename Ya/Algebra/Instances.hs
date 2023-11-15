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
	where mapping = rw rw

-- instance
-- 	( forall e . Wrapper into (I e)
-- 	, forall e . Wrapper into (TT_T_I I tt e)
-- 	, forall e . Wrapper into (T'TT'I I tt e)
-- 	, Covariant Endo Semi Functor into tt
-- 	) => Mapping Straight Straight into into (T'TT'I I tt) (TT_T_I I tt)
-- 	where mapping = rw / \from -> rw /
-- 		semifunctor @Straight @into @into (wrap `compose` from) `compose` uw @into

instance
	( Covariant Semi Functor from into tt
	, Covariant Endo Semi Functor into t
	, forall e . Wrapper into (T'TT'I t tt e)
	) => Mapping Straight Straight from into (T'TT'I t tt) (T'TT'I t tt)
	where mapping = rw / \from -> wrap @into
		`compose` (semifunctor @Straight @into @into
			`compose` semifunctor @Straight @from @into
			) from
		`compose` uw @into

instance
	( Covariant Semi Functor from into t
	, Covariant Endo Semi Functor into tt
	, forall e . Wrapper into (TT_T_I t tt e)
	) => Mapping Straight Straight from into (TT_T_I t tt) (TT_T_I t tt)
	where mapping = rw / \from -> wrap @into
		`compose` (semifunctor @Straight @into @into
			`compose` semifunctor @Straight @from @into
			) from
		`compose` uw @into

instance
	( Covariant Semi Functor from into t
	, forall ee . Covariant Endo Semi Functor into (U_I_II u ee)
	, forall ee . Wrapper into (U_I_II (U_I_T_II t u) e ee)
	, forall ee . Wrapper into (U_I_T_II t u e ee)
	, forall ee . Wrapper into (U_I_II u e (t ee))
	) => Mapping Straight Straight from into (U_I_II (U_I_T_II t u) e) (U_I_II (U_I_T_II t u) e)
	where mapping = rw / \from ->
		wrap @into @(U_I_II _ _ _)
		`compose` wrap @into @(U_I_T_II _ _ _ _)
		`compose` uw @into @(U_I_II _ _ _)
		`compose` semifunctor @Straight @into @into (semifunctor @Straight @from @into from)
		`compose` wrap @into @(U_I_II _ _ _)
		`compose` uw @into @(U_I_T_II _ _ _ _)
		`compose` uw @into @(U_I_II _ _ _)

instance
	( forall ee . Covariant Semi Functor from into (U_II_I u ee)
	, forall ee . Wrapper into (U_II_I (U_I_T_II t u) e ee)
	, forall ee . Wrapper into (U_I_T_II t u ee e)
	, forall ee . Wrapper into (U_II_I u (t e) ee)
	) => Mapping Straight Straight from into (U_II_I (U_I_T_II t u) e) (U_II_I (U_I_T_II t u) e)
	where mapping = rw / \from -> 
		wrap @into @(U_II_I _ _ _)
		`compose` wrap @into @(U_I_T_II _ _ _ _)
		`compose` uw @into @(U_II_I _ _ _)
		`compose` semifunctor @Straight @from @into from
		`compose` wrap @into @(U_II_I _ _ _)
		`compose` uw @into @(U_I_T_II _ _ _ _)
		`compose` uw @into @(U_II_I _ _ _)

instance
	( Covariant Semi Functor from into h
	, Covariant Endo Semi Functor into tt
	, Covariant Endo Semi Functor into t
	, forall e . Wrapper into (T_TT_TTT_I t tt h e)
	) => Mapping Straight Straight from into (T_TT_TTT_I t tt h) (T_TT_TTT_I t tt h)
	where mapping = rw / \from -> wrap @into
		`compose` (semifunctor @Straight @into @into
			`compose` semifunctor @Straight @into @into
			`compose` semifunctor @Straight @from @into
			) from
		`compose` uw @into

instance Mapping Straight Straight Arrow Arrow (That (/\) o) (That (/\) o)
	where mapping = rw / \from -> rw / \case
		These e x -> These e (from x)

instance Mapping Straight Straight Arrow Arrow (This (/\) o) (This (/\) o)
	where mapping = rw / \from -> rw / \case
		These x e -> These (from x) e

instance Mapping Straight Straight Arrow Arrow (That (\/) o) (That (\/) o)
	where mapping = rw / \from -> rw / \case
		That x -> That (from x)
		This e -> This e

instance Mapping Straight Straight Arrow Arrow (This (\/) o) (This (\/) o)
	where mapping = rw / \from -> rw / \case
		This x -> This (from x)
		That e -> That e

instance
	( Covariant Semi Functor from Arrow t
	, Covariant Functor from from (U_I_I u)
	, Covariant Monoidal Functor from u u t
	, forall e . Castable Opposite from (Both u e)
	) => Mapping Straight Straight from Arrow (U_I_I u `T'TT'I` t) (U_I_I u `TT_T_I` t)
	where mapping = rw / \from -> rw /
		monoidal @Straight @from @t @u @u
			(semifunctor @Straight from `compose` wrap @from @(Both _ _)) identity
		`compose` uw @Arrow @(U_I_I u _)

instance
	( Covariant Semi Functor Arrow Arrow t
	, Covariant Functor Arrow Arrow (U_I_I u)
	, Covariant Monoidal Functor Arrow u u tt
	, Mapping Straight Straight Arrow Arrow (T'TT'I t tt) (TT_T_I t tt)
	) => Mapping Straight Straight Arrow Arrow
		((U_I_I u `T'TT'I` t) `T'TT'I` tt)
		((U_I_I u `T'TT'I` t) `TT_T_I` tt)
	where mapping = rw / \from -> rw /
		semifunctor @Straight @Arrow @Arrow (wrap @Arrow @(T'TT'I (U_I_I u) t _)) `compose`
		wrapped (component @Straight @Arrow @Arrow @(T'TT'I (U_I_I u) tt) @(TT_T_I (U_I_I u) tt)) `compose`
		semifunctor @Straight @Arrow @Arrow @(U_I_I u)
			(wrapped / map @Straight @Straight @Arrow @Arrow @(T'TT'I t tt) @(TT_T_I t tt) from) `compose`
		uw @Arrow

instance Covariant Yoneda Functor Arrow Arrow tt =>
	Mapping Straight Straight Arrow Arrow (This (/\) e `T'TT'I` tt) (This (/\) e `TT_T_I` tt)
	where mapping = rw / \from -> rw / \(U_II_I (These x e)) ->
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
	where mapping = rw / \from ->
		wrap @into @(U_I_II _ _ _)
		`compose` wrap @into @(W_I_I_II _ _ _)
		`compose` wrap @into @(U_I_UU_II_III _ _ _ _ _)
		`compose` uw @into @(U_I_II u _ _)
		`compose` semifunctor @Straight @into @into
			(uw @into @(U_I_II uu _ _)
			`compose` semifunctor @Straight @from @into from
			`compose` wrap @into @(U_I_II uu _ _))
		`compose` wrap @into @(U_I_II u _ _)
		`compose` uw @into @(U_I_UU_II_III _ _ _ _ _)
		`compose` uw @into @(W_I_I_II _ _ _)
		`compose` uw @into @(U_I_II _ _ _)

instance Mapping Straight Straight Arrow Arrow
	(UU_V_U_I_II_T_II Straight Arrow Arrow t e)
	(UU_V_U_I_II_T_II Straight Arrow Arrow t e)
	where mapping = rw / \from -> rw (`compose` (rw (`compose` from)))

instance Mapping Opposite Straight Arrow Arrow
	(UU_V_U_I_II_T_II Opposite Arrow Arrow t e)
	(UU_V_U_I_II_T_II Opposite Arrow Arrow t e)
	where mapping = rw / \from -> rw (`compose` (rw (compose from)))

-- TODO: implement `mapping` method
instance Mapping Straight Straight (W_I_II_II (U_I_UU_III_U_II_I (->) (/\))) (->)
	(UU_V_U_I_II_T_II Straight (W_I_II_II (U_I_UU_III_U_II_I (->) (/\))) (->) (Straight (W_I_II_II (U_I_UU_III_U_II_I (->) (/\))) ee) e)
	(UU_V_U_I_II_T_II Straight (W_I_II_II (U_I_UU_III_U_II_I (->) (/\))) (->) (Straight (W_I_II_II (U_I_UU_III_U_II_I (->) (/\))) ee) e)

-- TODO: implement `mapping` method
instance Mapping Opposite Straight (W_I_II_II (U_I_UU_III_U_II_I (->) (/\))) (->)
	(UU_V_U_I_II_T_II U_II_I (W_I_II_II (U_I_UU_III_U_II_I (->) (/\))) (->) (U_II_I (W_I_I_II (U_I_UU_II_III (->) (/\))) ee) e)
	(UU_V_U_I_II_T_II U_II_I (W_I_II_II (U_I_UU_III_U_II_I (->) (/\))) (->) (U_II_I (W_I_I_II (U_I_UU_II_III (->) (/\))) ee) e)

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
	where mapping = rw / \from ->
		wrap @into @(R_U_I_T_I u t _)
		`compose` wrap @into @(Recursive _)
		`compose` uw @into @(U_II_I _ _ _)
		`compose` semifunctor @Straight from
		`compose` wrap @into @(U_II_I _ _ _)
		`compose` uw @into @(U_I_II _ _ _)
		`compose` semifunctor @Straight
			(uw @from
			`compose` semifunctor @Straight @from from
			`compose` wrap @from @(R_U_I_T_I u t _))
		`compose` wrap @into @(U_I_II _ _ _)
		`compose` uw @into @(Recursive _)
		`compose` uw @into @(R_U_I_T_I u t _)

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
	where mapping = rw / \from (U_1_I x) -> U_1_I / \_ -> from / x Unit

instance Mapping Straight Straight Arrow Arrow I (Both (/\))
	where mapping (U_I_II from) = U_I_II / \(I x) -> U_I_I (These (from x) (from x))

-- TODO: redefine using limits
instance Mapping Straight Straight Arrow Arrow (Both (/\)) (Both (/\))
	where mapping (U_I_II from) = U_I_II / \(U_I_I (These x y)) -> U_I_I (These (from x) (from y))

instance Mapping Straight Straight Arrow Arrow (U_I_II (/\) e) I
	where mapping (U_I_II from) = U_I_II / \(U_I_II (These _ x)) -> I (from x)

instance Mapping Straight Straight Arrow Arrow (U_II_I (/\) e) I
	where mapping (U_I_II from) = U_I_II / \(U_II_I (These x _)) -> I (from x)

instance Mapping Straight Straight Arrow Arrow (Both (\/)) I
	where mapping (U_I_II from) = U_I_II / \case
		U_I_I (This x) -> I (from x)
		U_I_I (That x) -> I (from x)

instance Mapping Straight Straight Arrow Arrow I (U_I_II (\/) e)
	where mapping (U_I_II from) = U_I_II / \(I x) -> U_I_II (That (from x))

instance Mapping Straight Straight Arrow Arrow I (U_II_I (\/) e)
	where mapping (U_I_II from) = U_I_II / \(I x) -> U_II_I (This (from x))
 
instance Mapping Straight Straight (W_I_II_II (U_I_UU_III_U_II_I (->) (/\))) Arrow
	(U_I_II (W_I_II_II (U_I_UU_III_U_II_I (->) (/\))) origin)
	(U_I_II (W_I_II_II (U_I_UU_III_U_II_I (->) (/\))) origin)
	where mapping = rw / \into -> rw `compose` rw `compose` rw / \from origin ->
		let These source source_origin = from origin in
		let These target target_source = (uw `compose` uw) into source in
		These target (source_origin `compose` target_source)

instance Mapping Opposite Straight (W_I_II_II (U_I_UU_III_U_II_I (->) (/\))) Arrow
	(U_II_I (W_I_II_II (U_I_UU_III_U_II_I (->) (/\))) origin)
	(U_II_I (W_I_II_II (U_I_UU_III_U_II_I (->) (/\))) origin)
	where mapping = rw / \from -> rw `compose` rw `compose` rw / \into origin ->
		let These source source_origin = (uw `compose` uw) from origin in
		let These target target_source = into source in
		These target (source_origin `compose` target_source)

instance Category (W_I_II_II (U_I_UU_III_U_II_I (->) (/\))) where
	identity = W_I_II_II `compose` U_I_UU_III_U_II_I / \x -> These x identity

instance Mapping Straight Straight
	(W_I_II_II (U_I_UU_III_U_II_I (->) (/\)))
	(W_I_II_II (U_I_UU_III_U_II_I (->) (/\)))
	(This (/\) e) I
	where mapping = rw `compose` rw `compose` rw /
		\from (U_II_I (These old e)) -> These 
			(I (wrapped (this @Straight @(->) identity) (from old)))
			(\(I new) -> U_II_I (These ((wrapped (that @Straight @(->) identity) (from old)) new) e))

instance Mapping Straight Straight
	(W_I_II_II (U_I_UU_III_U_II_I (->) (/\)))
	(W_I_II_II (U_I_UU_III_U_II_I (->) (/\)))
	(That (/\) e) I
	where mapping = rw `compose` rw `compose` rw /
		\from (U_I_II (These e old)) -> These 
			/ I (wrapped (this @Straight @(->) identity) (from old))
			/ \(I new) -> U_I_II (These e ((wrapped (that @Straight @(->) identity) (from old)) new))

instance Mapping Straight Straight (W_I_II_II (U_I_UU_III_U_II_I (->) (/\))) (->) I (Both (/\))
	where mapping = rw /
		\(W_I_II_II (U_I_UU_III_U_II_I from)) (I old) -> U_I_I (These
			/ (wrapped (this @Straight @(->) identity) (from old))
			/ (wrapped (this @Straight @(->) identity) (from old)))

instance Mapping Opposite Straight (W_I_II_II (U_I_UU_III_U_II_I (->) (/\))) (->) (U_II_I (->) e) (U_II_I (->) e)
   where mapping = rw / \(W_I_II_II (U_I_UU_III_U_II_I from)) -> semifunctor @Opposite / (\(These x _) -> x) `compose` from