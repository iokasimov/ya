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
	where mapping = rewrap / \from -> rewrap from

instance
	( forall e . Wrapper into (I e)
	, forall e . Wrapper into (TT_T_I I g e)
	, forall e . Wrapper into (T_TT_I I g e)
	, Covariant Endo Semi Functor into g
	) => Mapping Straight Straight into into (T_TT_I I g) (TT_T_I I g)
	where mapping = rewrap / \from -> rewrap /
		semifunctor @Straight @into @into (wrap `compose` from) `compose` unwrap @into

instance
	( Covariant Semi Functor from into g
	, Covariant Endo Semi Functor into f
	, forall e . Wrapper into (T_TT_I f g e)
	) => Mapping Straight Straight from into (T_TT_I f g) (T_TT_I f g)
	where mapping = rewrap / \from -> wrap @into
		`compose` (semifunctor @Straight @into @into
			`compose` semifunctor @Straight @from @into
			) from
		`compose` unwrap @into

instance
	( Covariant Semi Functor from into f
	, Covariant Endo Semi Functor into g
	, forall e . Wrapper into (TT_T_I f g e)
	) => Mapping Straight Straight from into (TT_T_I f g) (TT_T_I f g)
	where mapping = rewrap / \from -> wrap @into
		`compose` (semifunctor @Straight @into @into
			`compose` semifunctor @Straight @from @into
			) from
		`compose` unwrap @into

instance
	( Covariant Semi Functor from into t
	, forall ee . Covariant Endo Semi Functor into (U_I_II u ee)
	, forall ee . Wrapper into (U_I_II (U_I_T_II t u) e ee)
	, forall ee . Wrapper into (U_I_T_II t u e ee)
	, forall ee . Wrapper into (U_I_II u e (t ee))
	) => Mapping Straight Straight from into (U_I_II (U_I_T_II t u) e) (U_I_II (U_I_T_II t u) e)
	where mapping = rewrap / \from ->
		wrap @into @(U_I_II _ _ _)
		`compose` wrap @into @(U_I_T_II _ _ _ _)
		`compose` unwrap @into @(U_I_II _ _ _)
		`compose` semifunctor @Straight @into @into (semifunctor @Straight @from @into from)
		`compose` wrap @into @(U_I_II _ _ _)
		`compose` unwrap @into @(U_I_T_II _ _ _ _)
		`compose` unwrap @into @(U_I_II _ _ _)

instance
	( forall ee . Covariant Semi Functor from into (U_II_I u ee)
	, forall ee . Wrapper into (U_II_I (U_I_T_II t u) e ee)
	, forall ee . Wrapper into (U_I_T_II t u ee e)
	, forall ee . Wrapper into (U_II_I u (t e) ee)
	) => Mapping Straight Straight from into (U_II_I (U_I_T_II t u) e) (U_II_I (U_I_T_II t u) e)
	where mapping = rewrap / \from -> 
		wrap @into @(U_II_I _ _ _)
		`compose` wrap @into @(U_I_T_II _ _ _ _)
		`compose` unwrap @into @(U_II_I _ _ _)
		`compose` semifunctor @Straight @from @into from
		`compose` wrap @into @(U_II_I _ _ _)
		`compose` unwrap @into @(U_I_T_II _ _ _ _)
		`compose` unwrap @into @(U_II_I _ _ _)

instance
	( Covariant Semi Functor from into h
	, Covariant Endo Semi Functor into g
	, Covariant Endo Semi Functor into f
	, forall e . Wrapper into (T_TT_TTT_I f g h e)
	) => Mapping Straight Straight from into (T_TT_TTT_I f g h) (T_TT_TTT_I f g h)
	where mapping = rewrap / \from -> wrap @into
		`compose` (semifunctor @Straight @into @into
			`compose` semifunctor @Straight @into @into
			`compose` semifunctor @Straight @from @into
			) from
		`compose` unwrap @into

instance Mapping Straight Straight Arrow Arrow (That (/\) e) (That (/\) e)
	where mapping = rewrap / \from -> rewrap / \case
		These e x -> These e (from x)

instance Mapping Straight Straight Arrow Arrow (This (/\) e) (This (/\) e)
	where mapping = rewrap / \from -> rewrap / \case
		These x e -> These (from x) e

instance Mapping Straight Straight Arrow Arrow (That (\/) e) (That (\/) e)
	where mapping = rewrap / \from -> rewrap / \case
		That x -> That (from x)
		This e -> This e

instance Mapping Straight Straight Arrow Arrow (This (\/) e) (This (\/) e)
	where mapping = rewrap / \from -> rewrap / \case
		This x -> This (from x)
		That e -> That e

instance
	( Covariant Semi Functor from Arrow t
	, Covariant Functor from from (U_I_I u)
	, Covariant Monoidal Functor from u u t
	, forall e . Castable Dual from (Both u e)
	) => Mapping Straight Straight from Arrow (U_I_I u `T_TT_I` t) (U_I_I u `TT_T_I` t)
	where mapping = rewrap / \from -> rewrap /
		monoidal @Straight @from @t @u @u
			(semifunctor @Straight from `compose` wrap @from @(Both _ _)) identity
		`compose` unwrap @Arrow @(U_I_I u _)

instance
	( Covariant Semi Functor Arrow Arrow t
	, Covariant Functor Arrow Arrow (U_I_I u)
	, Covariant Monoidal Functor Arrow u u tt
	, Mapping Straight Straight Arrow Arrow (T_TT_I t tt) (TT_T_I t tt)
	) => Mapping Straight Straight Arrow Arrow
		((U_I_I u `T_TT_I` t) `T_TT_I` tt)
		((U_I_I u `T_TT_I` t) `TT_T_I` tt)
	where mapping = rewrap / \from -> rewrap /
		semifunctor @Straight @Arrow @Arrow (wrap @Arrow @(T_TT_I (U_I_I u) t _)) `compose`
		wrapped (component @Straight @Arrow @Arrow @(T_TT_I (U_I_I u) tt) @(TT_T_I (U_I_I u) tt)) `compose`
		semifunctor @Straight @Arrow @Arrow @(U_I_I u)
			(wrapped / map @Straight @Straight @Arrow @Arrow @(T_TT_I t tt) @(TT_T_I t tt) from) `compose`
		unwrap @Arrow

instance Covariant Yoneda Functor Arrow Arrow g =>
	Mapping Straight Straight Arrow Arrow (This (/\) e `T_TT_I` g) (This (/\) e `TT_T_I` g)
	where mapping = rewrap / \from -> rewrap @Arrow @(T_TT_I _ _ _) @(TT_T_I _ _ _) /
		\(U_II_I (These x e)) -> yoneda @Straight @Functor x (U_II_I `compose` (\x' -> These (from x') e))
		
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
	where mapping = rewrap / \from ->
		wrap @into @(U_I_II _ _ _)
		`compose` wrap @into @(W_I_I_II _ _ _)
		`compose` wrap @into @(U_I_UU_II_III _ _ _ _ _)
		`compose` unwrap @into @(U_I_II u _ _)
		`compose` semifunctor @Straight @into @into
			(unwrap @into @(U_I_II uu _ _)
			`compose` semifunctor @Straight @from @into from
			`compose` wrap @into @(U_I_II uu _ _))
		`compose` wrap @into @(U_I_II u _ _)
		`compose` unwrap @into @(U_I_UU_II_III _ _ _ _ _)
		`compose` unwrap @into @(W_I_I_II _ _ _)
		`compose` unwrap @into @(U_I_II _ _ _)

instance Mapping Straight Straight Arrow Arrow
	(UU_V_U_I_II_T_II Straight Arrow Arrow f i)
	(UU_V_U_I_II_T_II Straight Arrow Arrow f i)
	where mapping = rewrap / \from -> rewrap (`compose` (rewrap (`compose` from)))

instance Mapping Straight Straight Arrow Arrow
	(UU_V_U_I_II_T_II Straight Constant Arrow f i)
	(UU_V_U_I_II_T_II Straight Constant Arrow f i)
	where mapping = rewrap / \_ -> rewrap (`compose` (rewrap (rewrap identity)))

instance Mapping Dual Straight Arrow Arrow
	(UU_V_U_I_II_T_II Dual Arrow Arrow f i)
	(UU_V_U_I_II_T_II Dual Arrow Arrow f i)
	where mapping = rewrap / \from -> rewrap (`compose` (rewrap (compose (from))))

-- TODO: implement `mapping` method
instance Mapping Dual Straight (W_I_II_II (U_I_UU_III_U_II_I (->) (/\))) (->)
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
	, forall e e' . Wrapper from (U_II_I (U_I_T_II t u) e e')
	, forall e e' . Wrapper into (U_II_I (U_I_T_II t u) e e')
	, forall e e' . Wrapper from (U_I_II (U_I_T_II t u) e e')
	, forall e e' . Wrapper into (U_I_II (U_I_T_II t u) e e')
	) => Mapping Straight Straight from into (R_U_I_T_I u t) (R_U_I_T_I u t)
	where mapping = rewrap / \from ->
		wrap @into @(R_U_I_T_I u t _)
		`compose` wrap @into @(Recursive _)
		`compose` unwrap @into @(U_II_I _ _ _)
		`compose` semifunctor @Straight from
		`compose` wrap @into @(U_II_I _ _ _)
		`compose` unwrap @into @(U_I_II _ _ _)
		`compose` semifunctor @Straight
			(unwrap @from
			`compose` semifunctor @Straight @from from
			`compose` wrap @from @(R_U_I_T_I u t _))
		`compose` wrap @into @(U_I_II _ _ _)
		`compose` unwrap @into @(Recursive _)
		`compose` unwrap @into @(R_U_I_T_I u t _)

instance Mapping Straight Straight Arrow Arrow (U_I_II Arrow s) (U_I_II Arrow s)
	where mapping (U_I_II from) = U_I_II / \(U_I_II between) -> U_I_II (\x -> from (between x))

instance Mapping Dual Straight Arrow Arrow (U_II_I Arrow t) (U_II_I Arrow t)
	where mapping (U_II_I from) = U_I_II / \(U_II_I between) -> U_II_I (\x -> between (from x))

instance Category Arrow where
	identity = \x -> x

instance Mapping Straight Straight Arrow into f g
	=> Mapping Constant' Straight Arrow into f g
	where mapping (U_1_I x) = mapping (U_I_II (\_ -> x Unit))

-- instance Mapping Straight Straight Arrow Arrow (U_I_II Constant s) (U_I_II Constant s)
-- 	where mapping = rewrap / \from (U_I_II (Constant x)) -> U_I_II (Constant (from x))

-- instance Mapping Dual Straight Arrow Arrow (U_II_I Constant t) (U_II_I Constant t)
-- 	where mapping = rewrap / \_ (U_II_I (Constant x)) -> U_II_I (Constant (x))

-- instance Mapping Straight Straight Arrow into f g => Mapping Straight Straight Constant into f g
-- 	where mapping (U_I_II (Constant x)) = mapping (U_I_II (\_ -> x))

-- instance Mapping Dual Straight Arrow into f g => Mapping Dual Straight Constant into f g
-- 	where mapping (U_II_I (Constant x)) = mapping (U_II_I (\_ -> x))

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
	where mapping = rewrap / \into -> rewrap `compose` rewrap `compose` rewrap / \from origin ->
		let These source source_origin = from origin in
		let These target target_source = (unwrap `compose` unwrap) into source in
		These / target / source_origin `compose` target_source 

instance Mapping Dual Straight (W_I_II_II (U_I_UU_III_U_II_I (->) (/\))) Arrow
	(U_II_I (W_I_II_II (U_I_UU_III_U_II_I (->) (/\))) origin)
	(U_II_I (W_I_II_II (U_I_UU_III_U_II_I (->) (/\))) origin)
	where mapping = rewrap / \from -> rewrap `compose` rewrap `compose` rewrap / \into origin ->
		let These source source_origin = (unwrap `compose` unwrap) from origin in
		let These target target_source = into source in
		These / target / source_origin `compose` target_source 

instance Category (W_I_II_II (U_I_UU_III_U_II_I (->) (/\))) where
	identity = W_I_II_II `compose` U_I_UU_III_U_II_I / \x -> These x identity

instance Mapping Straight Straight
	(W_I_II_II (U_I_UU_III_U_II_I (->) (/\)))
	(W_I_II_II (U_I_UU_III_U_II_I (->) (/\)))
	(This (/\) e) I
	where mapping = rewrap `compose` rewrap `compose` rewrap /
		\from (U_II_I (These old e)) -> These 
			(I (wrapped (this @Straight @(->) identity) / from old))
			(\(I new) -> U_II_I (These ((wrapped (that @Straight @(->) identity) / from old) new) e))

instance Mapping Straight Straight
	(W_I_II_II (U_I_UU_III_U_II_I (->) (/\)))
	(W_I_II_II (U_I_UU_III_U_II_I (->) (/\)))
	(That (/\) e) I
	where mapping = rewrap `compose` rewrap `compose` rewrap /
		\from (U_I_II (These e old)) -> These 
			/ I (wrapped (this @Straight @(->) identity) (from old))
			/ \(I new) -> U_I_II (These e ((wrapped (that @Straight @(->) identity) / from old) new))

instance Mapping Straight Straight (W_I_II_II (U_I_UU_III_U_II_I (->) (/\))) (->) I (Both (/\))
	where mapping = rewrap /
		\(W_I_II_II (U_I_UU_III_U_II_I from)) (I old) -> U_I_I (These
			/ (wrapped (this @Straight @(->) identity) (from old))
			/ (wrapped (this @Straight @(->) identity) (from old)))

instance Mapping Dual Straight (W_I_II_II (U_I_UU_III_U_II_I (->) (/\))) (->) (U_II_I (->) e) (U_II_I (->) e)
   where mapping = rewrap / \(W_I_II_II (U_I_UU_III_U_II_I from)) -> semifunctor @Dual / (\(These x _) -> x) `compose` from