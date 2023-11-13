{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE UndecidableInstances #-}
module Ya.Algebra.Abstract where

infixl 0 /
infixr 8 /\, \/

type (/) t i = t i

data (/\) i ii = These i ii

data (\/) i ii = This i | That ii

newtype I i = I i

newtype Recursive f = Recursive (f (Recursive f))

newtype T_TT_I t tt i = T_TT_I (t (tt i))

newtype TT_T_I t tt i = TT_T_I (tt (t i))

newtype T_TT_TTT_I t tt ttt i = T_TT_TTT_I (t (tt (ttt i)))

data U_ u i ii

newtype U_I_I u i = U_I_I (u i i)

newtype U_I_II u i ii = U_I_II (u i ii)

newtype U_II_I u i ii = U_II_I (u ii i)

newtype U_1_I u _' i = U_1_I (u Unit i)

newtype U_I_1 u i _' = U_I_1 (u i Unit)

newtype U_I_T_II t u i ii = U_I_T_II (u i (t ii))

newtype U_T_I_II t u i ii = U_T_I_II (u (t i) ii)

newtype U_T_I_TT_I u t tt i = U_T_I_TT_I (u (t i) (tt i))

newtype U_I_UU_II_III u uu i ii iii = U_I_UU_II_III (u i (uu ii iii))

newtype U_UU_UUU_V_III_I_II_UUUU u uu uuu uuuu v i ii x = U_UU_UUU_V_III_I_II_UUUU
	(u (uu (v uuu x i) (v uuu x ii)) (v uuu x (uuuu i ii)))

newtype U_V_UU_UUU_UUUU_T_TT_I_II_III u v uu uuu uuuu t tt i ii iii =
	U_V_UU_UUU_UUUU_T_TT_I_II_III (u (uuu (t i) (tt ii)) (v uu (uuuu i ii) iii))

newtype UU_V_U_I_II_T_II v u uu t i ii =
	UU_V_U_I_II_T_II (uu (v u ii i) (t i))

newtype R_U_I_T_I u t i = R_U_I_T_I (Recursive (U_I_T_II t u i))

newtype U_I_UU_III_U_II_I u uu i ii iii =
	U_I_UU_III_U_II_I (u i (uu iii (u ii i)))

newtype W_I_II_II w i ii = W_I_II_II (w i ii ii)

newtype W_I_I_II w i ii = W_I_I_II (w i i ii)

newtype UU_U_I_II_U_II_I u uu i ii
	= UU_U_I_II_U_II_I (uu (u i ii) (u ii i))

newtype UU_V_U_III_I_V_U_III_II v u uu i ii iii
	= UU_V_U_III_I_V_U_III_II
		(uu iii (uu (v u iii i) (v u iii ii)))

type Diagram = U_

type Arrow = (->)

type Both = U_I_I

-- Rename to Straight?
type Straight = U_I_II

-- Rename to Opposite?
type Opposite = U_II_I

type This = U_II_I

type That = U_I_II

type Constant = U_1_I

type family Flip v where
	Flip Straight = Opposite
	Flip Opposite = Straight

type family Supertype e where
	Supertype (I i) = i
	Supertype (Recursive f) = f (Recursive f)
	Supertype (T_TT_I t tt i) = t (tt i)
	Supertype (TT_T_I t tt i) = tt (t i)
	Supertype (T_TT_TTT_I t tt ttt i) = t (tt (ttt i))
	Supertype (U_I_I u i) = u i i
	Supertype (U_1_I u _ i) = u Unit i
	Supertype (U_I_1 u i _) = u i Unit
	Supertype (U_I_II u i ii) = u i ii
	Supertype (U_II_I u ii i) = u i ii
	Supertype (U_I_T_II t u i ii) = u i (t ii)
	Supertype (U_T_I_II t u i ii) = u (t i) ii
	Supertype (U_T_I_TT_I u t tt i) = u (t i) (tt i)
	Supertype (U_I_UU_II_III u uu i ii iii) = u i (uu ii iii)
	Supertype (U_UU_UUU_V_III_I_II_UUUU u uu uuu uuuu v i ii iii) = 
		u (uu (v uuu iii i) (v uuu iii ii)) (v uuu iii (uuuu i ii))
	Supertype (U_V_UU_UUU_UUUU_T_TT_I_II_III u v uu uuu uuuu t tt i ii iii) =
		u (uuu (t i) (tt ii)) (v uu (uuuu i ii) iii)
	Supertype (UU_V_U_I_II_T_II v u uu t i ii) = uu (v u ii i) (t i)
	Supertype (R_U_I_T_I u t i) = Recursive (U_I_T_II t u i)
	Supertype (U_I_UU_III_U_II_I u uu i ii iii) = u i (uu iii (u ii i))
	Supertype (W_I_II_II w i ii) = w i ii ii
	Supertype (W_I_I_II w i ii) = w i i ii
	Supertype (Arrow Unit ii) = ii

class Castable direction morphism e where
	cast :: direction morphism e (Supertype e)

class (Castable Opposite to f, Castable Straight to f) => Wrapper to f where
deriving instance (Castable Opposite to f, Castable Straight to f) => Wrapper to f

instance Castable Straight Arrow (I i)
	where cast = U_I_II (\(I x) -> x)

instance Castable Opposite Arrow (I i)
	where cast = U_II_I I

instance Castable Straight Arrow (U_1_I u i ii)
	where cast = U_I_II (\(U_1_I x) -> x)

instance Castable Opposite Arrow (U_1_I u i ii)
	where cast = U_II_I U_1_I

instance Castable Straight Arrow (U_I_1 u i ii)
	where cast = U_I_II (\(U_I_1 x) -> x)

instance Castable Opposite Arrow (U_I_1 u i ii)
	where cast = U_II_I U_I_1

instance Castable Straight Arrow (U_I_I u i)
	where cast = U_I_II (\(U_I_I x) -> x)

instance Castable Opposite Arrow (U_I_I u i)
	where cast = U_II_I U_I_I

instance Castable Straight Arrow (U_I_II u i ii)
	where cast = U_I_II (\(U_I_II x) -> x)

instance Castable Opposite Arrow (U_I_II u i ii)
	where cast = U_II_I U_I_II

instance Castable Straight Arrow (U_II_I u i ii)
	where cast = U_I_II (\(U_II_I x) -> x)

instance Castable Opposite Arrow (U_II_I u i ii)
	where cast = U_II_I U_II_I

instance Castable Straight Arrow (T_TT_I f g i)
	where cast = U_I_II (\(T_TT_I x) -> x)

instance Castable Opposite Arrow (T_TT_I f g i)
	where cast = U_II_I T_TT_I

instance Castable Straight Arrow (TT_T_I f g i)
	where cast = U_I_II (\(TT_T_I x) -> x)

instance Castable Opposite Arrow (TT_T_I f g i)
	where cast = U_II_I TT_T_I

instance Castable Straight Arrow (T_TT_TTT_I f g h i)
	where cast = U_I_II (\(T_TT_TTT_I x) -> x)

instance Castable Opposite Arrow (T_TT_TTT_I f g h i)
	where cast = U_II_I T_TT_TTT_I

instance Castable Straight Arrow (U_I_T_II u t i ii)
	where cast = U_I_II (\(U_I_T_II x) -> x)

instance Castable Opposite Arrow (U_I_T_II u f i ii)
	where cast = U_II_I U_I_T_II

instance Castable Straight Arrow (U_T_I_TT_I u t tt i)
	where cast = U_I_II (\(U_T_I_TT_I x) -> x)

instance Castable Opposite Arrow (U_T_I_TT_I u t tt i)
	where cast = U_II_I U_T_I_TT_I

instance Castable Opposite Arrow (U_I_UU_II_III u uu i ii iii)
	where cast = U_II_I U_I_UU_II_III

instance Castable Straight Arrow (U_I_UU_II_III u uu i ii iii)
	where cast = U_I_II (\(U_I_UU_II_III x) -> x)

instance Castable Straight Arrow (U_UU_UUU_V_III_I_II_UUUU u uu uuu uuuu v i ii iii)
	where cast = U_I_II (\(U_UU_UUU_V_III_I_II_UUUU x) -> x)

instance Castable Opposite Arrow (U_UU_UUU_V_III_I_II_UUUU u uu uuu uuuu v i ii iii)
	where cast = U_II_I U_UU_UUU_V_III_I_II_UUUU

instance Castable Straight Arrow (U_V_UU_UUU_UUUU_T_TT_I_II_III u v uu uuu uuuu t tt i ii iii_)
	where cast = U_I_II (\(U_V_UU_UUU_UUUU_T_TT_I_II_III x) -> x)

instance Castable Opposite Arrow (U_V_UU_UUU_UUUU_T_TT_I_II_III u v uu uuu uuuu t tt i ii iii_)
	where cast = U_II_I U_V_UU_UUU_UUUU_T_TT_I_II_III

instance Castable Straight Arrow (UU_V_U_I_II_T_II v u uu t i ii)
	where cast = U_I_II (\(UU_V_U_I_II_T_II x) -> x)

instance Castable Opposite Arrow (UU_V_U_I_II_T_II v u uu t i ii)
	where cast = U_II_I UU_V_U_I_II_T_II

instance Castable Straight Arrow (Recursive f)
	where cast = U_I_II (\(Recursive x) -> x)

instance Castable Opposite Arrow (Recursive f)
	where cast = U_II_I Recursive

instance Castable Straight Arrow (R_U_I_T_I u t i)
	where cast = U_I_II (\(R_U_I_T_I x) -> x)

instance Castable Opposite Arrow (R_U_I_T_I u t i)
	where cast = U_II_I R_U_I_T_I

instance Castable Straight Arrow (U_I_UU_III_U_II_I u uu i ii iii)
	where cast = U_I_II (\(U_I_UU_III_U_II_I x) -> x)

instance Castable Opposite Arrow (U_I_UU_III_U_II_I u uu i ii iii)
	where cast = U_II_I U_I_UU_III_U_II_I

instance Castable Straight Arrow (W_I_II_II u i ii)
	where cast = U_I_II (\(W_I_II_II x) -> x)

instance Castable Opposite Arrow (W_I_II_II u i ii)
	where cast = U_II_I W_I_II_II

instance Castable Straight Arrow (W_I_I_II u i ii)
	where cast = U_I_II (\(W_I_I_II x) -> x)

instance Castable Opposite Arrow (W_I_I_II u i ii)
	where cast = U_II_I W_I_I_II

instance Castable Opposite (->) (Unit -> i)
	where cast = U_II_I (\x _ -> x)

instance Castable Straight (->) (Unit -> i)
	where cast = U_I_II (\f -> f Unit)

instance Wrapper Arrow x
	=> Castable Straight (W_I_II_II (U_I_UU_III_U_II_I (->) (/\))) x where
	cast = U_I_II (W_I_II_II (U_I_UU_III_U_II_I (\x -> These (unwrap x) wrap)))

instance Wrapper Arrow x
	=> Castable Opposite (W_I_II_II (U_I_UU_III_U_II_I (->) (/\))) x where
	cast = U_II_I (W_I_II_II (U_I_UU_III_U_II_I (\x -> These (wrap x) unwrap)))

uw :: Castable Straight into i => into i (Supertype i)
uw = let U_I_II x = cast in x

unwrap :: Castable Straight (->) i => i -> Supertype i
unwrap = let U_I_II x = cast in x

wrap :: Castable Opposite into i => into (Supertype i) i
wrap = let U_II_I x = cast in x

-- Category: initial object
data Void

-- Category: terminal object
data Unit = Unit

data Verdict = Yes | No

type family Same a b where
  Same a a = 'Yes
  Same a b = 'No

type Different a b = Same a b ~ 'No
type Matching a b = Same a b ~ 'Yes

(/) :: (i -> o) -> i -> o
(/) f x = f x
