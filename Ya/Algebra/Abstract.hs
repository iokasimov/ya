{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE UndecidableInstances #-}
module Ya.Algebra.Abstract where

infixl 0 /

type (/) t i = t i

data (/\) i ii = These i ii

data (\/) i ii = This i | That ii

newtype I i = I i

newtype Constant i ii = Constant ii

newtype Recursive f = Recursive (f (Recursive f))

newtype T_TT_I t tt i = T_TT_I (t (tt i))

newtype TT_T_I t tt i = TT_T_I (tt (t i))

newtype T_TT_TTT_I t tt ttt i = T_TT_TTT_I (t (tt (ttt i)))

newtype U_I_I u i = U_I_I (u i i)

newtype U_I_II u i ii = U_I_II (u i ii)

newtype U_II_I u i ii = U_II_I (u ii i)

newtype U_1_II u i ii = U_1_II (u Unit ii)

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

data U_ u i

type Arrow = (->)

type Mono = U_I_I

-- Rename to Straight?
type Flat = U_I_II

-- Rename to Opposite?
type Dual = U_II_I

type This = U_II_I

type That = U_I_II

type family Flip v where
	Flip Flat = Dual
	Flip Dual = Flat

type family Supertype e where
	Supertype (I i) = i
	Supertype (U_1_II u i ii) = u Unit ii
	Supertype (Constant i ii) = ii
	Supertype (Recursive f) = f (Recursive f)
	Supertype (T_TT_I t tt i) = t (tt i)
	Supertype (TT_T_I t tt i) = tt (t i)
	Supertype (T_TT_TTT_I t tt ttt i) = t (tt (ttt i))
	Supertype (U_I_I u i) = u i i
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

class Castable direction morphism e where
	cast :: direction morphism e (Supertype e)

class (Castable Dual to f, Castable Flat to f) => Wrapper to f where
deriving instance (Castable Dual to f, Castable Flat to f) => Wrapper to f

instance Castable Flat Arrow (I i)
	where cast = U_I_II (\(I x) -> x)

instance Castable Dual Arrow (I i)
	where cast = U_II_I I

instance Castable Flat Arrow (U_1_II u i ii)
	where cast = U_I_II (\(U_1_II x) -> x)

instance Castable Dual Arrow (U_1_II u i ii)
	where cast = U_II_I U_1_II

instance Castable Flat Arrow (Constant i ii)
	where cast = U_I_II (\(Constant x) -> x)

instance Castable Dual Arrow (Constant i ii)
	where cast = U_II_I Constant

instance Castable Flat Arrow (U_I_I u i)
	where cast = U_I_II (\(U_I_I x) -> x)

instance Castable Dual Arrow (U_I_I u i)
	where cast = U_II_I U_I_I

instance Castable Flat Arrow (U_I_II u i ii)
	where cast = U_I_II (\(U_I_II x) -> x)

instance Castable Dual Arrow (U_I_II u i ii)
	where cast = U_II_I U_I_II

instance Castable Flat Arrow (U_II_I u i ii)
	where cast = U_I_II (\(U_II_I x) -> x)

instance Castable Dual Arrow (U_II_I u i ii)
	where cast = U_II_I U_II_I

instance Castable Flat Arrow (T_TT_I f g i)
	where cast = U_I_II (\(T_TT_I x) -> x)

instance Castable Dual Arrow (T_TT_I f g i)
	where cast = U_II_I T_TT_I

instance Castable Flat Arrow (TT_T_I f g i)
	where cast = U_I_II (\(TT_T_I x) -> x)

instance Castable Dual Arrow (TT_T_I f g i)
	where cast = U_II_I TT_T_I

instance Castable Flat Arrow (T_TT_TTT_I f g h i)
	where cast = U_I_II (\(T_TT_TTT_I x) -> x)

instance Castable Dual Arrow (T_TT_TTT_I f g h i)
	where cast = U_II_I T_TT_TTT_I

instance Castable Flat Arrow (U_I_T_II u t i ii)
	where cast = U_I_II (\(U_I_T_II x) -> x)

instance Castable Dual Arrow (U_I_T_II u f i ii)
	where cast = U_II_I U_I_T_II

instance Castable Flat Arrow (U_T_I_TT_I u t tt i)
	where cast = U_I_II (\(U_T_I_TT_I x) -> x)

instance Castable Dual Arrow (U_T_I_TT_I u t tt i)
	where cast = U_II_I U_T_I_TT_I

instance Castable Dual Arrow (U_I_UU_II_III u uu i ii iii)
	where cast = U_II_I U_I_UU_II_III

instance Castable Flat Arrow (U_I_UU_II_III u uu i ii iii)
	where cast = U_I_II (\(U_I_UU_II_III x) -> x)

instance Castable Flat Arrow (U_UU_UUU_V_III_I_II_UUUU u uu uuu uuuu v i ii iii)
	where cast = U_I_II (\(U_UU_UUU_V_III_I_II_UUUU x) -> x)

instance Castable Dual Arrow (U_UU_UUU_V_III_I_II_UUUU u uu uuu uuuu v i ii iii)
	where cast = U_II_I U_UU_UUU_V_III_I_II_UUUU

instance Castable Flat Arrow (U_V_UU_UUU_UUUU_T_TT_I_II_III u v uu uuu uuuu t tt i ii iii_)
	where cast = U_I_II (\(U_V_UU_UUU_UUUU_T_TT_I_II_III x) -> x)

instance Castable Dual Arrow (U_V_UU_UUU_UUUU_T_TT_I_II_III u v uu uuu uuuu t tt i ii iii_)
	where cast = U_II_I U_V_UU_UUU_UUUU_T_TT_I_II_III

instance Castable Flat Arrow (UU_V_U_I_II_T_II v u uu t i ii)
	where cast = U_I_II (\(UU_V_U_I_II_T_II x) -> x)

instance Castable Dual Arrow (UU_V_U_I_II_T_II v u uu t i ii)
	where cast = U_II_I UU_V_U_I_II_T_II

instance Castable Flat Arrow (Recursive f)
	where cast = U_I_II (\(Recursive x) -> x)

instance Castable Dual Arrow (Recursive f)
	where cast = U_II_I Recursive

instance Castable Flat Arrow (R_U_I_T_I u t i)
	where cast = U_I_II (\(R_U_I_T_I x) -> x)

instance Castable Dual Arrow (R_U_I_T_I u t i)
	where cast = U_II_I R_U_I_T_I

instance Castable Flat Arrow (U_I_UU_III_U_II_I u uu i ii iii)
	where cast = U_I_II (\(U_I_UU_III_U_II_I x) -> x)

instance Castable Dual Arrow (U_I_UU_III_U_II_I u uu i ii iii)
	where cast = U_II_I U_I_UU_III_U_II_I

instance Castable Flat Arrow (W_I_II_II u i ii)
	where cast = U_I_II (\(W_I_II_II x) -> x)

instance Castable Dual Arrow (W_I_II_II u i ii)
	where cast = U_II_I W_I_II_II

instance Castable Flat Arrow (W_I_I_II u i ii)
	where cast = U_I_II (\(W_I_I_II x) -> x)

instance Castable Dual Arrow (W_I_I_II u i ii)
	where cast = U_II_I W_I_I_II

unwrap :: Castable Flat into i => into i (Supertype i)
unwrap = let U_I_II x = cast in x

wrap :: Castable Dual into i => into (Supertype i) i
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
