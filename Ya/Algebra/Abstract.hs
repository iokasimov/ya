{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE UndecidableInstances #-}
module Ya.Algebra.Abstract where

newtype Identity i = Identity i

newtype Recursive f = Recursive (f (Recursive f))

newtype U_I_I u i = U_I_I (u i i)

newtype U_I_II u i ii = U_I_II (u i ii)

newtype U_II_I u i ii = U_II_I (u ii i)

newtype T_TT_I t tt i = T_TT_I (t (tt i))

newtype T_TT_TTT_I t tt ttt i = T_TT_TTT_I (t (tt (ttt i)))

newtype U_I_T_II t u i ii = U_I_T_II (u i (t ii))

newtype U_T_I_II t u i ii = U_T_I_II (u (t i) ii)

newtype U_UU_UUU_UUUU_T_TT_I_II_III u uu uuu uuuu t tt i ii iii =
	U_UU_UUU_UUUU_T_TT_I_II_III (u (uuu (t i) (tt ii)) (uu (uuuu i ii) iii))

newtype R_U_I_T_I u t i = R_U_I_T_I (Recursive (U_I_T_II t u i))

type Arrow = (->)

type Mono = U_I_I

type Flat = U_I_II

type Dual = U_II_I

type Kleisli = U_I_T_II

type family Supertype e where
	Supertype (Identity i) = i
	Supertype (Recursive f) = f (Recursive f)
	Supertype (U_I_I u i) = u i i
	Supertype (U_I_II u i ii) = u i ii
	Supertype (U_II_I u ii i) = u i ii
	Supertype (U_I_T_II t u i ii) = u i (t ii)
	Supertype (U_T_I_II t u i ii) = u (t i) ii
	Supertype (T_TT_I t tt i) = t (tt i)
	Supertype (T_TT_TTT_I t tt ttt i) = t (tt (ttt i))
	Supertype (U_UU_UUU_UUUU_T_TT_I_II_III u uu uuu uuuu t tt i ii iii) =
		u (uuu (t i) (tt ii)) (uu (uuuu i ii) iii)
	Supertype (R_U_I_T_I u t i) = Recursive (U_I_T_II t u i)

class Castable direction morphism e where
	cast :: (direction morphism e) (Supertype e)

class (Castable Dual to f, Castable Flat to f) => Wrapper to f where
deriving instance (Castable Dual to f, Castable Flat to f) => Wrapper to f

instance Castable Flat Arrow (Identity i)
	where cast = U_I_II (\(Identity x) -> x)

instance Castable Dual Arrow (Identity i)
	where cast = U_II_I Identity

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

instance Castable Flat Arrow (T_TT_TTT_I f g h i)
	where cast = U_I_II (\(T_TT_TTT_I x) -> x)

instance Castable Dual Arrow (T_TT_TTT_I f g h i)
	where cast = U_II_I T_TT_TTT_I

instance Castable Flat Arrow (U_I_T_II u t i ii)
	where cast = U_I_II (\(U_I_T_II x) -> x)

instance Castable Dual Arrow (U_I_T_II u f i ii)
	where cast = U_II_I U_I_T_II

instance Castable Flat Arrow (U_UU_UUU_UUUU_T_TT_I_II_III u uu uuu uuuu t tt i ii iii_)
	where cast = U_I_II (\(U_UU_UUU_UUUU_T_TT_I_II_III x) -> x)

instance Castable Dual Arrow (U_UU_UUU_UUUU_T_TT_I_II_III u uu uuu uuuu t tt i ii iii_)
	where cast = U_II_I U_UU_UUU_UUUU_T_TT_I_II_III

instance Castable Flat Arrow (Recursive f)
	where cast = U_I_II (\(Recursive x) -> x)

instance Castable Dual Arrow (Recursive f)
	where cast = U_II_I Recursive

instance Castable Flat Arrow (R_U_I_T_I u t i)
	where cast = U_I_II (\(R_U_I_T_I x) -> x)

instance Castable Dual Arrow (R_U_I_T_I u t i)
	where cast = U_II_I R_U_I_T_I

unwrap :: Castable Flat into i => into i (Supertype i)
unwrap = let U_I_II x = cast in x

wrap :: Castable Dual into i => into (Supertype i) i
wrap = let U_II_I x = cast in x