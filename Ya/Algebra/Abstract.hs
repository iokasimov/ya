{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE UndecidableInstances #-}
module Ya.Algebra.Abstract where

newtype Identity i = Identity i

newtype U_I_I u i = U_I_I (u i i)

newtype U_I_II u i ii = U_I_II (u i ii)

newtype U_II_I u i ii = U_II_I (u ii i)

newtype T_TT_I t tt i = T_TT_I (t (tt i))

newtype T_TT_TTT_I t tt ttt i = T_TT_TTT_I (t (tt (ttt i)))

newtype U_I_T_II t u i ii = U_I_T_II (u i (t ii))

newtype U_T_I_II t u i ii = U_T_I_II (u (t i) ii)

type Arrow = (->)

type Mono = U_I_I

type Flat = U_I_II

type Dual = U_II_I

type Kleisli = U_I_T_II

type family Supertype e where
	Supertype (Identity i) = i
	Supertype (U_I_I u i) = u i i
	Supertype (U_I_II u i ii) = u i ii
	Supertype (U_II_I u ii i) = u i ii
	Supertype (U_I_T_II t u i ii) = u i (t ii)
	Supertype (U_T_I_II t u i ii) = u (t i) ii
	Supertype (T_TT_I t tt i) = t (tt i)
	Supertype (T_TT_TTT_I t tt ttt i) = t (tt (ttt i))

class Castable direction morphism e where
	cast :: (direction morphism e) (Supertype e)

class (Castable Dual to f, Castable Flat to f) => Wrapper to f where
deriving instance (Castable Dual to f, Castable Flat to f) => Wrapper to f

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