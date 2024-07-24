{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE UndecidableInstances #-}
module Ya.Algebra.Abstract where

newtype U_U_I_II_UU_I_II u uu i ii = U_U_I_II_UU_I_II (u (u i ii) (uu i ii))

newtype Identity i = Identity i

newtype Recursive f = Recursive (f (Recursive f))

newtype T_TT_I t tt i = T_TT_I (t (tt i))

newtype TT_T_I t tt i = TT_T_I (tt (t i))

newtype T_'_I e t i = T_'_I (t i)

newtype T_TTT_TT_I t ttt tt i = T_TTT_TT_I (t (tt (ttt i)))

data U_ u i ii

newtype U_I_I u i = U_I_I (u i i)

newtype U_I_II u i ii = U_I_II (u i ii)

newtype U_II_I u i ii = U_II_I (u ii i)

newtype U_1_I u _' i = U_1_I (u () i)

newtype U_I_1 u i _' = U_I_1 (u i ())

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

newtype U_III_UU_I_II u uu iii i ii =
	U_III_UU_I_II (u i (uu ii iii))

newtype U_I_UU_III_U_II_I u uu i ii iii =
	U_I_UU_III_U_II_I (u i (uu iii (u ii i)))

newtype W_I_II_II w i ii = W_I_II_II (w i ii ii)

newtype W_I_I_II w i ii = W_I_I_II (w i i ii)

newtype W_I_II_I w i ii = W_I_II_I (w i ii i)

newtype W_II_II_I w i ii = W_II_II_I (w ii ii i)

newtype W_III_I_II w iii i ii = W_III_I_II (w i ii iii)

newtype UU_U_I_II_U_II_I u uu i ii
	= UU_U_I_II_U_II_I (uu (u i ii) (u ii i))

newtype UU_V_U_III_I_V_U_III_II v u uu i ii iii
	= UU_V_U_III_I_V_U_III_II
		(uu iii (uu (v u iii i) (v u iii ii)))

type Diagram = U_

type Arrow = (->)

type Function = (->)

type Both = U_I_I

type Straight = U_I_II

pattern Straight :: u e ee -> Straight u e ee
pattern Straight x <- U_I_II x
	where Straight x = U_I_II x

{-# COMPLETE Straight #-}

pattern Out :: u e ee -> U_I_II u e ee
pattern Out x = U_I_II x

type Opposite = U_II_I

pattern Opposite :: u e ee -> Opposite u ee e
pattern Opposite x <- U_II_I x
	where Opposite x = U_II_I x

{-# COMPLETE Opposite #-}

pattern In :: u e ee -> U_II_I u ee e
pattern In x = U_II_I x

type This = U_II_I

type That = U_I_II

type Constant = U_1_I

type Labeled = T_'_I

-- TODO: move to `Primitive`
type Fore = Labeled (Straight (->) () ())

-- TODO: move to `Primitive`
pattern Fore :: t e -> Fore t e
pattern Fore e = T_'_I e

-- TODO: move to `Primitive`
type Back = Labeled (Opposite (->) () ())

-- TODO: move to `Primitive`
pattern Back :: t e -> Back t e
pattern Back e = T_'_I e

type family Flip v where
	Flip Straight = Opposite
	Flip Opposite = Straight

type family Supertype e where
 Supertype (Identity i) = i
 Supertype (Recursive f) = f (Recursive f)
 Supertype (T_TT_I t tt i) = t (tt i)
 Supertype (TT_T_I t tt i) = tt (t i)
 Supertype (T_'_I e t i) = t i
 Supertype (T_TTT_TT_I t ttt tt i) = t (tt (ttt i))
 Supertype (U_I_I u i) = u i i
 Supertype (U_1_I u _ i) = u () i
 Supertype (U_I_1 u i _) = u i ()
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
 Supertype (U_III_UU_I_II u uu iii i ii) = u i (uu ii iii)
 Supertype (U_I_UU_III_U_II_I u uu i ii iii) = u i (uu iii (u ii i))
 Supertype (W_I_II_I w i ii) = w i ii i
 Supertype (W_I_II_II w i ii) = w i ii ii
 Supertype (W_II_II_I w i ii) = w ii ii i
 Supertype (W_I_I_II w i ii) = w i i ii
 Supertype (W_III_I_II w iii i ii) = w i ii iii
 Supertype (Arrow () ii) = ii
 Supertype (Arrow i ii) = Arrow i ii
 Supertype (U_U_I_II_UU_I_II u uu i ii) = u (u i ii) (uu i ii)

class Castable direction morphism e where
	cast :: direction morphism e (Supertype e)

class (Castable Opposite to f, Castable Straight to f) => Wrapper to f where
deriving instance (Castable Opposite to f, Castable Straight to f) => Wrapper to f

instance Castable Straight (->) (Identity i)
	where cast = U_I_II (\(Identity x) -> x)

instance Castable Opposite (->) (Identity i)
	where cast = U_II_I Identity

instance Castable Straight (->) (U_1_I u i ii)
	where cast = U_I_II (\(U_1_I x) -> x)

instance Castable Opposite (->) (U_1_I u i ii)
	where cast = U_II_I U_1_I

instance Castable Straight (->) (U_I_1 u i ii)
	where cast = U_I_II (\(U_I_1 x) -> x)

instance Castable Opposite (->) (U_I_1 u i ii)
	where cast = U_II_I U_I_1

instance Castable Straight (->) (U_I_I u i)
	where cast = U_I_II (\(U_I_I x) -> x)

instance Castable Opposite (->) (U_I_I u i)
	where cast = U_II_I U_I_I

instance Castable Straight (->) (U_I_II u i ii)
	where cast = U_I_II (\(U_I_II x) -> x)

instance Castable Opposite (->) (U_I_II u i ii)
	where cast = U_II_I U_I_II

instance Castable Straight (->) (U_II_I u i ii)
	where cast = U_I_II (\(U_II_I x) -> x)

instance Castable Opposite (->) (U_II_I u i ii)
	where cast = U_II_I U_II_I

instance Castable Straight (->) (T_TT_I f g i)
	where cast = U_I_II (\(T_TT_I x) -> x)

instance Castable Opposite (->) (T_TT_I f g i)
	where cast = U_II_I T_TT_I

instance Castable Straight (->) (TT_T_I f g i)
	where cast = U_I_II (\(TT_T_I x) -> x)

instance Castable Opposite (->) (TT_T_I f g i)
	where cast = U_II_I TT_T_I

instance Castable Straight (->) (T_'_I e t i)
	where cast = U_I_II (\(T_'_I x) -> x)

instance Castable Opposite (->) (T_'_I e t i)
	where cast = U_II_I T_'_I

instance Castable Straight (->) (T_TTT_TT_I f g h i)
	where cast = U_I_II (\(T_TTT_TT_I x) -> x)

instance Castable Opposite (->) (T_TTT_TT_I f g h i)
	where cast = U_II_I T_TTT_TT_I

instance Castable Straight (->) (U_I_T_II u t i ii)
	where cast = U_I_II (\(U_I_T_II x) -> x)

instance Castable Opposite (->) (U_I_T_II u f i ii)
	where cast = U_II_I U_I_T_II

instance Castable Straight (->) (U_T_I_TT_I u t tt i)
	where cast = U_I_II (\(U_T_I_TT_I x) -> x)

instance Castable Opposite (->) (U_T_I_TT_I u t tt i)
	where cast = U_II_I U_T_I_TT_I

instance Castable Opposite (->) (U_I_UU_II_III u uu i ii iii)
	where cast = U_II_I U_I_UU_II_III

instance Castable Straight (->) (U_I_UU_II_III u uu i ii iii)
	where cast = U_I_II (\(U_I_UU_II_III x) -> x)

instance Castable Straight (->) (U_UU_UUU_V_III_I_II_UUUU u uu uuu uuuu v i ii iii)
	where cast = U_I_II (\(U_UU_UUU_V_III_I_II_UUUU x) -> x)

instance Castable Opposite (->) (U_UU_UUU_V_III_I_II_UUUU u uu uuu uuuu v i ii iii)
	where cast = U_II_I U_UU_UUU_V_III_I_II_UUUU

instance Castable Straight (->) (U_V_UU_UUU_UUUU_T_TT_I_II_III u v uu uuu uuuu t tt i ii iii_)
	where cast = U_I_II (\(U_V_UU_UUU_UUUU_T_TT_I_II_III x) -> x)

instance Castable Opposite (->) (U_V_UU_UUU_UUUU_T_TT_I_II_III u v uu uuu uuuu t tt i ii iii_)
	where cast = U_II_I U_V_UU_UUU_UUUU_T_TT_I_II_III

instance Castable Straight (->) (UU_V_U_I_II_T_II v u uu t i ii)
	where cast = U_I_II (\(UU_V_U_I_II_T_II x) -> x)

instance Castable Opposite (->) (UU_V_U_I_II_T_II v u uu t i ii)
	where cast = U_II_I UU_V_U_I_II_T_II

instance Castable Straight (->) (Recursive f)
	where cast = U_I_II (\(Recursive x) -> x)

instance Castable Opposite (->) (Recursive f)
	where cast = U_II_I Recursive

instance Castable Straight (->) (R_U_I_T_I u t i)
	where cast = U_I_II (\(R_U_I_T_I x) -> x)

instance Castable Opposite (->) (R_U_I_T_I u t i)
	where cast = U_II_I R_U_I_T_I

instance Castable Straight (->) (U_III_UU_I_II u uu iii i ii)
	where cast = U_I_II (\(U_III_UU_I_II x) -> x)

instance Castable Opposite (->) (U_III_UU_I_II u uu iii i ii)
	where cast = U_II_I U_III_UU_I_II

instance Castable Straight (->) (U_I_UU_III_U_II_I u uu i ii iii)
	where cast = U_I_II (\(U_I_UU_III_U_II_I x) -> x)

instance Castable Opposite (->) (U_I_UU_III_U_II_I u uu i ii iii)
	where cast = U_II_I U_I_UU_III_U_II_I

instance Castable Straight (->) (W_I_II_II u i ii)
	where cast = U_I_II (\(W_I_II_II x) -> x)

instance Castable Opposite (->) (W_I_II_II u i ii)
	where cast = U_II_I W_I_II_II

instance Castable Straight (->) (W_I_II_I u i ii)
	where cast = U_I_II (\(W_I_II_I x) -> x)

instance Castable Opposite (->) (W_I_II_I u i ii)
	where cast = U_II_I W_I_II_I

instance Castable Straight (->) (W_II_II_I w i ii)
	where cast = U_I_II (\(W_II_II_I x) -> x)

instance Castable Opposite (->) (W_II_II_I w i ii)
	where cast = U_II_I W_II_II_I

instance Castable Straight (->) (W_I_I_II u i ii)
	where cast = U_I_II (\(W_I_I_II x) -> x)

instance Castable Opposite (->) (W_I_I_II u i ii)
	where cast = U_II_I W_I_I_II

instance Castable Straight (->) (W_III_I_II w iii i ii)
	where cast = U_I_II (\(W_III_I_II x) -> x)

instance Castable Opposite (->) (W_III_I_II w iii i ii)
	where cast = U_II_I W_III_I_II

instance Castable Opposite (->) (() -> i)
	where cast = U_II_I (\x _ -> x)

instance Castable Straight (->) (() -> i)
	where cast = U_I_II (\f -> f ())

instance Castable Opposite (->) (U_U_I_II_UU_I_II u uu i ii)
	where cast = U_II_I U_U_I_II_UU_I_II

instance Castable Straight (->) (U_U_I_II_UU_I_II u uu i ii)
	where cast = U_I_II (\(U_U_I_II_UU_I_II x) -> x)

unwrap :: Castable Straight into i => into i (Supertype i)
unwrap = let U_I_II x = cast in x

wrap :: Castable Opposite (->) i => Supertype i -> i
wrap = let U_II_I x = cast in x

-- Category: initial object
data Void

type family Equals a b where
  Equals a b = a ~ b
