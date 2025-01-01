{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE UndecidableInstances #-}
module Ya.Algebra.Abstract where

infixl 8 `T'I`

infixl 9 #

infixl 8 `WR`
infixl 7 `WR_`
infixl 6 `WR__`
infixl 5 `WR___`

infixl 6 `T'TT'I`, `TT'T'I`
infixl 7 `T'TT'I_`

infixr 9 `L`

type WR t i = t i
type WR_ t i = t i
type WR__ t i = t i
type WR___ t i = t i

type T'I t i = t i

type family Supertype e

class Elicitable direction morphism e where
 elicit :: direction morphism e (Supertype e)

class (Elicitable Opposite to f, Elicitable Straight to f) => Wrapper to f where
deriving instance (Elicitable Opposite to f, Elicitable Straight to f) => Wrapper to f

newtype I i = Identity i

type instance Supertype (I i) = i

instance Elicitable Straight (->) (I i)
 where elicit = U_I_II (\(Identity x) -> x)

instance Elicitable Opposite (->) (I i)
 where elicit = U_II_I Identity

newtype U_U_I_II_UU_I_II u uu i ii = U_U_I_II_UU_I_II (u (u i ii) (uu i ii))

type instance Supertype (U_U_I_II_UU_I_II u uu i ii) = u (u i ii) (uu i ii)

instance Elicitable Opposite (->) (U_U_I_II_UU_I_II u uu i ii)
 where elicit = U_II_I U_U_I_II_UU_I_II

instance Elicitable Straight (->) (U_U_I_II_UU_I_II u uu i ii)
 where elicit = U_I_II (\(U_U_I_II_UU_I_II x) -> x)

newtype Recursive f = Recursive (f (Recursive f))

newtype T'TT'I t tt i = T'TT'I (t (tt i))

type T'TT'I_ = T'TT'I

type instance Supertype (T'TT'I t tt i) = t (tt i)

instance Elicitable Straight (->) (T'TT'I f g i)
 where elicit = U_I_II (\(T'TT'I x) -> x)

instance Elicitable Opposite (->) (T'TT'I f g i)
 where elicit = U_II_I T'TT'I

newtype TT'T'I t tt i = TT'T'I (tt (t i))

type instance Supertype (TT'T'I t tt i) = tt (t i)

instance Elicitable Straight (->) (TT'T'I f g i)
 where elicit = U_I_II (\(TT'T'I x) -> x)

instance Elicitable Opposite (->) (TT'T'I f g i)
 where elicit = U_II_I TT'T'I

newtype T e i = Tagged i

type (#) = T

type instance Supertype (T e i) = i

instance Elicitable Straight (->) (T e i)
 where elicit = U_I_II (\(Tagged x) -> x)

instance Elicitable Opposite (->) (T e i)
 where elicit = U_II_I Tagged

newtype L l t i = Labeled (t i)

newtype T'TTT'TT'I t ttt tt i = T'TTT'TT'I (t (tt (ttt i)))

type instance Supertype (T'TTT'TT'I t ttt tt i) = t (tt (ttt i))

instance Elicitable Straight (->) (T'TTT'TT'I f g h i)
 where elicit = U_I_II (\(T'TTT'TT'I x) -> x)

instance Elicitable Opposite (->) (T'TTT'TT'I f g h i)
 where elicit = U_II_I T'TTT'TT'I

data U_ u i ii

newtype U_I_I u i = U_I_I (u i i)

type instance Supertype (U_I_I u i) = u i i

instance Elicitable Straight (->) (U_I_I u i)
 where elicit = U_I_II (\(U_I_I x) -> x)

instance Elicitable Opposite (->) (U_I_I u i)
 where elicit = U_II_I U_I_I

newtype U_I_II u i ii = U_I_II (u i ii)

type instance Supertype (U_I_II u i ii) = u i ii

instance Elicitable Straight (->) (U_I_II u i ii)
 where elicit = U_I_II (\(U_I_II x) -> x)

instance Elicitable Opposite (->) (U_I_II u i ii)
 where elicit = U_II_I U_I_II

newtype U_II_I u i ii = U_II_I (u ii i)

type instance Supertype (U_II_I u ii i) = u i ii

instance Elicitable Straight (->) (U_II_I u i ii)
 where elicit = U_I_II (\(U_II_I x) -> x)

instance Elicitable Opposite (->) (U_II_I u i ii)
 where elicit = U_II_I U_II_I

newtype U_1_I u _' i = U_1_I (u () i)

newtype U_I_1 u i _' = U_I_1 (u i ())

newtype U_I_T_II t u i ii = U_I_T_II (u i (t ii))

newtype U_T_I_II t u i ii = U_T_I_II (u (t i) ii)

newtype U_T_I_TT_I u t tt i = U_T_I_TT_I (u (t i) (tt i))

newtype U_I_UU_II_III u uu i ii iii = U_I_UU_II_III (u i (uu ii iii))

newtype U_I_UU_II_I u uu i ii = U_I_UU_II_I (u i (uu ii i))

newtype U_I_UU_I_II u uu i ii = U_I_UU_I_II (u i (uu i ii))

newtype U_I_UU_II_U_II_I u uu i ii = U_I_UU_II_U_II_I (u i (uu ii (u ii i)))

newtype U_UU_UUU_V_III_I_II_UUUU u uu uuu uuuu v i ii x = U_UU_UUU_V_III_I_II_UUUU
 (u (uu (v uuu x i) (v uuu x ii)) (v uuu x (uuuu i ii)))

newtype U_V_UU_UUU_UUUU_T'TT'I_II_III u v uu uuu uuuu t tt i ii iii =
 U_V_UU_UUU_UUUU_T'TT'I_II_III (u (uuu (t i) (tt ii)) (v uu (uuuu i ii) iii))

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

type Opposite = U_II_I

pattern Opposite :: u e ee -> Opposite u ee e
pattern Opposite x <- U_II_I x
 where Opposite x = U_II_I x

{-# COMPLETE Opposite #-}

pattern In :: u e ee -> U_II_I u ee e
pattern In x = U_II_I x

type family Flip v where
 Flip Straight = Opposite
 Flip Opposite = Straight

type instance Supertype (U_1_I u _ i) = u () i

instance Elicitable Straight (->) (U_1_I u i ii)
 where elicit = U_I_II (\(U_1_I x) -> x)

instance Elicitable Opposite (->) (U_1_I u i ii)
 where elicit = U_II_I U_1_I

type instance Supertype (U_I_1 u i _) = u i ()

instance Elicitable Straight (->) (U_I_1 u i ii)
 where elicit = U_I_II (\(U_I_1 x) -> x)

instance Elicitable Opposite (->) (U_I_1 u i ii)
 where elicit = U_II_I U_I_1

type instance Supertype (L e t i) = t i

instance Elicitable Straight (->) (L e t i)
 where elicit = U_I_II (\(Labeled x) -> x)

instance Elicitable Opposite (->) (L e t i)
 where elicit = U_II_I Labeled

type instance Supertype (U_I_T_II t u i ii) = u i (t ii)

instance Elicitable Straight (->) (U_I_T_II u t i ii)
 where elicit = U_I_II (\(U_I_T_II x) -> x)

instance Elicitable Opposite (->) (U_I_T_II u f i ii)
 where elicit = U_II_I U_I_T_II

type instance Supertype (U_T_I_II t u i ii) = u (t i) ii

instance Elicitable Straight (->) (U_T_I_II u t i ii)
 where elicit = U_I_II (\(U_T_I_II x) -> x)

instance Elicitable Opposite (->) (U_T_I_II u t i ii)
 where elicit = U_II_I U_T_I_II

type instance Supertype (U_T_I_TT_I u t tt i) = u (t i) (tt i)

instance Elicitable Straight (->) (U_T_I_TT_I u t tt i)
 where elicit = U_I_II (\(U_T_I_TT_I x) -> x)

instance Elicitable Opposite (->) (U_T_I_TT_I u t tt i)
 where elicit = U_II_I U_T_I_TT_I

type instance Supertype (U_I_UU_II_III u uu i ii iii) = u i (uu ii iii)

instance Elicitable Opposite (->) (U_I_UU_II_III u uu i ii iii)
 where elicit = U_II_I U_I_UU_II_III

instance Elicitable Straight (->) (U_I_UU_II_III u uu i ii iii)
 where elicit = U_I_II (\(U_I_UU_II_III x) -> x)

type instance Supertype (U_I_UU_II_U_II_I u uu i ii) = u i (uu ii (u ii i))

instance Elicitable Opposite (->) (U_I_UU_II_U_II_I u uu i ii) where
 elicit = U_II_I U_I_UU_II_U_II_I

instance Elicitable Straight (->) (U_I_UU_II_U_II_I u uu i ii) where
 elicit = U_I_II (\(U_I_UU_II_U_II_I x) -> x)

type instance Supertype (U_I_UU_II_I u uu i ii) = u i (uu ii i)

instance Elicitable Opposite (->) (U_I_UU_II_I u uu i ii)
 where elicit = U_II_I U_I_UU_II_I

instance Elicitable Straight (->) (U_I_UU_II_I u uu i ii)
 where elicit = U_I_II (\(U_I_UU_II_I x) -> x)

type instance Supertype (U_I_UU_I_II u uu i ii) = u i (uu i ii)

instance Elicitable Opposite (->) (U_I_UU_I_II u uu i ii)
 where elicit = U_II_I U_I_UU_I_II

instance Elicitable Straight (->) (U_I_UU_I_II u uu i ii)
 where elicit = U_I_II (\(U_I_UU_I_II x) -> x)

type instance Supertype (U_UU_UUU_V_III_I_II_UUUU u uu uuu uuuu v i ii iii) =
 u (uu (v uuu iii i) (v uuu iii ii)) (v uuu iii (uuuu i ii))

instance Elicitable Straight (->) (U_UU_UUU_V_III_I_II_UUUU u uu uuu uuuu v i ii iii)
 where elicit = U_I_II (\(U_UU_UUU_V_III_I_II_UUUU x) -> x)

instance Elicitable Opposite (->) (U_UU_UUU_V_III_I_II_UUUU u uu uuu uuuu v i ii iii)
 where elicit = U_II_I U_UU_UUU_V_III_I_II_UUUU

type instance Supertype (U_V_UU_UUU_UUUU_T'TT'I_II_III u v uu uuu uuuu t tt i ii iii) =
  u (uuu (t i) (tt ii)) (v uu (uuuu i ii) iii)

instance Elicitable Straight (->) (U_V_UU_UUU_UUUU_T'TT'I_II_III u v uu uuu uuuu t tt i ii iii_)
 where elicit = U_I_II (\(U_V_UU_UUU_UUUU_T'TT'I_II_III x) -> x)

instance Elicitable Opposite (->) (U_V_UU_UUU_UUUU_T'TT'I_II_III u v uu uuu uuuu t tt i ii iii_)
 where elicit = U_II_I U_V_UU_UUU_UUUU_T'TT'I_II_III

type instance Supertype (UU_V_U_I_II_T_II v u uu t i ii) = uu (v u ii i) (t i)

instance Elicitable Straight (->) (UU_V_U_I_II_T_II v u uu t i ii)
 where elicit = U_I_II (\(UU_V_U_I_II_T_II x) -> x)

instance Elicitable Opposite (->) (UU_V_U_I_II_T_II v u uu t i ii)
 where elicit = U_II_I UU_V_U_I_II_T_II

type instance Supertype (Recursive f) = f (Recursive f)

instance Elicitable Straight (->) (Recursive f)
 where elicit = U_I_II (\(Recursive x) -> x)

instance Elicitable Opposite (->) (Recursive f)
 where elicit = U_II_I Recursive

type instance Supertype (R_U_I_T_I u t i) = Recursive (U_I_T_II t u i)

instance Elicitable Straight (->) (R_U_I_T_I u t i)
 where elicit = U_I_II (\(R_U_I_T_I x) -> x)

instance Elicitable Opposite (->) (R_U_I_T_I u t i)
 where elicit = U_II_I R_U_I_T_I

type instance Supertype (U_III_UU_I_II u uu iii i ii) = u i (uu ii iii)

instance Elicitable Straight (->) (U_III_UU_I_II u uu iii i ii)
 where elicit = U_I_II (\(U_III_UU_I_II x) -> x)

instance Elicitable Opposite (->) (U_III_UU_I_II u uu iii i ii)
 where elicit = U_II_I U_III_UU_I_II

type instance Supertype (U_I_UU_III_U_II_I u uu i ii iii) = u i (uu iii (u ii i))

instance Elicitable Straight (->) (U_I_UU_III_U_II_I u uu i ii iii)
 where elicit = U_I_II (\(U_I_UU_III_U_II_I x) -> x)

instance Elicitable Opposite (->) (U_I_UU_III_U_II_I u uu i ii iii)
 where elicit = U_II_I U_I_UU_III_U_II_I

type instance Supertype (W_I_II_II w i ii) = w i ii ii

instance Elicitable Straight (->) (W_I_II_II u i ii)
 where elicit = U_I_II (\(W_I_II_II x) -> x)

instance Elicitable Opposite (->) (W_I_II_II u i ii)
 where elicit = U_II_I W_I_II_II

type instance Supertype (W_I_II_I w i ii) = w i ii i

instance Elicitable Straight (->) (W_I_II_I u i ii)
 where elicit = U_I_II (\(W_I_II_I x) -> x)

instance Elicitable Opposite (->) (W_I_II_I u i ii)
 where elicit = U_II_I W_I_II_I

type instance Supertype (W_II_II_I w i ii) = w ii ii i

instance Elicitable Straight (->) (W_II_II_I w i ii)
 where elicit = U_I_II (\(W_II_II_I x) -> x)

instance Elicitable Opposite (->) (W_II_II_I w i ii)
 where elicit = U_II_I W_II_II_I

type instance Supertype (W_I_I_II w i ii) = w i i ii

instance Elicitable Straight (->) (W_I_I_II u i ii)
 where elicit = U_I_II (\(W_I_I_II x) -> x)

instance Elicitable Opposite (->) (W_I_I_II u i ii)
 where elicit = U_II_I W_I_I_II

type instance Supertype (W_III_I_II w iii i ii) = w i ii iii

instance Elicitable Straight (->) (W_III_I_II w iii i ii)
 where elicit = U_I_II (\(W_III_I_II x) -> x)

instance Elicitable Opposite (->) (W_III_I_II w iii i ii)
 where elicit = U_II_I W_III_I_II

-- type instance Supertype (Arrow i ii) = Arrow i ii

-- instance Elicitable Opposite (->) (Arrow i ii)
 -- where elicit = U_II_I (\f -> f)

-- instance Elicitable Straight (->) (Arrow i ii)
 -- where elicit = U_I_II (\f -> f)

type instance Supertype (Arrow Unit ii) = ii

instance Elicitable Opposite (->) (Arrow Unit ii)
 where elicit = U_II_I (\ii -> (\_ -> ii))

instance Elicitable Straight (->) (Arrow Unit ii)
 where elicit = U_I_II (\f -> f ())

-- type instance Supertype (Arrow i Void) = Arrow i i

-- instance Elicitable Opposite (->) (Arrow i Void)
 -- where elicit = U_II_I (\ii -> (\_ -> ii))

-- instance Elicitable Straight (->) (Arrow Unit ii)
 -- where elicit = U_I_II (\f -> f ())

unwrap :: Elicitable Straight into i => into i (Supertype i)
unwrap = let U_I_II x = elicit in x

wrap :: Elicitable Opposite into i => into (Supertype i) i
wrap = let U_II_I x = elicit in x

-- Category: initial object
data Void

type Unit = ()

pattern Unit = ()

type family Equals a b where
  Equals a b = a ~ b
