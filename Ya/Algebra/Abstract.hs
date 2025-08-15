{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE UndecidableInstances #-}
module Ya.Algebra.Abstract where

infixl 9 #, `T`, `L`
infixl 8 `T'I`
infixl 7 `T'I_`

infixl 7 `T'TT'I`, `TT'T'I`
infixl 6 `T'TT'I_`

type T t = t
type T'I t = t
type T'I_ t = t

type family Supertype e

class Elicitable direction morphism e where
 elicit :: direction morphism e (Supertype e)

class (Elicitable T'II'I to f, Elicitable T'I'II to f) => Wrapper to f where
deriving instance (Elicitable T'II'I to f, Elicitable T'I'II to f) => Wrapper to f

newtype I i = Identity i

type instance Supertype (I i) = i

instance Elicitable T'I'II (->) (I i)
 where elicit = T'I'II (\(Identity x) -> x)

instance Elicitable T'II'I (->) (I i)
 where elicit = T'II'I Identity

newtype U_T'I'II_UT'I'II u uu i ii = U_T'I'II_UT'I'II (u (u i ii) (uu i ii))

type instance Supertype (U_T'I'II_UT'I'II u uu i ii) = u (u i ii) (uu i ii)

instance Elicitable T'II'I (->) (U_T'I'II_UT'I'II u uu i ii)
 where elicit = T'II'I U_T'I'II_UT'I'II

instance Elicitable T'I'II (->) (U_T'I'II_UT'I'II u uu i ii)
 where elicit = T'I'II (\(U_T'I'II_UT'I'II x) -> x)

newtype Recursive f = Recursive (f (Recursive f))

newtype T'TT'I t tt i = T'TT'I (t (tt i))

type T'TT'I_ = T'TT'I

type instance Supertype (T'TT'I t tt i) = t (tt i)

instance Elicitable T'I'II (->) (T'TT'I f g i)
 where elicit = T'I'II (\(T'TT'I x) -> x)

instance Elicitable T'II'I (->) (T'TT'I f g i)
 where elicit = T'II'I T'TT'I

newtype TT'T'I t tt i = TT'T'I (tt (t i))

type instance Supertype (TT'T'I t tt i) = tt (t i)

instance Elicitable T'I'II (->) (TT'T'I f g i)
 where elicit = T'I'II (\(TT'T'I x) -> x)

instance Elicitable T'II'I (->) (TT'T'I f g i)
 where elicit = T'II'I TT'T'I

newtype Tagged e i = Tag i

type (#) = Tagged

type instance Supertype (Tagged e i) = i

instance Elicitable T'I'II (->) (Tagged e i)
 where elicit = T'I'II (\(Tag x) -> x)

instance Elicitable T'II'I (->) (Tagged e i)
 where elicit = T'II'I Tag

newtype T'TTT'TT'I t ttt tt i = T'TTT'TT'I (t (tt (ttt i)))

type instance Supertype (T'TTT'TT'I t ttt tt i) = t (tt (ttt i))

instance Elicitable T'I'II (->) (T'TTT'TT'I f g h i)
 where elicit = T'I'II (\(T'TTT'TT'I x) -> x)

instance Elicitable T'II'I (->) (T'TTT'TT'I f g h i)
 where elicit = T'II'I T'TTT'TT'I

data U_ u i ii

newtype T'I'I u i = T'I'I (u i i)

type instance Supertype (T'I'I u i) = u i i

instance Elicitable T'I'II (->) (T'I'I u i)
 where elicit = T'I'II (\(T'I'I x) -> x)

instance Elicitable T'II'I (->) (T'I'I u i)
 where elicit = T'II'I T'I'I

newtype T'I'II u i ii = T'I'II (u i ii)

type instance Supertype (T'I'II u i ii) = u i ii

instance Elicitable T'I'II (->) (T'I'II u i ii)
 where elicit = T'I'II (\(T'I'II x) -> x)

instance Elicitable T'II'I (->) (T'I'II u i ii)
 where elicit = T'II'I T'I'II

newtype T'II'I u i ii = T'II'I (u ii i)

type instance Supertype (T'II'I u ii i) = u i ii

instance Elicitable T'I'II (->) (T'II'I u i ii)
 where elicit = T'I'II (\(T'II'I x) -> x)

instance Elicitable T'II'I (->) (T'II'I u i ii)
 where elicit = T'II'I T'II'I

newtype U_1_I u _' i = U_1_I (u () i)

newtype U_I_1 u i _' = U_I_1 (u i ())

newtype T'I' i ii = T'I' i

type instance Supertype (T'I' i ii) = i

instance Elicitable T'II'I (->) (T'I' i ii) where elicit = T'II'I T'I'
instance Elicitable T'I'II (->) (T'I' i ii) where elicit = T'I'II (\(T'I' x) -> x)

newtype T''II u i ii = T''II ii

type instance Supertype (T''II u i ii) = ii

instance Elicitable T'II'I (->) (T''II u i ii) where elicit = T'II'I T''II
instance Elicitable T'I'II (->) (T''II u i ii) where elicit = T'I'II (\(T''II x) -> x)

newtype T'I'TT'II u t i ii = T'I'TT'II (u i (t ii))

newtype U_T'I'II t u i ii = U_T'I'II (u (t i) ii)

newtype T'TT'I'TTT'I u t tt i = T'TT'I'TTT'I (u (t i) (tt i))

newtype T'I'TT'II'I u uu i ii = T'I'TT'II'I (u i (uu ii i))

newtype T'II'TT'I'III u uu i ii iii = T'II'TT'I'III (u ii (uu i iii))

type instance Supertype (T'II'TT'I'III u uu i ii iii) = u ii (uu i iii)

instance Elicitable T'II'I (->) (T'II'TT'I'III u uu i ii iii)
 where elicit = T'II'I T'II'TT'I'III

instance Elicitable T'I'II (->) (T'II'TT'I'III u uu i ii iii)
 where elicit = T'I'II (\(T'II'TT'I'III x) -> x)

newtype U_I_UT'I'II u uu i ii = U_I_UT'I'II (u i (uu i ii))

newtype T'I'TT'II'T'II'I u uu i ii = T'I'TT'II'T'II'I (u i (uu ii (u ii i)))

newtype U_UU_UUU_V_III_I_II_UUUU u uu uuu uuuu v i ii x = U_UU_UUU_V_III_I_II_UUUU
 (u (uu (v uuu x i) (v uuu x ii)) (v uuu x (uuuu i ii)))

newtype U_V_UU_UUU_UUUU_T'TT'I_II_III u v uu uuu uuuu t tt i ii iii =
 U_V_UU_UUU_UUUU_T'TT'I_II_III (u (uuu (t i) (tt ii)) (v uu (uuuu i ii) iii))

newtype UU_V_T'I'II_T_II v u uu t i ii =
 UU_V_T'I'II_T_II (uu (v u ii i) (t i))

newtype R_U_I_T_I u t i = R_U_I_T_I (Recursive (T'I'TT'II u t i))

newtype U_III_UT'I'II u uu iii i ii =
 U_III_UT'I'II (u i (uu ii iii))

newtype U_I_UU_III_T'II'I u uu i ii iii =
 U_I_UU_III_T'II'I (u i (uu iii (u ii i)))

newtype W_I_II_II w i ii = W_I_II_II (w i ii ii)

newtype W_I_I_II w i ii = W_I_I_II (w i i ii)

newtype W_I_II_I w i ii = W_I_II_I (w i ii i)

newtype W_II_II_I w i ii = W_II_II_I (w ii ii i)

newtype W_III_I_II w iii i ii = W_III_I_II (w i ii iii)

newtype UU_T'I'II_T'II'I u uu i ii
 = UU_T'I'II_T'II'I (uu (u i ii) (u ii i))

newtype UU_V_U_III_I_V_U_III_II v u uu i ii iii
 = UU_V_U_III_I_V_U_III_II
  (uu iii (uu (v u iii i) (v u iii ii)))

type Diagram = U_

type Arrow = (->)

type Function = (->)

type Both = T'I'I

pattern Both :: u i i -> T'I'I u i
pattern Both x = T'I'I x

pattern In :: u e ee -> T'II'I u ee e
pattern In x = T'II'I x

type instance Supertype (U_1_I u _ i) = u () i

instance Elicitable T'I'II (->) (U_1_I u i ii)
 where elicit = T'I'II (\(U_1_I x) -> x)

instance Elicitable T'II'I (->) (U_1_I u i ii)
 where elicit = T'II'I U_1_I

type instance Supertype (U_I_1 u i _) = u i ()

instance Elicitable T'I'II (->) (U_I_1 u i ii)
 where elicit = T'I'II (\(U_I_1 x) -> x)

instance Elicitable T'II'I (->) (U_I_1 u i ii)
 where elicit = T'II'I U_I_1

newtype L t _t l i = Labeled (t i)

type instance Supertype (L t _t l i) = t i

instance Elicitable T'I'II (->) (L t _t l i)
 where elicit = T'I'II (\(Labeled x) -> x)

instance Elicitable T'II'I (->) (L t _t l i)
 where elicit = T'II'I Labeled

type instance Supertype (T'I'TT'II u t i ii) = u i (t ii)

instance Elicitable T'I'II (->) (T'I'TT'II u t i ii)
 where elicit = T'I'II (\(T'I'TT'II x) -> x)

instance Elicitable T'II'I (->) (T'I'TT'II u t i ii)
 where elicit = T'II'I T'I'TT'II

type instance Supertype (U_T'I'II t u i ii) = u (t i) ii

instance Elicitable T'I'II (->) (U_T'I'II u t i ii)
 where elicit = T'I'II (\(U_T'I'II x) -> x)

instance Elicitable T'II'I (->) (U_T'I'II u t i ii)
 where elicit = T'II'I U_T'I'II

type instance Supertype (T'TT'I'TTT'I u t tt i) = u (t i) (tt i)

instance Elicitable T'I'II (->) (T'TT'I'TTT'I u t tt i)
 where elicit = T'I'II (\(T'TT'I'TTT'I x) -> x)

instance Elicitable T'II'I (->) (T'TT'I'TTT'I u t tt i)
 where elicit = T'II'I T'TT'I'TTT'I

type instance Supertype (T'I'TT'II'T'II'I u uu i ii) = u i (uu ii (u ii i))

instance Elicitable T'II'I (->) (T'I'TT'II'T'II'I u uu i ii) where
 elicit = T'II'I T'I'TT'II'T'II'I

instance Elicitable T'I'II (->) (T'I'TT'II'T'II'I u uu i ii) where
 elicit = T'I'II (\(T'I'TT'II'T'II'I x) -> x)

type instance Supertype (T'I'TT'II'I u uu i ii) = u i (uu ii i)

instance Elicitable T'II'I (->) (T'I'TT'II'I u uu i ii)
 where elicit = T'II'I T'I'TT'II'I

instance Elicitable T'I'II (->) (T'I'TT'II'I u uu i ii)
 where elicit = T'I'II (\(T'I'TT'II'I x) -> x)

type instance Supertype (U_I_UT'I'II u uu i ii) = u i (uu i ii)

instance Elicitable T'II'I (->) (U_I_UT'I'II u uu i ii)
 where elicit = T'II'I U_I_UT'I'II

instance Elicitable T'I'II (->) (U_I_UT'I'II u uu i ii)
 where elicit = T'I'II (\(U_I_UT'I'II x) -> x)

type instance Supertype (U_UU_UUU_V_III_I_II_UUUU u uu uuu uuuu v i ii iii) =
 u (uu (v uuu iii i) (v uuu iii ii)) (v uuu iii (uuuu i ii))

instance Elicitable T'I'II (->) (U_UU_UUU_V_III_I_II_UUUU u uu uuu uuuu v i ii iii)
 where elicit = T'I'II (\(U_UU_UUU_V_III_I_II_UUUU x) -> x)

instance Elicitable T'II'I (->) (U_UU_UUU_V_III_I_II_UUUU u uu uuu uuuu v i ii iii)
 where elicit = T'II'I U_UU_UUU_V_III_I_II_UUUU

type instance Supertype (U_V_UU_UUU_UUUU_T'TT'I_II_III u v uu uuu uuuu t tt i ii iii) =
  u (uuu (t i) (tt ii)) (v uu (uuuu i ii) iii)

instance Elicitable T'I'II (->) (U_V_UU_UUU_UUUU_T'TT'I_II_III u v uu uuu uuuu t tt i ii iii_)
 where elicit = T'I'II (\(U_V_UU_UUU_UUUU_T'TT'I_II_III x) -> x)

instance Elicitable T'II'I (->) (U_V_UU_UUU_UUUU_T'TT'I_II_III u v uu uuu uuuu t tt i ii iii_)
 where elicit = T'II'I U_V_UU_UUU_UUUU_T'TT'I_II_III

type instance Supertype (UU_V_T'I'II_T_II v u uu t i ii) = uu (v u ii i) (t i)

instance Elicitable T'I'II (->) (UU_V_T'I'II_T_II v u uu t i ii)
 where elicit = T'I'II (\(UU_V_T'I'II_T_II x) -> x)

instance Elicitable T'II'I (->) (UU_V_T'I'II_T_II v u uu t i ii)
 where elicit = T'II'I UU_V_T'I'II_T_II

type instance Supertype (Recursive f) = f (Recursive f)

instance Elicitable T'I'II (->) (Recursive f)
 where elicit = T'I'II (\(Recursive x) -> x)

instance Elicitable T'II'I (->) (Recursive f)
 where elicit = T'II'I Recursive

type instance Supertype (R_U_I_T_I u t i) = Recursive (T'I'TT'II u t i)

instance Elicitable T'I'II (->) (R_U_I_T_I u t i)
 where elicit = T'I'II (\(R_U_I_T_I x) -> x)

instance Elicitable T'II'I (->) (R_U_I_T_I u t i)
 where elicit = T'II'I R_U_I_T_I

type instance Supertype (U_III_UT'I'II u uu iii i ii) = u i (uu ii iii)

instance Elicitable T'I'II (->) (U_III_UT'I'II u uu iii i ii)
 where elicit = T'I'II (\(U_III_UT'I'II x) -> x)

instance Elicitable T'II'I (->) (U_III_UT'I'II u uu iii i ii)
 where elicit = T'II'I U_III_UT'I'II

type instance Supertype (U_I_UU_III_T'II'I u uu i ii iii) = u i (uu iii (u ii i))

instance Elicitable T'I'II (->) (U_I_UU_III_T'II'I u uu i ii iii)
 where elicit = T'I'II (\(U_I_UU_III_T'II'I x) -> x)

instance Elicitable T'II'I (->) (U_I_UU_III_T'II'I u uu i ii iii)
 where elicit = T'II'I U_I_UU_III_T'II'I

type instance Supertype (W_I_II_II w i ii) = w i ii ii

instance Elicitable T'I'II (->) (W_I_II_II u i ii)
 where elicit = T'I'II (\(W_I_II_II x) -> x)

instance Elicitable T'II'I (->) (W_I_II_II u i ii)
 where elicit = T'II'I W_I_II_II

type instance Supertype (W_I_II_I w i ii) = w i ii i

instance Elicitable T'I'II (->) (W_I_II_I u i ii)
 where elicit = T'I'II (\(W_I_II_I x) -> x)

instance Elicitable T'II'I (->) (W_I_II_I u i ii)
 where elicit = T'II'I W_I_II_I

type instance Supertype (W_II_II_I w i ii) = w ii ii i

instance Elicitable T'I'II (->) (W_II_II_I w i ii)
 where elicit = T'I'II (\(W_II_II_I x) -> x)

instance Elicitable T'II'I (->) (W_II_II_I w i ii)
 where elicit = T'II'I W_II_II_I

type instance Supertype (W_I_I_II w i ii) = w i i ii

instance Elicitable T'I'II (->) (W_I_I_II u i ii)
 where elicit = T'I'II (\(W_I_I_II x) -> x)

instance Elicitable T'II'I (->) (W_I_I_II u i ii)
 where elicit = T'II'I W_I_I_II

type instance Supertype (W_III_I_II w iii i ii) = w i ii iii

instance Elicitable T'I'II (->) (W_III_I_II w iii i ii)
 where elicit = T'I'II (\(W_III_I_II x) -> x)

instance Elicitable T'II'I (->) (W_III_I_II w iii i ii)
 where elicit = T'II'I W_III_I_II

-- type instance Supertype (Arrow i ii) = Arrow i ii

-- instance Elicitable T'II'I (->) (Arrow i ii)
 -- where elicit = T'II'I (\f -> f)

-- instance Elicitable T'I'II (->) (Arrow i ii)
 -- where elicit = T'I'II (\f -> f)

type instance Supertype (Arrow Unit ii) = ii

instance (i ~ Unit) => Elicitable T'II'I (->) (Arrow i ii)
 where elicit = T'II'I (\ii -> (\_ -> ii))

instance (i ~ Unit) => Elicitable T'I'II (->) (Arrow i ii)
 where elicit = T'I'II (\f -> f ())

-- type instance Supertype (Arrow i Void) = Arrow i i

-- instance Elicitable T'II'I (->) (Arrow i Void)
 -- where elicit = T'II'I (\ii -> (\_ -> ii))

-- instance Elicitable T'I'II (->) (Arrow Unit ii)
 -- where elicit = T'I'II (\f -> f ())

unwrap :: forall into i .
 Elicitable T'I'II into i =>
 into i (Supertype i)
unwrap = let T'I'II x = elicit in x

wrap :: forall into i .
 Elicitable T'II'I into i =>
 into (Supertype i) i
wrap = let T'II'I x = elicit in x

-- Category: initial object
data Void

type Unit = ()

pattern Unit = ()

type family Equals a b where
  Equals a b = a ~ b
