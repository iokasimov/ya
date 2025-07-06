{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE UndecidableSuperClasses #-}
module Ya.Algebra.Effectful where

import Ya.Algebra.Abstract
import Ya.Algebra.Definition

infixr 7 `JNT`
infixr 6 `JNT_`

type family Jointable effect where
 Jointable (T'I'II (AR) e) = ()
 Jointable (S'I'II e) = ()
 Jointable (T'I'II (U_I_UT'II'I (AR) (P)) e) = ()

type family JNT effect where
 JNT (T'I'II (AR) e) = T'TT'I (T'I'II (AR) e)
 JNT (S'I'II e) = TT'T'I (S'I'II e)
 JNT (T'I'II (U_I_UT'II'I (AR) (P)) e) = T'TTT'TT'I (T'I'II (AR) e) (T'II'I (P) e)

type JNT_ effect = JNT effect

-- class Labeling label effect inside where
