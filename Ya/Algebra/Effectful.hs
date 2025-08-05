{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE UndecidableSuperClasses #-}
module Ya.Algebra.Effectful where

import Ya.Algebra.Abstract
import Ya.Algebra.Definition

infixl 7 `JNT`
infixl 6 `JNT_`

type family JNT inner effect where
 JNT inner (T'I'II (AR) e) = T'TT'I (T'I'II (AR) e) inner
 JNT inner (S'I'II e) = TT'T'I (S'I'II e) inner
 JNT inner (T'I'II (T'I'TT'II'I (AR) (P)) e) = T'TTT'TT'I (T'I'II (AR) e) (T'II'I (P) e) inner

type JNT_ inner effect = JNT inner effect
