{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE UndecidableSuperClasses #-}
module Ya.Algebra.Effectful where

import Ya.Algebra.Abstract
import Ya.Algebra.Definition

infixl 7 `J'T'TT'I`

type family J'T'TT'I inner effect where
 J'T'TT'I inner (T'I'II (AR) e) = T'TT'I (T'I'II (AR) e) inner
 J'T'TT'I inner (S'I'II e) = TT'T'I (S'I'II e) inner
 J'T'TT'I inner (T'I'II (T'I'TT'II'I (AR) (P)) e) = T'TTT'TT'I (T'I'II (AR) e) (T'II'I (P) e) inner

type JNT_ inner effect = J'T'TT'I inner effect

type Jointed outer inner = J'T'TT'I inner outer
