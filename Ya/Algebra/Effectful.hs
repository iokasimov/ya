{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE UndecidableSuperClasses #-}
module Ya.Algebra.Effectful where

import Ya.Algebra.Abstract
import Ya.Algebra.Definition

infixl 6 `J'T'TT'I`

type family Jointed outer where
 Jointed (T'I'II (AR) e) = T'TT'I (T'I'II (AR) e)
 Jointed (S'I'II e) = TT'T'I (S'I'II e)
 Jointed (T'I'II (T'I'TT'II'I (AR) (P)) e) = T'TTT'TT'I (T'I'II (AR) e) (T'II'I (P) e)

type J'T'TT'I inner outer = Jointed outer inner
