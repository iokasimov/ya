{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE UndecidableInstances #-}
module Ya.Program.Interface.Fieldable where

import Ya.Algebra
import Ya.Operators
import Ya.Program.Patterns
import Ya.Program.Primitive

class Fieldable e r where
 at :: Reference (P) r e e

instance {-# OVERLAPPABLE #-}
 ( Covariant Objective (AR) ee (eee `P` eeee)
 , Contravariant Objective (AR) ee (eee `P` eeee)
 , Fieldable e (eee `P` eeee)
 ) => Fieldable e ee where
 at = (fio @(AR) `compose` fio @(AR))
   (objective @T'II'I @AR @ee @(eee `P` eeee))
  `compose` at @e @(eee `P` eeee)
  `compose` objective @T'I'II @AR @ee @(eee `P` eeee)

instance Fieldable e e where
 at = it

instance Fieldable e (ee `P` e) where
 at (These x xx) = xx `hjd` (x `hjd`)

instance {-# OVERLAPS #-} Fieldable e ee => Fieldable e (ee `P` eee) where
 at (These x xs) = These
  `li` this `ha` at @e @ee `hv` x
  `li` that `ha` at @e @ee `hv` x `ho` (`hjd` xs)
