{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE UndecidableInstances #-}
module Ya.Program.Interface.Fieldable where

import Ya.Algebra
import Ya.Operators
import Ya.Program.Patterns
import Ya.Program.Primitive

class Fieldable e r where
 field :: Reference (P) r e e

instance {-# OVERLAPPABLE #-}
 ( Covariant Objective (AR) ee (eee `P` eeee)
 , Contravariant Objective (AR) ee (eee `P` eeee)
 , Fieldable e (eee `P` eeee)
 ) => Fieldable e ee where
 field = (fio @(AR) `compose` fio @(AR))
   (objective @T'II'I @AR @ee @(eee `P` eeee))
  `compose` field @e @(eee `P` eeee)
  `compose` objective @T'I'II @AR @ee @(eee `P` eeee)

instance Fieldable e e where
 field = it

instance Fieldable e (ee `P` e) where
 field (These x xx) = xx `hjd` (x `hjd`)

instance {-# OVERLAPS #-} Fieldable e ee => Fieldable e (ee `P` eee) where
 field (These x xs) = this `ha` field @e @ee `hc` x `hjd_` that `ha` field @e @ee `hc` x `ho` (`hjd` xs)