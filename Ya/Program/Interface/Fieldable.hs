{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE UndecidableInstances #-}
module Ya.Program.Interface.Fieldable where

import Ya.Algebra
import Ya.Operators
import Ya.Program.Patterns
import Ya.Program.Primitive

class Fieldable i r where
 field :: Supertype (r `AT` i)

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
 field = mirror

instance Fieldable e (ee `P` e) where
 field (These x xx) = xx `hjd` (x `hjd`)

instance {-# OVERLAPS #-} Fieldable e ee => Fieldable e (ee `P` eee) where
 field (These x xs) = this `ha` field @e @ee `har` x `hjd_` that `ha` field @e @ee `har` x `ho_` (`hjd` xs)
