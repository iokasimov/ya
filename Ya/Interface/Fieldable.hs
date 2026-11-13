{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE UndecidableInstances #-}
module Ya.Interface.Fieldable where

import Ya.Semantics
import Ya.Operators

class Fieldable i r where
 record :: Supertype (r `AT` i)

instance {-# OVERLAPPABLE #-}
 ( Covariant Objective (AR) ee (eee `P` eeee)
 , Contravariant Objective (AR) ee (eee `P` eeee)
 , Fieldable e (eee `P` eeee)
 ) => Fieldable e ee where
 record = (fio @(AR) `compose` fio @(AR))
   (objective @T'II'I @AR @ee @(eee `P` eeee))
  `compose` record @e @(eee `P` eeee)
  `compose` objective @T'I'II @AR @ee @(eee `P` eeee)

instance Fieldable e e where
 record x = These x identity

instance Fieldable e (ee `P` e) where
 record (These x xx) = These xx (These x)

instance {-# OVERLAPS #-} Fieldable e ee => Fieldable e (ee `P` eee) where
 record (These x xs) = (this `ha` record @e @ee `ha'nt'ha` x) `These` (that `ha` record @e @ee `ha'nt'ha` x `ho_` (`These` xs))
