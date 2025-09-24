{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE UndecidableInstances #-}
module Ya.Program.Interface.Fieldable where

import Ya.Algebra
import Ya.Operators
import Ya.Program.Patterns
import Ya.Program.Primitive
import Ya.Program.Labels

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
 at (These x xx) = xx `lu` (x `lu`)

instance {-# OVERLAPS #-} Fieldable e ee => Fieldable e (ee `P` eee) where
 at (These x xs) = These
  `li` this `ha` at @e @ee `hv` x
  -- `li` \new -> adjust (Attribute (at @e @ee)) (constant new) x `lu` xs
  `li` that `ha` at @e @ee `hv` x `ho` (`lu` xs)

shaft :: forall tt t i . Side `AR` Supertype ((t `P'T'I'TT'I` (Reverse tt `P'T'I'TT'I` Forward tt)) i `AT` tt i)
shaft x = unwrap `hv______` Scope `hv` at @((Reverse tt `P'T'I'TT'I` Forward tt) i) @((t `P'T'I'TT'I` (Reverse tt `P'T'I'TT'I` Forward tt)) i)
 `ho____` Left `hu__` Scope `hv` at @(Reverse tt i) @((Reverse tt `P'T'I'TT'I` Forward tt) i) `ho_'he` Scope `hv` it @(tt i)
  `la__` Right `hu__` Scope `hv` at @(Forward tt i) @((Reverse tt `P'T'I'TT'I` Forward tt) i) `ho_'he` Scope `hv` it @(tt i)
  `li__` x

focus :: forall t tt i . Supertype ((t `P'T'I'TT'I` (Reverse tt `P'T'I'TT'I` Forward tt)) i `AT` t i)
focus (T'TT'I'TTT'I (These x xs)) = x `lu` T'TT'I'TTT'I `ha` (`lu` xs)

other :: forall t tt i . Supertype ((t `P'T'I'TT'I` (Reverse tt `P'T'I'TT'I` Forward tt)) i `AT` (Reverse tt `P'T'I'TT'I` Forward tt) i)
other (T'TT'I'TTT'I (These x xs)) = xs `lu` T'TT'I'TTT'I `ha` (x `lu`)
