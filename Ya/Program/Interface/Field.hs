module Ya.Program.Interface.Field where

import Ya.Algebra
import Ya.Program.Patterns
import Ya.Program.Primitive
import Ya.Program.Labels

class Field e r where
 at :: Reference P r e e

instance Field e e where
 at = it

instance Field e (ee `P` e) where
 at (These x xx) = xx `lu` (x `lu`)

instance {-# OVERLAPS #-} Field e ee => Field e (ee `P` eee) where
 at (These x xs) = These
  `li` this (at @e @ee `hv` x)
  `li` \new -> adjust (Attribute (at @e @ee)) (constant new) x `lu` xs

shaft :: forall t tt i . Side `AR` Supertype ((t `P'T'I'TT'I` (Reverse tt `P'T'I'TT'I` Forward tt)) i `AT` tt i)
shaft x = unwrap `hv______` Scope `hv` it `ho____'he` Scope `hv` at @((Reverse tt `P'T'I'TT'I` Forward tt) i)
 `ho____'he` Left `hu__` Scope `hv` at @(Reverse tt i) `ho_'he` Scope `hv` it @(tt i)
     `la__` Right `hu__` Scope `hv` at @(Forward tt i) `ho_'he` Scope `hv` it @(tt i)
     `li__` x

focus :: forall t tt i . Supertype ((t `P'T'I'TT'I` (Reverse tt `P'T'I'TT'I` Forward tt)) i `AT` t i)
focus (U_T_I_TT_I (These x xs)) = x `lu` U_T_I_TT_I `ha` (`lu` xs)