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
