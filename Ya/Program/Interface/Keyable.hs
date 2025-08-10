module Ya.Program.Interface.Keyable where

import Ya.Algebra
import Ya.Program.Patterns

class Keyable key datastructure where
 key :: key `AR_` Supertype (Attribute (datastructure item) (Stops key item))
