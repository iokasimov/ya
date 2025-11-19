module Ya.Program.Interface.Stackable where

import Ya.Algebra
import Ya.Operators
import Ya.Program.Patterns
import Ya.Program.Primitive
import Ya.Program.Labels

type family Popped datastructure where
 Popped (Construction Optional) = Optional
 Popped (Optional `T'TT'I` Construction Optional) = Optional

class Stackable datastructure where
 pop :: datastructure item `AR__` Optional item `P` datastructure item
 push :: item -> datastructure item `AR__` item `P` datastructure item

-- TODO: refactor, it's hard to read
instance Stackable List where
 pop = \case
  T'TT'I (T'I'II (This _)) -> Empty Unit `lu` empty @List
  T'TT'I (Exist (Build (Recursive (T'TT'I (T'II'I (These xs x)))))) -> Exist x `lu` (xs `yo` F'T'I'TT'I `yi` T'TT'I)
 push item s = item `lu` rewrap
  (Exist `ha` F'T'I'TT'I `ha` Recursive `ha` T'TT'I `ha` T'II'I `ha` (`lu` item) `ha` (`yo` unwrap @Arrow @(F'T'I'TT'I _ _ _))) s

-- TODO: refactor, it's hard to read
instance Stackable (Construction Optional) where
 pop = \case
  F'T'I'TT'I (Recursive (T'TT'I (T'II'I (These (Exist xs) x)))) -> Exist x `lu` F'T'I'TT'I xs
  F'T'I'TT'I (Recursive (T'TT'I (T'II'I (These (Empty xs) x)))) -> Empty Unit `lu` F'T'I'TT'I (Recursive (T'TT'I (T'II'I (These (Empty xs) x))))
 push x = \old -> These x (Item x `ha` T'I'II `ha` That  `rewrap` old)

pattern Plane :: Stackable t => t i -> t `L` t `T` Void `T` i
pattern Plane i = Label i

pattern Whirl :: Stackable t => t i -> t `L` t `T` (Void `P` Void) `T` i
pattern Whirl i = Label i

pattern Align :: Stackable t => t i -> t `L` t `T` Void `T` i
pattern Align i = Label i

pattern Cross :: Stackable t => t i -> t `L` t `T` (Void `P` Void) `T` i
pattern Cross i = Label i
