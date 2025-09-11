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
 pop :: Automation `T'I` datastructure item `T'I` Optional item `T'I` datastructure item
 push :: item -> Automation `T'I` datastructure item `T'I` item `T'I` datastructure item

-- TODO: refactor, it's hard to read
instance Stackable List where
 pop = \case
  T'TT'I (T'I'II (This _)) -> by Empty `lu` empty @List
  T'TT'I (Exist (Construct (Recursive (T'I'TT'II (These x xs))))) -> Exist x `lu` (xs `yo` R_U_I_T_I `yi` T'TT'I)
 push item s = item `lu` rewrap
  (Exist `ha` R_U_I_T_I `ha` Recursive `ha` T'I'TT'II `ha` These item `ha` (`yo` unwrap @Arrow @(R_U_I_T_I _ _ _))) s

-- TODO: refactor, it's hard to read
instance Stackable (Construction Optional) where
 pop = \case
  R_U_I_T_I (Recursive (T'I'TT'II (These x (Exist xs)))) -> Exist x `lu` R_U_I_T_I xs
  R_U_I_T_I (Recursive (T'I'TT'II (These x (Empty xs)))) -> by Empty `lu` R_U_I_T_I (Recursive (T'I'TT'II (These x (Empty xs))))
 push x = \old -> These x (Item x `ha` Next  `rewrap` old)

pattern Plane :: Stackable t => t i -> t `L` t `T` Void `T` i
pattern Plane i = Label i

pattern Whirl :: Stackable t => t i -> t `L` t `T` (Void `P` Void) `T` i
pattern Whirl i = Label i

pattern Align :: Stackable t => t i -> t `L` t `T` Void `T` i
pattern Align i = Label i

pattern Cross :: Stackable t => t i -> t `L` t `T` (Void `P` Void) `T` i
pattern Cross i = Label i
