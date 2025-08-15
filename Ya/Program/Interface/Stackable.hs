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
  Empty @List _ -> by None `lu` Empty @List ()
  T'TT'I (Some (Construct (Recursive (T'I'TT'II (These x xs))))) -> Some x `lu` (xs `yo` R_U_I_T_I `yi` T'TT'I)
 push item s = item `lu` rewrap
  (Some `ha` R_U_I_T_I `ha` Recursive `ha` T'I'TT'II `ha` These item `ha` (`yo` unwrap @Arrow @(R_U_I_T_I _ _ _))) s

-- TODO: refactor, it's hard to read
instance Stackable (Construction Optional) where
 pop = \case
  R_U_I_T_I (Recursive (T'I'TT'II (These x (Some xs)))) -> Some x `lu` R_U_I_T_I xs
  R_U_I_T_I (Recursive (T'I'TT'II (These x (None xs)))) -> by None `lu` R_U_I_T_I (Recursive (T'I'TT'II (These x (None xs))))
 push x = \old -> These x (Item x `ha` Next  `rewrap` old)

pattern Plane :: Stackable t => t i -> t `L` t `T` Void `T` i
pattern Plane i = Labeled i

pattern Whirl :: Stackable t => t i -> t `L` t `T` (Void `P` Void) `T` i
pattern Whirl i = Labeled i

pattern Align :: Stackable t => t i -> t `L` t `T` Void `T` i
pattern Align i = Labeled i

pattern Cross :: Stackable t => t i -> t `L` t `T` (Void `P` Void) `T` i
pattern Cross i = Labeled i
