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
  T'TT'I (Some (Construct (Recursive (U_I_T_II (These x xs))))) -> Some x `lu` (T'TT'I / xs `yo` R_U_I_T_I)
 push item s = item `lu` rewrap
  (Some `ha` R_U_I_T_I `ha` Recursive `ha` U_I_T_II `ha` These item `ha` (`yo` unwrap @Arrow @(R_U_I_T_I _ _ _))) s

-- TODO: refactor, it's hard to read
instance Stackable (Construction Optional) where
 pop = \case
  R_U_I_T_I (Recursive (U_I_T_II (These x (Some xs)))) -> Some x `lu` R_U_I_T_I xs
  R_U_I_T_I (Recursive (U_I_T_II (These x (None xs)))) -> by None `lu` R_U_I_T_I (Recursive (U_I_T_II (These x (None xs))))
 push x = \old -> These x (Item x `ha` Next  `rewrap` old)

pattern Plane :: Stackable t => t i -> (Void `L` t) i
pattern Plane i = Labeled i

pattern Align :: Stackable t => t i -> (Void `L` t) i
pattern Align i = Labeled i

pattern Cross :: Stackable t => t i -> ((Void `P` Void) `L` t) i
pattern Cross i = Labeled i
