module Ya.Program.Interface.Stack where

import Ya.Algebra
import Ya.Program.Patterns
import Ya.Program.Primitive
import Ya.Program.Labels

type family Popped datastructure where
 Popped (Construction Optional) = Optional
 Popped (Optional `T'TT'I` Construction Optional) = Optional

class Stack datastructure where
 pop :: Automation `WR` datastructure item `WR` Supertype (Popped datastructure item) `WR` datastructure item
 push :: item -> Automation `WR` datastructure item `WR` item `WR` datastructure item

-- TODO: refactor, it's hard to read
instance Stack List where
 pop = \case
  Empty @List _ -> This () `lu` Empty @List ()
  T'TT'I (Some (Construct (Recursive (U_I_T_II (These x xs))))) -> That x `lu` (T'TT'I / xs `yo` R_U_I_T_I)
 push item s = item `lu` rewrap
  (Some `ha` R_U_I_T_I `ha` Recursive `ha` U_I_T_II `ha` These item `ha` (`yo` unwrap @Arrow @(R_U_I_T_I _ _ _))) s

-- TODO: refactor, it's hard to read
instance Stack (Construction Optional) where
 pop = \case
  R_U_I_T_I (Recursive (U_I_T_II (These x (Some xs)))) -> That x `lu` R_U_I_T_I xs
  R_U_I_T_I (Recursive (U_I_T_II (These x (None xs)))) -> by This `lu` R_U_I_T_I (Recursive (U_I_T_II (These x (None xs))))
 push x = \old -> These x (Item x `ha` Next  `rewrap` old)
