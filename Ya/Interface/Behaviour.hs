module Ya.Interface.Behaviour where

import Ya.Semantics.Structures
import Ya.Interface.Primitives

pattern Apply :: forall tt t i . t `T` i `AR__` t `L` tt `T` Void `T` i
pattern Apply x = Label @t @tt @Void x

pattern Spark :: forall t i . i `AR__` I `L` t `T` Void `T` i
pattern Spark x = Label (Identity x)

pattern Check :: forall e t i . t i `AR__` t `L` T'I'II (S) e `T` Void `T'I` i
pattern Check x = Label x

pattern Maybe :: forall e i . i `AR__` I `L` T'I'II (S) Unit `T` Void `T'I` i
pattern Maybe x = Label (Identity x)

pattern Forth :: forall tt t i . t i `AR____` t `L` tt `T` (Void) `T` i
pattern Forth x = Label @_ @_ @_ x

pattern Aback :: forall tt t i . t i `AR____` t `L` tt `T` (Void `P` Void) `T` i
pattern Aback x = Label @_ @_ @_ x

pattern Plain :: forall t i . i -> I `L` t `T` (Void) `T` i
pattern Plain i = Label (Identity i)

pattern Stack :: forall t i . i -> I `L` t `T` (Void `P` Void) `T` i
pattern Stack i = Label (Identity i)

pattern Every :: forall i . i `AR__` I `L` T'I'I P `T` (Void) `T` i
pattern Every x = Label @_ @(T'I'I P) @Void (Identity x)

pattern Twice :: forall e i . i `AR__` I `L` T'I'I (P) `T` Void `T'I` i
pattern Twice x = Label (Identity x)

pattern Exist :: forall e t i . t i `AR__` t `L` T'I'II (S) Unit `T` Void `T'I` i
pattern Exist x = Label x
