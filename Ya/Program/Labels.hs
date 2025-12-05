{-# LANGUAGE AllowAmbiguousTypes #-}
module Ya.Program.Labels where

import Ya.Algebra
import Ya.Program.Patterns

pattern Apply :: t e `AR__` t `L` tt `T` Void `T` e
pattern Apply e = Label @_ @_ @Void e

pattern First :: t ii `AR__` t `L` T'I'II (S) i `T` Void `T` ii
pattern First x = Label x

pattern Again :: forall e t . e `AR__` Alone `L` t `T` Recursive `T` e
pattern Again i = Label @_ @_ @Recursive (Alone i)

pattern Check, Try
 :: forall e i t .
 t e `AR__` t `L` S'I'II i `T` Void `T'I` e
pattern Check e = Label e
pattern Try e = Label e

pattern Retry :: forall e i t . t e `AR__` t `L` S'I'II i `T` Recursive `T` e
-- pattern Retry :: forall t tt e . t e `AR__` t `L` tt ` Recursive `T` e
pattern Retry e = Label @_ @_ @Recursive e

pattern Until :: forall i e t . t e `AR__` t `L` S'I'II i `T` Void `T` e
pattern Until e = Label @_ @_ @Void e

type Forward t = t `L` t `T` Void
type Reverse t = t `L` t `T` (Void `P` Void)

-- TODO: make this label type-safe
pattern Forth :: forall t tt ttt ll i . tt `L` ttt `T` ll `T` i `AR____` tt `L` ttt `T` ll `L` t `T` Void `T` i
pattern Forth x = Label @_ @_ @Void x

pattern Prior :: forall t tt ttt ll i . tt `L` ttt `T` ll `T` i `AR____` tt `L` ttt `T` ll `L` t `T` (Void `P` Void) `T` i
pattern Prior x = Label @_ @_ @(Void `P` Void) x

pattern New e = Label @(State _) @(State _) @Void e
pattern Old e = Label @(State _) @(State _) @(Void `P` Void) e

pattern Lease e = Label @(State _) @(State _) @(Void `P` Void) e

pattern Every :: forall i ii iii e .
 Component (AR) (Covariant Day (AR) (P) (P) (S'I'II iii) (S'I'II iii `L` S'I'II iii `T` Void) i ii) (S'I'II iii) =>
 S'I'II iii e `AR__` S'I'II iii `L` S'I'II iii `T` Void `T` e
pattern Every x = Label @_ @_ @Void x

pattern Level :: forall t i . i `AR__` Alone `L` t `T` Void `T` i
pattern Level x = Label (Alone x)
