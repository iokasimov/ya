{-# LANGUAGE AllowAmbiguousTypes #-}
module Ya.Program.Labels where

import Ya.Algebra
import Ya.Program.Patterns

pattern Run, Def, Apply, Usual, Default :: t e `AR__` t `L` tt `T` Void `T` e
pattern Run e = Labeled @_ @_ @Void e
pattern Def e = Labeled @_ @_ @Void e
pattern Apply e = Labeled @_ @_ @Void e
pattern Usual e = Labeled @_ @_ @Void e
pattern Default e = Labeled @_ @_ @Void e

pattern First :: t o `AR__` t `L` tt `T` Void `T` o
pattern First i = Labeled i

pattern Again :: forall e t tt . t e `AR__` t `L` tt `T` Recursive `T` e
pattern Again i = Labeled @_ @_ @Recursive i

pattern Check, Try
 :: forall e i t .
 t e `AR__` t `L` S'I'II i `T` Void `T'I` e
pattern Check e = Labeled e
pattern Try e = Labeled e

pattern Retry :: forall e i t . t e `AR__` t `L` S'I'II i `T` Recursive `T` e
pattern Retry e = Labeled @_ @_ @Recursive e

pattern Until :: forall i e t . t e `AR__` t `L` S'I'II i `T` Recursive `T` e
pattern Until e = Labeled @_ @_ @Recursive e

type Forward t = t `L` t `T` Void
type Reverse t = t `L` t `T` (Void `P` Void)

pattern Forth e = Labeled @_ @_ @Void e
pattern Prior e = Labeled @_ @_ @(Void `P` Void) e

pattern New e = Labeled @(State _) @(State _) @Void e
pattern Old e = Labeled @(State _) @(State _) @(Void `P` Void) e

pattern Lease e = Labeled @(State _) @(State _) @(Void `P` Void) e

pattern Every :: forall i ii iii e .
 Component (AR) (Covariant Day (AR) (P) (P) (S'I'II iii) (S'I'II iii `L` S'I'II iii `T` Void) i ii) (S'I'II iii) =>
 S'I'II iii e `AR__` S'I'II iii `L` S'I'II iii `T` Void `T` e
pattern Every x = Labeled @_ @_ @Void x
