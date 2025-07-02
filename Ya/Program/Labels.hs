{-# LANGUAGE AllowAmbiguousTypes #-}
module Ya.Program.Labels where

import Ya.Algebra
import Ya.Program.Patterns

pattern Run, Def, Usual, Default :: t e `AR__` t `L` Void `T'I` e
pattern Run e = Labeled @_ @Void e
pattern Def e = Labeled @_ @Void e
pattern Usual e = Labeled @_ @Void e
pattern Default e = Labeled @_ @Void e

-- TODO: restrict to Scrolling List, Scrolling Tree
pattern Range :: e `AR__` Only `L` Void `T` e
pattern Range x = Labeled (Only x)

pattern First :: t o `AR__` t `L` Void `T` o
pattern First i = Labeled i

pattern Again :: forall e t . t e `AR__` t `L` Recursive `T` e
pattern Again i = Labeled @_ @Recursive i

pattern Check, Try
 :: forall e t .
 t e `AR__` t `L` Void `T'I` e
pattern Check e = Labeled e
pattern Try e = Labeled e

pattern Retry :: forall e t . t e `AR__` t `L` Recursive `T` e
pattern Retry e = Labeled @_ @Recursive e

type Forward t = t `L` Void

type Reverse t = t `L` (Void `P` Void)

pattern Forth e = Labeled @_ @Void e
pattern Prior e = Labeled @_ @(Void `P` Void) e

pattern New e = Labeled @(State _) @Void e
pattern Old e = Labeled @(State _) @(Void `P` Void) e

pattern Every :: forall i ii iii e .
 Component (AR) (Covariant Day (AR) (P) (P) (T'I'II (S) iii) (T'I'II (S) iii `L` Void) i ii) (T'I'II (S) iii) =>
 T'I'II (S) i e `AR__` T'I'II (S) i `L` Void `T` e
pattern Every x = Labeled @_ @Void x

pattern Prune :: forall i e .
 Component (AR) (T'I'II (S) i) (T'I'II (S) Unit) =>
 T'I'II (S) i e `AR__` T'I'II (S) i `L` (Void `P` Void) `T` e
pattern Prune x = Labeled @_ @(Void `P` Void) x
