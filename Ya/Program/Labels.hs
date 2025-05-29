{-# LANGUAGE AllowAmbiguousTypes #-}
module Ya.Program.Labels where

import Ya.Algebra
import Ya.Program.Patterns

pattern Run, Def, Usual, Default :: t e `AR__` Void `L` t `T'I` e
pattern Run e = Labeled @Void e
pattern Def e = Labeled @Void e
pattern Usual e = Labeled @Void e
pattern Default e = Labeled @Void e

-- TODO: restrict to Scrolling List, Scrolling Tree
pattern Range :: e `AR__` Void `L` Only `T'I` e
pattern Range x = Labeled (Only x)

pattern First :: t o `AR__` Void `L` t `T'I` o
pattern First i = Labeled i

pattern Again :: forall e t . t e `AR__` Recursive `L` t `T'I` e
pattern Again i = Labeled @Recursive i

pattern Check, Try
 :: forall e t .
 t e `AR__` Void `L` t `T'I` e
pattern Check e = Labeled e
pattern Try e = Labeled e

pattern Retry :: forall e t . t e `AR__` Recursive `L` t `T'I` e
pattern Retry e = Labeled @Recursive e

type Forward = L Void

type Reverse = L (Void `P` Void)

pattern Forth e = Labeled @Void e
pattern Prior e = Labeled @(Void `P` Void) e

pattern New e = Labeled @Void @(State _) e
pattern Old e = Labeled @(Void `P` Void) @(State _) e

pattern Every :: forall i ii iii e .
 Component (AR) (Covariant Day (AR) (P) (P) (T'I'II (S) iii) (Void `L` T'I'II (S) iii) i ii) (T'I'II (S) iii) =>
 T'I'II (S) i e `AR__` Void `L` T'I'II (S) i `T'I` e
pattern Every x = Labeled @Void x

pattern Prune :: forall i e .
 Component (AR) (T'I'II (S) i) (T'I'II (S) Unit) =>
 T'I'II (S) i e `AR__` (Void `P` Void) `L` T'I'II (S) i `T'I` e
pattern Prune x = Labeled @(Void `P` Void) x