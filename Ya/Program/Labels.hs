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

type Fore = T'I'II (S) () ()

type Back = T'II'I (S) () ()

type Forward = L Void

type Reverse = L (Void `P` Void)

pattern Forward :: t e `AR__` Void `L` t `T'I` e
pattern Forward e = Labeled e

pattern Reverse :: t e `AR__` (Void `P` Void) `L` t `T'I` e
pattern Reverse e = Labeled e

pattern Forth :: t e `AR__` Void `L` t `T'I` e
pattern Forth e = Labeled e

pattern Prior :: t e `AR__` (Void `P` Void) `L` t `T'I` e
pattern Prior e = Labeled e

pattern New e = Labeled @Void e

pattern Old e = Labeled @(Void `P` Void) e
