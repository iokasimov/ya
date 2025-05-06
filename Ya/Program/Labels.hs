module Ya.Program.Labels where

import Ya.Algebra
import Ya.Program.Patterns

pattern Run, Def, Usual, Default :: t e `AR__` L Void t e
pattern Run e = Labeled @Void e
pattern Def e = Labeled @Void e
pattern Usual e = Labeled @Void e
pattern Default e = Labeled @Void e

-- TODO: restrict to Scrolling List, Scrolling Tree
pattern Range :: e `AR__` (Void `L` Only) e
pattern Range x = Labeled (Only x)

pattern First :: Progress i o `AR__` Void `L` Progress i `T'I` o
pattern First i = Labeled i

pattern Again :: forall t i . t i `AR__` L Recursive t i
pattern Again i = Labeled @Recursive i

pattern Try :: forall e ee . Error e ee `AR__` Void `L` Error e `T'I` ee
pattern Try e = Labeled e

pattern Check :: forall e ee . Error e ee `AR__` Void `L` Error e `T'I` ee
pattern Check e = Labeled e

pattern Retry :: forall ee e . Error e ee `AR__` L Recursive (Error e) ee
pattern Retry e = Labeled @Recursive e

type Fore = T'I'II S () ()

type Back = U_II_I S () ()

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

pattern Use :: t e `AR__` L (T'I'II S Void Void) t e
pattern Use e = Labeled e

pattern New e = Labeled @Void @(State _) e

pattern Old e = Labeled @(Void `P` Void) @(State _) e
