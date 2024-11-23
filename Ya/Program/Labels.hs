module Ya.Program.Labels where

import Ya.Algebra
import Ya.Program.Patterns

pattern Def e = Labeled @() e
pattern Usual e = Labeled @() e
pattern Default e = Labeled @() e

type Cascading = L (Straight LM () ())

pattern Cascading :: t e -> Cascading t e
pattern Cascading e = Labeled e

type Repeating = L (U_I_I LM ())

pattern Again :: t e -> Repeating t e
pattern Again e = Labeled e

pattern Try e = Labeled @() e

pattern Check e = Labeled @() e

pattern Retry e = Labeled @(() `LM` ()) e

type Fore = U_I_II ML () ()

type Back = U_II_I ML () ()

type Forward = L Fore

pattern Forward :: t e -> Forward t e
pattern Forward e = Labeled e

type Reverse = L Back

pattern Reverse :: t e -> Reverse t e
pattern Reverse e = Labeled e

pattern Forth :: t e -> Forward t e
pattern Forth e = Labeled e

pattern Prior :: t e -> Reverse t e
pattern Prior e = Labeled e

pattern Use :: t e -> L (U_I_II ML () ()) t e
pattern Use e = Labeled e

-- pattern Usual :: t e -> L (U_I_II ML () ()) t e
-- pattern Usual e = Labeled e

pattern New e = Labeled @() @(State _) e

pattern Old e = Labeled @(() `LM` ()) @(State _) e
