module Ya.Program.Labels where

import Ya.Algebra
import Ya.Program.Patterns

pattern Run, Def, Usual, Default :: t e -> L Unit t e
pattern Run e = Labeled @Unit e
pattern Def e = Labeled @Unit e
pattern Usual e = Labeled @Unit e
pattern Default e = Labeled @Unit e

type Cascading = L (() `P` ())

pattern Cascading :: List i -> Cascading List i
pattern Cascading i = Labeled i

-- TODO: restrict to Lists, Nonempty Lists
pattern Align :: t i -> (Unit `L` t) i
pattern Align i = Labeled i

-- TODO: restrict to Lists, Nonempty Lists
pattern Cross :: t i -> ((Void `P` Void) `L` t) i
pattern Cross i = Labeled i

type First = L (Unit)

pattern First :: Progress i o -> First (Progress i) o
pattern First i = Labeled i

pattern Again :: forall t i . t i -> L Recursive t i
pattern Again i = Labeled @Recursive i

pattern Try :: forall e ee . Error e ee -> L Unit (Error e) ee
pattern Try e = Labeled @() e

pattern Check :: forall e ee . Error e ee -> L Unit (Error e) ee
pattern Check e = Labeled @() e

pattern Retry :: forall ee e . Error e ee -> L Recursive (Error e) ee
pattern Retry e = Labeled @Recursive e

type Fore = U_I_II S () ()

type Back = U_II_I S () ()

type Forward = L Unit

pattern Forward :: t e -> Forward t e
pattern Forward e = Labeled e

type Reverse = L (Unit `P` Unit)

pattern Reverse :: t e -> Reverse t e
pattern Reverse e = Labeled e

pattern Forth :: t e -> Forward t e
pattern Forth e = Labeled e

pattern Prior :: t e -> Reverse t e
pattern Prior e = Labeled e

pattern Use :: t e -> L (U_I_II S () ()) t e
pattern Use e = Labeled e

pattern New e = Labeled @() @(State _) e

pattern Old e = Labeled @(() `P` ()) @(State _) e
