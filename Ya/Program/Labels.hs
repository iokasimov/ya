{-# LANGUAGE AllowAmbiguousTypes #-}
module Ya.Program.Labels where

import Ya.Algebra
import Ya.Program.Patterns

pattern Apply :: forall tt t i . t `T` i `AR__` t `L` tt `T` Void `T` i
pattern Apply x = Label @t @tt @Void x

pattern First :: forall t e i . t i `AR__` t `L` T'I'II (S) e `T` Void `T` i
pattern First x = Label x

pattern Again :: forall e t . e `AR__` Alone `L` t `T` Recursive `T` e
pattern Again x = Label @_ @_ @Recursive (Alone x)

pattern Check :: forall e t i . t i `AR__` t `L` S'I'II e `T` Void `T'I` i
pattern Check x = Label x

pattern Retry :: forall t i e . t i `AR__` t `L` S'I'II e `T` Recursive `T` i
pattern Retry x = Label @_ @_ @Recursive x

pattern Until :: forall e i t . t i `AR__` t `L` S'I'II e `T` Void `T` i
pattern Until x = Label @_ @_ @Void x

-- pattern Allot :: forall e t i . t i `AR_____` t `L` State e `T` (Void) `T` i
-- pattern Allot e = Label @_ @(State _) @(Void) e

pattern Lease :: forall e t i . t i `AR_____` t `L` State e `T` (Void `P` Void) `T` i
pattern Lease e = Label @_ @(State _) @(Void `P` Void) e

pattern Every :: forall i ii iii e .
 Component (AR) (Covariant Day (AR) (P) (P) (S'I'II iii) (S'I'II iii `L` S'I'II iii `T` Void) i ii) (S'I'II iii) =>
 S'I'II iii e `AR__` S'I'II iii `L` S'I'II iii `T` Void `T` e
pattern Every x = Label @_ @_ @Void x

pattern Level :: forall t i . i `AR__` Alone `L` t `T` Void `T` i
pattern Level x = Label (Alone x)

pattern Claim :: forall i t ii . t ii `AR__` t `L` T'I'II (AR) i `T` (Void) `T` ii
pattern Claim x = Label x
