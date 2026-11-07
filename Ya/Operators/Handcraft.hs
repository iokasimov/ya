{-# LANGUAGE AllowAmbiguousTypes #-}
module Ya.Operators.Handcraft where

import Ya.Semantics

infixl 8 `fo`
infixl 7 `fio`, `foi`, `foo`, `fok`, `fia`, `fai`, `faa`, `fak`, `kfo`, `kfa`
infixl 6 `fiok`, `foik`, `fiak`, `faik`, `kfio`, `kfoi`, `kfia`, `kfai`, `fokl`, `fakl`, `fo'nt'fo`, `fa'nt'fa`
infixl 5 `fiokl`, `foikl`, `fiakl`, `faikl`, `fio'nt'fo`, `foi'nt'fo`, `fia'nt'fa`, `fai'nt'fa`
infixl 4 `fio'nt'fio`, `foo'nt'fio`, `fo'dc'fo'nt'fo`, `fa'dc'fa'nt'fa`, `fo'nt'fo'dc'fo`

fo :: forall source target t a o .
 Covariant Semi Functor source target t =>
 source a o -> target (t a) (t o)
fo = map @T'I'II @source @target @t

foi :: forall source target t a o i .
 Covariant Semi Functor source target (T'II'I t i) =>
 (forall e . Wrapper target (T'II'I t i e)) =>
 source a o -> target (t a i) (t o i)
foi = wrapped `compose` fo @source @target @(T'II'I t _)

fio :: forall source target t a o i .
 Covariant Semi Functor source target (T'I'II t i) =>
 (forall e . Wrapper target (T'I'II t i e)) =>
 source a o -> target (t i a) (t i o)
fio = wrapped `compose` fo @source @target @(T'I'II t _)

foo :: forall source target t a o .
 Covariant Semi Functor source target (T'I'I t) =>
 (forall e . Wrapper target (T'I'I t e)) =>
 source a o -> target (t a a) (t o o)
foo = wrapped `compose` fo @_ @_ @(T'I'I _)

fa :: forall source target t a o .
 Contravariant Semi Functor source target t =>
 source a o -> target (t o) (t a)
fa = map @T'II'I

faa :: forall source target t a o .
 Contravariant Semi Functor source target (T'I'I t) =>
 (forall e . Wrapper target (T'I'I t e)) =>
 source a o -> target (t o o) (t a a)
faa = wrapped `compose` fa @source @target @(T'I'I _)

fai :: forall source target t a o i .
 Contravariant Semi Functor source target (T'II'I t i) =>
 (forall e . Wrapper target (T'II'I t i e)) =>
 source a o -> target (t o i) (t a i)
fai = wrapped `compose` fa @source @target @(T'II'I _ _)

fia :: forall source target t a o i .
 Contravariant Semi Functor source target (T'I'II t i) =>
 (forall e . Wrapper target (T'I'II t i e)) =>
 source a o -> target (t i o) (t i a)
fia = wrapped `compose` fa @source @target @(T'I'II _ _)

fok :: forall source target t tt l a o .
 Component target (t `T'TT'I` tt `L` tt `T` l) t =>
 Covariant Functor source target t =>
 (forall e . Wrapper target (t `T'TT'I` tt `L` tt `T` l `T'I_` e)) =>
 source a (tt `L` tt `T` l `T` o) -> target (t a) (t o)
fok = fio (component @target @(t `T'TT'I` tt `L` tt `T` l) @t `compose` subtype) `compose` fo

fiok :: forall source target t tt l i a o .
 Component target (T'I'II t i `T'TT'I` tt `L` tt `T` l) (T'I'II t i) =>
 Covariant Functor source target (T'I'II t i) =>
 (forall e . Wrapper target (T'I'II t i e)) =>
 (forall e . Wrapper target (T'I'II t i `T'TT'I` tt `L` tt `T` l `T'I_` e)) =>
 source a (tt `L` tt `T` l `T` o) -> target (t i a) (t i o)
fiok = wrapped `compose` fok @source @target @(T'I'II t _)

foik :: forall source target t tt l i a o .
 Component target (T'II'I t i `T'TT'I` tt `L` tt `T` l) (T'II'I t i) =>
 Covariant Functor source target (T'II'I t i) =>
 (forall e . Wrapper target (T'II'I t i e)) =>
 (forall e . Wrapper target (T'II'I t i `T'TT'I` tt `L` tt `T` l `T'I_` e)) =>
 source a (tt `L` tt `T` l `T` o) -> target (t a i) (t o i)
foik = wrapped `compose` fok @source @target @(T'II'I t _)

fak :: forall source target t tt l a o .
 Component target (t `T'TT'I` tt `L` tt `T` l) t =>
 Contravariant Functor source target t =>
 Supertyping source (tt `L` tt `T` l `T` o) =>
 Supertyping source (I `L` tt `T` l `T` a) =>
 Supertyping source (I `T` a) =>
 (forall e . Wrapper target (t `T'TT'I` tt `L` tt `T` l `T'I_` e)) =>
 source (tt o) (I `L` tt `T` l `T` a) -> target (t a) (t o)
fak source = component @target @(t `T'TT'I` tt `L` tt `T` l) @t
 `compose` subtype `compose` fa (supertype `compose` supertype `compose` source `compose` supertype)

fiak :: forall source target t tt l i a o .
 Component target (T'I'II t i `T'TT'I` tt `L` tt `T` l) (T'I'II t i) =>
 Contravariant Functor source target (T'I'II t i) =>
 Supertyping source (tt `L` tt `T` l `T` o) =>
 Supertyping source (I `L` tt `T` l `T` a) =>
 Supertyping source (I `T` a) =>
 (forall e . Wrapper target (T'I'II t i e)) =>
 (forall e . Wrapper target (T'I'II t i `T'TT'I` tt `L` tt `T` l `T'I_` e)) =>
 source (tt o) (I `L` tt `T` l `T` a) -> target (t i a) (t i o)
fiak = wrapped `compose` fak @source @target @(T'I'II t _)

faik :: forall source target t tt l i a o .
 Component target (T'II'I t i `T'TT'I` tt `L` tt `T` l) (T'II'I t i) =>
 Contravariant Functor source target (T'II'I t i) =>
 Supertyping source (tt `L` tt `T` l `T` o) =>
 Supertyping source (I `L` tt `T` l `T` a) =>
 Supertyping source (I `T` a) =>
 (forall e . Wrapper target (T'II'I t i e)) =>
 (forall e . Wrapper target (T'II'I t i `T'TT'I` tt `L` tt `T` l `T'I_` e)) =>
 source (tt o) (I `L` tt `T` l `T` a) -> target (t a i) (t o i)
faik = wrapped `compose` fak @source @target @(T'II'I t _)

kfo :: forall source target t tt ll a o .
 Component target t (t `T'TT'I` tt `L` tt `T` ll) =>
 Covariant Functor source target t =>
 (forall e . Wrapper source (I e)) =>
 (forall e . Wrapper source (I `L` tt `T` ll `T` e)) =>
 (forall e . Wrapper source (tt `L` tt `T` ll `T` e)) =>
 (forall e . Wrapper target (t `T'TT'I` tt `L` tt `T` ll `T'I_` e)) =>
 source (tt a) (I `L` tt `T` ll `T` o) -> target (t a) (t o)
kfo source = fo (supertype `compose` supertype `compose` source `compose` supertype)
 `compose` supertype `compose` component @target @t @(t `T'TT'I` tt `L` tt `T` ll)

kfio :: forall source target t tt ll i a o .
 Component target (T'I'II t i) (T'I'II t i `T'TT'I` tt `L` tt `T` ll) =>
 Covariant Functor source target (T'I'II t i) =>
 (forall e . Wrapper source (I e)) =>
 (forall e . Wrapper source (I `L` tt `T` ll `T` e)) =>
 (forall e . Wrapper source (tt `L` tt `T` ll `T` e)) =>
 (forall e . Wrapper target (T'I'II t i `T'TT'I` tt `L` tt `T` ll `T'I_` e)) =>
 (forall e . Wrapper target (T'I'II t i `T'I_` e)) =>
 source (tt a) (I `L` tt `T` ll `T` o) -> target (t i a) (t i o)
kfio source = fio (supertype `compose` supertype `compose` source `compose` supertype)
 `compose` supertype `compose` supertype `compose` component @target @(T'I'II t i) @(T'I'II t i `T'TT'I` tt `L` tt `T` ll) `compose` subtype

kfoi :: forall source target t tt ll i a o .
 Component target (T'II'I t i) (T'II'I t i `T'TT'I` tt `L` tt `T` ll) =>
 Covariant Functor source target (T'II'I t i) =>
 (forall e . Wrapper source (I e)) =>
 (forall e . Wrapper source (I `L` tt `T` ll `T` e)) =>
 (forall e . Wrapper source (tt `L` tt `T` ll `T` e)) =>
 (forall e . Wrapper target (T'II'I t i `T'TT'I` tt `L` tt `T` ll `T'I_` e)) =>
 (forall e . Wrapper target (T'II'I t i `T'I_` e)) =>
 source (tt a) (I `L` tt `T` ll `T` o) -> target (t a i) (t o i)
kfoi source = foi (supertype `compose` supertype `compose` source `compose` supertype)
 `compose` supertype `compose` supertype `compose` component @target @(T'II'I t i) @(T'II'I t i `T'TT'I` tt `L` tt `T` ll) `compose` subtype

kfa :: forall source target t tt ll a o .
 Component target t (t `T'TT'I` tt `L` tt `T` ll) =>
 Contravariant Functor source target t =>
 (forall e . Wrapper source (I e)) =>
 (forall e . Wrapper source (I `L` tt `T` ll `T` e)) =>
 (forall e . Wrapper source (tt `L` tt `T` ll `T` e)) =>
 (forall e . Wrapper target (t `T'TT'I` tt `L` tt `T` ll `T'I_` e)) =>
 source o (tt `L` tt `T` ll `T` a) -> target (t a) (t o)
kfa source = fa source
 `compose` supertype `compose` component @target @t @(t `T'TT'I` tt `L` tt `T` ll)

kfai :: forall source target t tt ll i a o .
 Component target (T'II'I t i) (T'II'I t i `T'TT'I` tt `L` tt `T` ll) =>
 Contravariant Functor source target (T'II'I t i) =>
 (forall e . Wrapper source (I e)) =>
 (forall e . Wrapper source (I `L` tt `T` ll `T` e)) =>
 (forall e . Wrapper source (tt `L` tt `T` ll `T` e)) =>
 (forall e . Wrapper target (T'II'I t i `T'TT'I` tt `L` tt `T` ll `T'I_` e)) =>
 (forall e . Wrapper target (T'II'I t i e)) =>
 source o (tt `L` tt `T` ll `T` a) -> target (t a i) (t o i)
kfai = wrapped `compose` kfa @source @target @(T'II'I t _)

kfia :: forall source target t tt ll i a o .
 Component target (T'I'II t i) (T'I'II t i `T'TT'I` tt `L` tt `T` ll) =>
 Contravariant Functor source target (T'I'II t i) =>
 (forall e . Wrapper source (I e)) =>
 (forall e . Wrapper source (I `L` tt `T` ll `T` e)) =>
 (forall e . Wrapper source (tt `L` tt `T` ll `T` e)) =>
 (forall e . Wrapper target (T'I'II t i `T'TT'I` tt `L` tt `T` ll `T'I_` e)) =>
 (forall e . Wrapper target (T'I'II t i e)) =>
 source o (tt `L` tt `T` ll `T` a) -> target (t i a) (t i o)
kfia = wrapped `compose` kfa @source @target @(T'I'II t _)

fokl :: forall source target t tt l ll a o .
 Covariant Semi Functor source target t =>
 Component target (t `T'TT'I` tt `L` tt `T` ll `L` t `T` l) (t `TT'T'I` tt) =>
 (forall e . Wrapper target (t `T'TT'I` tt `L` tt `T` ll `L` t `T` l `T'I_` e)) =>
 (forall e . Wrapper target (t `TT'T'I` tt `T'I_` e)) =>
 source a (tt `L` tt `T` ll `L` t `T` l `T` o) -> target (t a) (tt (t o))
fokl = fio (wrapped (component @target @(t `T'TT'I` tt `L` tt `T` ll `L` t `T` l) @(t `TT'T'I` tt))) `compose` fo

fiokl :: forall source target t tt l ll i a o .
 Covariant Semi Functor target target tt =>
 Covariant Semi Functor source target (T'I'II t i) =>
 Component target (T'I'II t i `T'TT'I` tt `L` tt `T` ll `L` T'I'II t i `T` l) (T'I'II t i `TT'T'I` tt) =>
 (forall e . Wrapper target (T'I'II t i `T'TT'I` tt `L` tt `T` ll `L` T'I'II t i `T` l `T'I_` e)) =>
 (forall e . Wrapper target (T'I'II t i `TT'T'I` tt `T'I_` e)) =>
 (forall e . Wrapper source (T'I'II t i e)) =>
 (forall e . Wrapper target (T'I'II t i e)) =>
 source a (tt `L` tt `T` ll `L` T'I'II t i `T` l `T` o) -> target (t i a) (tt (t i o))
fiokl = fio @target (fo @target supertype) `compose` fai @target subtype `compose` fokl @source @target @(T'I'II t i)

foikl :: forall source target t tt l ll i a o .
 Covariant Endo Semi Functor target tt =>
 Covariant Semi Functor source target (T'II'I t i) =>
 Component target (T'II'I t i `T'TT'I` tt `L` tt `T` ll `L` T'II'I t i `T` l) (T'II'I t i `TT'T'I` tt) =>
 (forall e . Wrapper target (T'II'I t i `T'TT'I` tt `L` tt `T` ll `L` T'II'I t i `T` l `T'I_` e)) =>
 (forall e . Wrapper target (T'II'I t i `TT'T'I` tt `T'I_` e)) =>
 (forall e . Wrapper source (T'II'I t i e)) =>
 (forall e . Wrapper target (T'II'I t i e)) =>
 source a (tt `L` tt `T` ll `L` T'II'I t i `T` l `T` o) -> target (t a i) (tt (t o i))
foikl = fio @target (fo @target supertype) `compose` fai @target subtype `compose` fokl @source @target @(T'II'I t i)

fakl :: forall source target t tt l ll a o .
 Contravariant Semi Functor source target t =>
 Component target (t `T'TT'I` tt `L` tt `T` ll `L` t `T` l) (t `TT'T'I` tt) =>
 (forall e . Wrapper target (t `T'TT'I` tt `L` tt `T` ll `L` t `T` l `T'I_` e)) =>
 (forall e . Wrapper target (t `TT'T'I` tt `T'I_` e)) =>
 (forall e . Supertyping source (tt `L` tt `T` ll `T` e)) =>
 (forall e . Supertyping source (tt `L` tt `T` ll `L` t `T` l `T` e)) =>
 (forall e . Supertyping source (I `L` tt `T` ll `L` t `T` l `T` e)) =>
 (forall e . Supertyping source (I `L` tt `T` ll `T` e)) =>
 (forall e . Supertyping source (I `T` e)) =>
 source (tt o) (I `L` tt `T` ll `L` t `T` l `T` a) -> target (t a) (tt (t o))
fakl source = wrapped (component @target @(t `T'TT'I` tt `L` tt `T` ll `L` t `T` l) @(t `TT'T'I` tt))
 `compose` fa (supertype `compose` supertype `compose` supertype `compose` source `compose` supertype `compose` supertype)

fiakl :: forall source target t tt l ll i a o .
 Contravariant Endo Semi Functor target tt =>
 Contravariant Semi Functor source target (T'I'II t i) =>
 Component target (T'I'II t i `T'TT'I` tt `L` tt `T` ll `L` T'I'II t i `T` l) (T'I'II t i `TT'T'I` tt) =>
 (forall e . Wrapper target (T'I'II t i `T'TT'I` tt `L` tt `T` ll `L` T'I'II t i `T` l `T'I_` e)) =>
 (forall e . Wrapper target (T'I'II t i `TT'T'I` tt `T'I_` e)) =>
 (forall e . Supertyping source (tt `L` tt `T` ll `T` e)) =>
 (forall e . Supertyping source (tt `L` tt `T` ll `L` T'I'II t i `T` l `T` e)) =>
 (forall e . Supertyping source (I `L` tt `T` ll `L` T'I'II t i `T` l `T` e)) =>
 (forall e . Supertyping source (I `L` tt `T` ll `T` e)) =>
 (forall e . Supertyping source (I `T` e)) =>
 (forall e . Wrapper target (T'I'II t i e)) =>
 source (tt o) (I `L` tt `T` ll `L` T'I'II t i `T` l `T` a) -> target (t i a) (tt (t i o))
fiakl = fio @target (fa @target subtype) `compose` fai @target subtype `compose` fakl @source @target @(T'I'II t i)

faikl :: forall source target t tt l ll i a o .
 Contravariant Endo Semi Functor target tt =>
 Contravariant Semi Functor source target (T'II'I t i) =>
 Component target (T'II'I t i `T'TT'I` tt `L` tt `T` ll `L` T'II'I t i `T` l) (T'II'I t i `TT'T'I` tt) =>
 (forall e . Wrapper target (T'II'I t i `T'TT'I` tt `L` tt `T` ll `L` T'II'I t i `T` l `T'I_` e)) =>
 (forall e . Wrapper target (T'II'I t i `TT'T'I` tt `T'I_` e)) =>
 (forall e . Supertyping source (tt `L` tt `T` ll `T` e)) =>
 (forall e . Supertyping source (tt `L` tt `T` ll `L` T'II'I t i `T` l `T` e)) =>
 (forall e . Supertyping source (I `L` tt `T` ll `L` T'II'I t i `T` l `T` e)) =>
 (forall e . Supertyping source (I `L` tt `T` ll `T` e)) =>
 (forall e . Supertyping source (I `T` e)) =>
 (forall e . Wrapper target (T'II'I t i e)) =>
 source (tt o) (I `L` tt `T` ll `L` T'II'I t i `T` l `T` a) -> target (t a i) (tt (t o i))
faikl = fio @target (fa @target subtype) `compose` fai @target subtype `compose` fakl @source @target @(T'II'I t i)

fo'nt'fo :: forall source target t tt ll a o .
 Covariant Semi Functor source target t =>
 Covariant Semi Functor source target tt =>
 Component target (t `L` tt `T` ll) tt =>
 (forall e . Wrapper source (I `T` e)) =>
 (forall e . Wrapper source (I `L` tt `T` ll `T` e)) =>
 (forall e . Wrapper target (t `L` tt `T` ll `T` e)) =>
 source a (I `L` tt `T` ll `T` o) -> target (t a) (tt o)
fo'nt'fo source = component @target @(t `L` tt `T` ll) @tt `compose` subtype
 `compose` fo @source @target (supertype `compose` supertype `compose` source)

fio'nt'fo :: forall source target t tt ll i a o .
 (forall e . Covariant Semi Functor source target (T'I'II t e)) =>
 Covariant Semi Functor source target tt =>
 Component target (T'I'II t i `L` tt `T` ll) tt =>
 (forall e . Wrapper source (I `T` e)) =>
 (forall e . Wrapper source (I `L` tt `T` ll `T` e)) =>
 (forall e . Wrapper target (T'I'II t i `L` tt `T` ll `T` e)) =>
 (forall e . Wrapper target (T'I'II t i `T` e)) =>
 source a (I `L` tt `T` ll `T` o) -> target (t i a) (tt o)
fio'nt'fo source = component @target @(T'I'II t i `L` tt `T` ll) @tt `compose` subtype
 `compose` fo @source @target (supertype `compose` supertype `compose` source) `compose` subtype

fio'nt'fio :: forall source target t tt ll i ii a o .
 Category target =>
 Covariant Semi Functor source target (T'I'II t i) =>
 Covariant Semi Functor source target (T'I'II tt ii) =>
 Component target (T'I'II t i `L` T'I'II tt ii `T` ll) (T'I'II tt ii) =>
 (forall e . Wrapper source (I `T` e)) =>
 (forall e ee . Wrapper source (I `L` T'I'II tt ee `T` ll `T` e)) =>
 (forall e ee eee . Wrapper target (T'I'II t ee `L` T'I'II tt eee `T` ll `T` e)) =>
 (forall e ee . Wrapper target (T'I'II t ee `T` e)) =>
 (forall e ee . Wrapper target (T'I'II tt ee `T` e)) =>
 source a (I `L` T'I'II tt ii `T` ll `T` o) -> target (t i a) (tt ii o)
fio'nt'fio source = wrapped (component @target @(T'I'II t i `L` T'I'II tt ii `T` ll) @(T'I'II tt ii))
 `compose` fo @source @target (supertype `compose` supertype `compose` source) `compose` subtype

foi'nt'fo :: forall source target t tt ll i a o .
 (forall e . Covariant Semi Functor source target (T'II'I t e)) =>
 Covariant Semi Functor source target tt =>
 Component target (T'II'I t i `L` tt `T` ll) tt =>
 (forall e . Wrapper source (I `T` e)) =>
 (forall e . Wrapper source (I `L` tt `T` ll `T` e)) =>
 (forall e . Wrapper target (T'II'I t i `L` tt `T` ll `T` e)) =>
 (forall e . Wrapper target (T'II'I t i `T` e)) =>
 source a (I `L` tt `T` ll `T` o) -> target (t a i) (tt o)
foi'nt'fo source = component @target @(T'II'I t i `L` tt `T` ll) @tt `compose` subtype
 `compose` fo @source @target (supertype `compose` supertype `compose` source) `compose` subtype

foo'nt'fio :: forall source target t tt ll i ii a o .
 Category target =>
 Covariant Semi Functor source target (T'I'I t) =>
 Covariant Semi Functor source target (T'I'II tt ii) =>
 Component target (T'I'I t `L` T'I'II tt ii `T` ll) (T'I'II tt ii) =>
 (forall e . Wrapper source (I `T` e)) =>
 (forall e ee . Wrapper source (I `L` T'I'II tt ee `T` ll `T` e)) =>
 (forall e ee eee . Wrapper target (T'I'I t `L` T'I'II tt eee `T` ll `T` e)) =>
 (forall e . Wrapper target (T'I'I t `T` e)) =>
 (forall e ee . Wrapper target (T'I'II tt ee `T` e)) =>
 source a (I `L` T'I'II tt ii `T` ll `T` o) -> target (t a a) (tt ii o)
foo'nt'fio source = wrapped (component @target @(T'I'I t `L` T'I'II tt ii `T` ll) @(T'I'II tt ii))
 `compose` fo @source @target (supertype `compose` supertype `compose` source) `compose` subtype

fa'nt'fa :: forall source target t tt ll a o .
 Contravariant Semi Functor source target t =>
 Contravariant Semi Functor source target tt =>
 Component target (t `L` tt `T` ll) tt =>
 (forall e . Wrapper source (I `T` e)) =>
 (forall e . Wrapper source (I `L` tt `T` ll `T` e)) =>
 (forall e . Wrapper target (t `L` tt `T` ll `T` e)) =>
 source o (I `L` tt `T` ll `T` a) -> target (t a) (tt o)
fa'nt'fa source = component @target @(t `L` tt `T` ll) @tt `compose` subtype
 `compose` fa @source @target (supertype `compose` supertype `compose` source)

fai'nt'fa :: forall source target t tt ll i a o .
 Contravariant Semi Functor source target (T'II'I t i) =>
 Contravariant Semi Functor source target tt =>
 Component target (T'II'I t i `L` tt `T` ll) tt =>
 (forall e . Wrapper source (I `T` e)) =>
 (forall e . Wrapper source (I `L` tt `T` ll `T` e)) =>
 (forall e . Wrapper target (T'II'I t i `L` tt `T` ll `T` e)) =>
 (forall e . Wrapper target (T'II'I t i `T` e)) =>
 source o (I `L` tt `T` ll `T` a) -> target (t a i) (tt o)
fai'nt'fa source = component @target @(T'II'I t i `L` tt `T` ll) @tt `compose` subtype
 `compose` fa @source @target (supertype `compose` supertype `compose` source) `compose` subtype

fia'nt'fa :: forall source target t tt ll i a o .
 Contravariant Semi Functor source target (T'I'II t i) =>
 Contravariant Semi Functor source target tt =>
 Component target (T'I'II t i `L` tt `T` ll) tt =>
 (forall e . Wrapper source (I `T` e)) =>
 (forall e . Wrapper source (I `L` tt `T` ll `T` e)) =>
 (forall e . Wrapper target (T'I'II t i `L` tt `T` ll `T` e)) =>
 (forall e . Wrapper target (T'I'II t i `T` e)) =>
 source o (I `L` tt `T` ll `T` a) -> target (t i a) (tt o)
fia'nt'fa source = component @target @(T'I'II t i `L` tt `T` ll) @tt `compose` subtype
 `compose` fa @source @target (supertype `compose` supertype `compose` source) `compose` subtype

fa'dc'fa'nt'fa :: forall source target a aa o t tt ttt tttt ttttt lll lllll .
 Hom Functor source =>
 Hom Functor target =>
 (forall e . Component (AR) (I `L` (T'I'II target e `T'TT'I` T'II'I (P) e) `T` (Void)) (T'I'II target e `T'TT'I` T'II'I (P) e)) =>
 (forall e ee . Component target ((T'I'II source (ttttt e ee) `P'T'I'TT'I` T'I' (tttt (t e) (tt ee))) `L` T'I'I ttttt `T` lllll `L` ttt `T` lll) ttt) =>
 (forall e ee . Wrapper target (T'I' (tttt (t e) (tt ee)) o)) =>
 (forall e . Wrapper source (I e)) =>
 (forall e . Wrapper source (I `L` T'I'I ttttt `T` lllll `T` e)) =>
 (forall e . Wrapper source (I `L` T'I'I ttttt `T` lllll `L` ttt `T` lll `T` e)) =>
 (Wrapper target (T'II'I (P) (T'I' (tttt (t a) (tt aa)) o) (T'I'II source (ttttt a aa) o))) =>
 (forall e ee eee . Wrapper target ((T'I'II source (ttttt e ee) `P'T'I'TT'I` T'I' (tttt (t e) (tt ee))) eee)) =>
 (forall e ee eee . Wrapper target ((T'I'II source (ttttt e ee) `P'T'I'TT'I` T'I' (tttt (t e) (tt ee))) `L` T'I'I ttttt `T` lllll `T` eee)) =>
 (forall e ee eee . Wrapper target ((T'I'II source (ttttt e ee) `P'T'I'TT'I` T'I' (tttt (t e) (tt ee))) `L` T'I'I ttttt `T` lllll `L` ttt `T` lll `T` eee)) =>
 source (ttttt a aa) (I `L` T'I'I ttttt `T` lllll `L` ttt `T` lll `T` o) `AR____` target (tttt (t a) (tt aa)) (ttt o)
fa'dc'fa'nt'fa source = component @target @((T'I'II source (ttttt a aa) `P'T'I'TT'I` T'I' (tttt (t a) (tt aa))) `L` T'I'I ttttt `T` lllll `L` ttt `T` lll) @ttt
 `compose` subtype `compose` subtype
 `compose` subtype @target @((T'I'II source (ttttt a aa) `P'T'I'TT'I` T'I' (tttt (t a) (tt aa))) _)
 `compose` supertype `compose` (wrapped `compose` wrapped)
  (component @(AR) @(I `L` (T'I'II target ((T'I' (tttt (t a) (tt aa)) o)) `T'TT'I` T'II'I (P) ((T'I' (tttt (t a) (tt aa)) o))) `T` (Void))
   @(T'I'II target (T'I' (tttt (t a) (tt aa)) o) `T'TT'I` T'II'I (P) (T'I' (tttt (t a) (tt aa)) o)))
  (T'I'II (supertype @source `compose` supertype `compose` supertype `fio` source))
 `compose` subtype @target @(T'I' (tttt (t a) (tt aa)) o)

fo'dc'fo'nt'fo :: forall source target a aa o t tt ttt tttt ttttt lll lllll .
 Hom Functor source =>
 Hom Functor target =>
 (forall e . Component (AR) (I `L` (T'I'II target e `T'TT'I` T'II'I (P) e) `T` (Void)) (T'I'II target e `T'TT'I` T'II'I (P) e)) =>
 (forall e ee . Component target ((T'I'II source (ttttt e ee) `P'T'I'TT'I` T'I' (tttt (t e) (tt ee))) `L` T'I'I ttttt `T` lllll `L` ttt `T` lll) ttt) =>
 (forall e ee . Wrapper target (T'I' (tttt (t e) (tt ee)) o)) =>
 (forall e . Wrapper source (I e)) =>
 (forall e . Wrapper source (I `L` T'I'I ttttt `T` lllll `T` e)) =>
 (forall e . Wrapper source (I `L` T'I'I ttttt `T` lllll `L` ttt `T` lll `T` e)) =>
 (Wrapper target (T'II'I (P) (T'I' (tttt (t a) (tt aa)) o) (T'I'II source (ttttt a aa) o))) =>
 (forall e ee eee . Wrapper target ((T'I'II source (ttttt e ee) `P'T'I'TT'I` T'I' (tttt (t e) (tt ee))) eee)) =>
 (forall e ee eee . Wrapper target ((T'I'II source (ttttt e ee) `P'T'I'TT'I` T'I' (tttt (t e) (tt ee))) `L` T'I'I ttttt `T` lllll `T` eee)) =>
 (forall e ee eee . Wrapper target ((T'I'II source (ttttt e ee) `P'T'I'TT'I` T'I' (tttt (t e) (tt ee))) `L` T'I'I ttttt `T` lllll `L` ttt `T` lll `T` eee)) =>
 source (ttttt a aa) (I `L` T'I'I ttttt `T` lllll `L` ttt `T` lll `T` o) `AR____` target (tttt (t a) (tt aa)) (ttt o)
fo'dc'fo'nt'fo source = component @target @((T'I'II source (ttttt a aa) `P'T'I'TT'I` T'I' (tttt (t a) (tt aa))) `L` T'I'I ttttt `T` lllll `L` ttt `T` lll) @ttt
 `compose` subtype `compose` subtype
 `compose` subtype @target @((T'I'II source (ttttt a aa) `P'T'I'TT'I` T'I' (tttt (t a) (tt aa))) _)
 `compose` supertype `compose` (wrapped `compose` wrapped)
  (component @(AR) @(I `L` (T'I'II target ((T'I' (tttt (t a) (tt aa)) o)) `T'TT'I` T'II'I (P) ((T'I' (tttt (t a) (tt aa)) o))) `T` (Void))
   @(T'I'II target (T'I' (tttt (t a) (tt aa)) o) `T'TT'I` T'II'I (P) (T'I' (tttt (t a) (tt aa)) o)))
  (T'I'II (supertype @source `compose` supertype `compose` supertype `fio` source))
 `compose` subtype @target @(T'I' (tttt (t a) (tt aa)) o)

fo'nt'fo'dc'fo :: forall source target a o oo t tt ttt tttt ttttt lll lllll .
 Hom Functor source =>
 Hom Functor target =>
 (forall e . Component (AR) (I `L` (T'I'II target e `T'TT'I` T'II'I (P) e) `T` (Void)) (T'I'II target e `T'TT'I` T'II'I (P) e)) =>
 (forall e ee . Component target (((T'II'I source (ttttt e ee) `P'T'I'TT'I` ttt)) `L` T'I'I ttttt `T` lllll `L` ttt `T` lll) (T'I' (tttt (t e) (tt ee)))) =>
 (forall e ee . Wrapper target (T'I' (tttt (t e) (tt ee)) a)) =>
 (forall e . Wrapper source (I e)) =>
 (forall e . Wrapper source (I `L` T'I'I ttttt `T` lllll `T` e)) =>
 (forall e . Wrapper source (I `L` T'I'I ttttt `T` lllll `L` ttt `T` lll `T` e)) =>
 (forall e ee eee . Wrapper target (T'II'I (P) (ttt a) (T'II'I source (ttttt e ee) a))) =>
 (forall e ee eee . Wrapper target ((T'II'I source (ttttt e ee) `P'T'I'TT'I` ttt) eee)) =>
 (forall e ee eee . Wrapper target ((T'II'I source (ttttt e ee) `P'T'I'TT'I` ttt) `L` T'I'I ttttt `T` lllll `T` eee)) =>
 (forall e ee eee . Wrapper target ((T'II'I source (ttttt e ee) `P'T'I'TT'I` ttt) `L` T'I'I ttttt `T` lllll `L` ttt `T` lll `T` eee)) =>
 source a (I `L` T'I'I ttttt `T` lllll `L` ttt `T` lll `T` (ttttt o oo)) `AR____` target (ttt a) (tttt (t o) (tt oo))
fo'nt'fo'dc'fo source = wrapped (component @target @((T'II'I source (ttttt o oo) `P'T'I'TT'I` ttt) `L` T'I'I ttttt `T` lllll `L` ttt `T` lll) @(T'I' (tttt (t o) (tt oo))))
 `compose` subtype `compose` subtype @target @((T'II'I source (ttttt o oo) `P'T'I'TT'I` ttt) _)
 `compose` supertype `compose` (wrapped `compose` wrapped)
  (component @(AR) @(I `L` (T'I'II target (ttt a) `T'TT'I` T'II'I (P) (ttt a)) `T` (Void))
   @(T'I'II target (ttt a) `T'TT'I` T'II'I (P) (ttt a))) -- (T'I' (tttt (t a) (tt aa)) o)))
  (T'II'I (supertype @source `compose` supertype `compose` supertype `fio` source))

infixl 8 `yo`, `yo'st`, `yo'vt`, `yo'ut`
infixl 7 `yo_`, `yo_'st`, `yo_'vt`, `yo_'ut`
infixl 6 `yo__`, `yo__'st`, `yo__'vt`, `yo__'ut`
infixl 5 `yo___`, `yo___'st`, `yo___'vt`, `yo___'ut`
infixl 4 `yo____`, `yo____'st`, `yo____'vt`, `yo____'ut`
infixl 3 `yo_____`, `yo_____'st`, `yo_____'vt`, `yo_____'ut`
infixl 2 `yo______`, `yo______'st`, `yo______'vt`, `yo______'ut`
infixl 1 `yo_______`, `yo_______'st`, `yo_______'vt`, `yo_______'ut`

yo, yo_, yo__, yo___, yo____, yo_____, yo______, yo_______
 :: forall source target t a o .
 Hom Functor target =>
 Covariant Yoneda Functor source target t =>
 (forall e ee . Wrapper target (T'I'II source e ee)) =>
 (forall e ee . Wrapper target (T'II'I target e ee)) =>
 target (t a) (target (source a o) (t o))
yo = fai @target subtype `compose` yoneda @T'I'II @Functor

yo_ = yo
yo__ = yo
yo___ = yo
yo____ = yo
yo_____ = yo
yo______ = yo
yo_______ = yo

yo'st, yo_'st, yo__'st, yo___'st, yo____'st, yo_____'st, yo______'st, yo_______'st
 :: forall source target t a o .
 Hom Functor target =>
 (forall e . Contravariant Semi Functor source target (T'II'I source e)) =>
 Covariant Yoneda Functor source target t =>
 (forall e ee . Wrapper target (T'I'II source e ee)) =>
 (forall e ee . Wrapper target (T'II'I source e ee)) =>
 (forall e ee . Wrapper target (T'II'I target e ee)) =>
 (forall e . Wrapper source e) =>
 target (t a) (target (source (Supertype a) o) (t o))
yo'st = fai @target (fai @source supertype) `compose` yo @source @target @t

yo_'st = yo'st
yo__'st = yo'st
yo___'st = yo'st
yo____'st = yo'st
yo_____'st = yo'st
yo______'st = yo'st
yo_______'st = yo'st

yo'vt, yo_'vt, yo__'vt, yo___'vt, yo____'vt, yo_____'vt, yo______'vt, yo_______'vt
 :: forall target t i a o .
 Hom Functor target =>
 Covariant Endo Yoneda Functor target t =>
 Initial target =>
 (forall e . Wrapper target (target Void e)) =>
 (Supertype (target Void o) ~ Unit) =>
 (forall e ee . Wrapper target (T'II'I target e ee)) =>
 (forall e ee . Wrapper target (T'I'II target e ee)) =>
 (forall e ee . Wrapper target (T'I'II target e ee)) =>
 (forall e ee . Wrapper target (T'II'I target e ee)) =>
 target (t Void) (target Unit (t o))
yo'vt = fai @target (fai @target initial `compose` subtype @target @(target Void o)) `compose` yo @target @target @t

yo_'vt = yo'vt
yo__'vt = yo'vt
yo___'vt = yo'vt
yo____'vt = yo'vt
yo_____'vt = yo'vt
yo______'vt = yo'vt
yo_______'vt = yo'vt

yo'ut, yo_'ut, yo__'ut, yo___'ut, yo____'ut, yo_____'ut, yo______'ut, yo_______'ut
 :: forall target t i a o .
 Hom Functor target =>
 Covariant Endo Yoneda Functor target t =>
 Terminal target =>
 (forall e . Wrapper target (target Unit e)) =>
 (Supertype (target Unit o) ~ o) =>
 (forall e ee . Wrapper target (T'II'I target e ee)) =>
 (forall e ee . Wrapper target (T'I'II target e ee)) =>
 (forall e ee . Wrapper target (T'I'II target e ee)) =>
 (forall e ee . Wrapper target (T'II'I target e ee)) =>
 target (t a) (target o (t o))
yo'ut = fai @target (fai @target terminal `compose` subtype @target @(target Unit o)) `compose` yo @target @target @t

yo_'ut = yo'ut
yo__'ut = yo'ut
yo___'ut = yo'ut
yo____'ut = yo'ut
yo_____'ut = yo'ut
yo______'ut = yo'ut
yo_______'ut = yo'ut

infixl 8 `yio`, `yio'st`, `yio'vt`, `yio'st'vt`, `yio'ut`, `yio'ut'st`

infixl 9 `ho`, `ho'vt`, `ho'st'vt`, `ho'ut`, `ho'ut'st`, `ho'st`
infixl 8 `ho_`, `ho_'vt`, `ho_'st'vt`, `ho_'ut`, `ho_'ut'st`, `ho_'st`
infixl 7 `ho__`, `ho__'vt`, `ho__'st'vt`, `ho__'ut`, `ho__'ut'st`, `ho__'st`
infixl 6 `ho___`, `ho___'vt`, `ho___'st'vt`, `ho___'ut`, `ho___'ut'st`, `ho___'st`
infixl 5 `ho____`, `ho____'vt`, `ho____'st'vt`, `ho____'ut`, `ho____'ut'st`, `ho____'st`
infixl 4 `ho_____`, `ho_____'vt`, `ho_____'st'vt`, `ho_____'ut`, `ho_____'ut'st`, `ho_____'st`
infixl 3 `ho______`, `ho______'vt`, `ho______'st'vt`, `ho______'ut`, `ho______'ut'st`, `ho______'st`
infixl 2 `ho_______`, `ho_______'vt`, `ho_______'st'vt`, `ho_______'ut`, `ho_______'ut'st`, `ho_______'st`
infixl 1 `ho________`, `ho________'vt`, `ho________'st'vt`, `ho________'ut`, `ho________'ut'st`, `ho________'st`

yio, ho, ho_, ho__, ho___, ho____, ho_____, ho______, ho_______, ho________
 :: forall source target t i a o .
 Hom Functor target =>
 Covariant Yoneda Functor source target (T'I'II t i) =>
 (forall e ee . Wrapper target (T'I'II source e ee)) =>
 (forall e ee . Wrapper target (T'I'II target e ee)) =>
 (forall e ee . Wrapper target (T'II'I target e ee)) =>
 (forall e . Wrapper target (T'I'II t i e)) =>
 target (t i a) (target (source a o) (t i o))
yio = fio @target supertype `compose` yo @source @target @(T'I'II t i) `compose` subtype

ho = yio
ho_ = yio
ho__ = yio
ho___ = yio
ho____ = yio
ho_____ = yio
ho______ = yio
ho_______ = yio
ho________ = yio

yio'st, ho'st, ho_'st, ho__'st, ho___'st, ho____'st, ho_____'st, ho______'st, ho_______'st, ho________'st
 :: forall source target t i a o .
 Hom Functor target =>
 Covariant Yoneda Functor source target (T'I'II t i) =>
 Contravariant Semi Functor source target (T'II'I source o) =>
 Covariant Semi Functor source target (T'I'II source o) =>
 Supertyping source a =>
 (forall e ee . Wrapper target (T'II'I target e ee)) =>
 (forall e ee . Wrapper target (T'I'II target e ee)) =>
 (forall e ee . Wrapper target (T'I'II source e ee)) =>
 (forall e ee . Wrapper target (T'II'I source e ee)) =>
 (forall e ee . Wrapper target (T'I'II t e ee)) =>
 target (t i a) (target (source (Supertype a) o) (t i o))
yio'st = fai @target (fai @source supertype) `compose` yio @source @target @t

ho'st = yio'st
ho_'st = yio'st
ho__'st = yio'st
ho___'st = yio'st
ho____'st = yio'st
ho_____'st = yio'st
ho______'st = yio'st
ho_______'st = yio'st
ho________'st = yio'st

yio'vt, ho'vt, ho_'vt, ho__'vt, ho___'vt, ho____'vt, ho_____'vt, ho______'vt, ho_______'vt, ho________'vt
 :: forall target t i a o .
 Hom Functor target =>
 Covariant Endo Yoneda Functor target (T'I'II t i) =>
 Hom Functor target =>
 Initial target =>
 (forall e . Wrapper target (target Void e)) =>
 (Supertype (target Void o) ~ Unit) =>
 (forall e ee . Wrapper target (T'II'I target e ee)) =>
 (forall e ee . Wrapper target (T'I'II target e ee)) =>
 (forall e ee . Wrapper target (T'I'II target e ee)) =>
 (forall e ee . Wrapper target (T'II'I target e ee)) =>
 (forall e ee . Wrapper target (T'I'II t e ee)) =>
 target (t i Void) (target Unit (t i o))
yio'vt = fai @target (fai @target initial `compose` subtype @target @(target Void o)) `compose` yio @target @target @t

ho'vt = yio'vt
ho_'vt = yio'vt
ho__'vt = yio'vt
ho___'vt = yio'vt
ho____'vt = yio'vt
ho_____'vt = yio'vt
ho______'vt = yio'vt
ho_______'vt = yio'vt
ho________'vt = yio'vt

yio'st'vt, ho'st'vt, ho_'st'vt, ho__'st'vt, ho___'st'vt, ho____'st'vt, ho_____'st'vt, ho______'st'vt, ho_______'st'vt, ho________'st'vt
 :: forall target t i a o .
 Hom Functor target =>
 Covariant Endo Yoneda Functor target (T'I'II t i) =>
 Hom Functor target =>
 Initial target =>
 (forall e . Wrapper target (target Void e)) =>
 (Supertype (target Void o) ~ Unit) =>
 Supertyping target a =>
 (Supertype a ~ Void) =>
 (forall e ee . Wrapper target (T'II'I target e ee)) =>
 (forall e ee . Wrapper target (T'I'II target e ee)) =>
 (forall e ee . Wrapper target (T'I'II target e ee)) =>
 (forall e ee . Wrapper target (T'II'I target e ee)) =>
 (forall e ee . Wrapper target (T'I'II t e ee)) =>
 target (t i a) (target Unit (t i o))
yio'st'vt = fai @target (fai @target (initial `compose` supertype) `compose` subtype @target @(target Void o)) `compose` yio @target @target @t

ho'st'vt = yio'st'vt
ho_'st'vt = yio'st'vt
ho__'st'vt = yio'st'vt
ho___'st'vt = yio'st'vt
ho____'st'vt = yio'st'vt
ho_____'st'vt = yio'st'vt
ho______'st'vt = yio'st'vt
ho_______'st'vt = yio'st'vt
ho________'st'vt = yio'st'vt

yio'ut, ho'ut, ho_'ut, ho__'ut, ho___'ut, ho____'ut, ho_____'ut, ho______'ut, ho_______'ut, ho________'ut
 :: forall target t i a o .
 Hom Functor target =>
 Covariant Endo Yoneda Functor target (T'I'II t i) =>
 Hom Functor target =>
 Terminal target =>
 (forall e . Wrapper target (target Unit e)) =>
 (Supertype (target Unit o) ~ o) =>
 (forall e ee . Wrapper target (T'II'I target e ee)) =>
 (forall e ee . Wrapper target (T'I'II target e ee)) =>
 (forall e ee . Wrapper target (T'I'II target e ee)) =>
 (forall e ee . Wrapper target (T'II'I target e ee)) =>
 (forall e ee . Wrapper target (T'I'II t e ee)) =>
 target (t i a) (target o (t i o))
yio'ut = fai @target (fai @target terminal `compose` subtype @target @(target Unit o)) `compose` yio @target @target @t

ho'ut = yio'ut
ho_'ut = yio'ut
ho__'ut = yio'ut
ho___'ut = yio'ut
ho____'ut = yio'ut
ho_____'ut = yio'ut
ho______'ut = yio'ut
ho_______'ut = yio'ut
ho________'ut = yio'ut

yio'ut'st, ho'ut'st, ho_'ut'st, ho__'ut'st, ho___'ut'st, ho____'ut'st, ho_____'ut'st, ho______'ut'st, ho_______'ut'st, ho________'ut'st
 :: forall target t i a o .
 Hom Functor target =>
 Covariant Endo Yoneda Functor target (T'I'II t i) =>
 Terminal target =>
 (forall e . Wrapper target (target Unit e)) =>
 (Supertype (target Unit o) ~ o) =>
 (Wrapper target o) =>
 (forall e ee . Wrapper target (T'I'II target e ee)) =>
 (forall e ee . Wrapper target (T'II'I target e ee)) =>
 (forall e ee . Wrapper target (T'I'II t e ee)) =>
 target (t i a) (target o (t i (Supertype o)))
yio'ut'st = fio @target (fio @target supertype)
 `compose` fai @target (fai @target terminal `compose` subtype @target @(target Unit o))
 `compose` yio @target @target @t

ho'ut'st = yio'ut'st
ho_'ut'st = yio'ut'st
ho__'ut'st = yio'ut'st
ho___'ut'st = yio'ut'st
ho____'ut'st = yio'ut'st
ho_____'ut'st = yio'ut'st
ho______'ut'st = yio'ut'st
ho_______'ut'st = yio'ut'st
ho________'ut'st = yio'ut'st

infixl 8 `yoi`, `yoi'st`, `yoi'vt`, `yoi'st'vt`, `yoi'ut`, `yoi'ut'st`

yoi :: forall source target t i a o .
 Hom Functor target =>
 Covariant Yoneda Functor source target (T'II'I t i) =>
 (forall e ee . Wrapper target (T'I'II source e ee)) =>
 (forall e . Wrapper target (T'II'I t i e)) =>
 (forall e ee . Wrapper target (T'I'II target e ee)) =>
 (forall e ee . Wrapper target (T'II'I target e ee)) =>
 target (t a i) (target (source a o) (t o i))
yoi = fio @target supertype `compose` yo @source @target @(T'II'I t i) `compose` subtype

yoi'st
 :: forall source target t i a o .
 Hom Functor target =>
 Covariant Yoneda Functor source target (T'II'I t i) =>
 Contravariant Semi Functor source target (T'II'I source o) =>
 Covariant Semi Functor source target (T'I'II source o) =>
 Supertyping source a =>
 (forall e ee . Wrapper target (T'II'I target e ee)) =>
 (forall e ee . Wrapper target (T'I'II target e ee)) =>
 (forall e ee . Wrapper target (T'I'II source e ee)) =>
 (forall e ee . Wrapper target (T'II'I source e ee)) =>
 (forall e ee . Wrapper target (T'II'I t e ee)) =>
 target (t a i) (target (source (Supertype a) o) (t o i))
yoi'st = fai @target (fai @source supertype) `compose` yoi @source @target @t

yoi'vt
 :: forall target t i a o .
 Hom Functor target =>
 Covariant Endo Yoneda Functor target (T'II'I t i) =>
 Hom Functor target =>
 Initial target =>
 (forall e . Wrapper target (target Void e)) =>
 (Supertype (target Void o) ~ Unit) =>
 (forall e ee . Wrapper target (T'II'I target e ee)) =>
 (forall e ee . Wrapper target (T'I'II target e ee)) =>
 (forall e ee . Wrapper target (T'I'II target e ee)) =>
 (forall e ee . Wrapper target (T'II'I target e ee)) =>
 (forall e ee . Wrapper target (T'II'I t e ee)) =>
 target (t Void i) (target Unit (t o i))
yoi'vt = fai @target (fai @target initial `compose` subtype @target @(target Void o)) `compose` yoi @target @target @t

yoi'st'vt
 :: forall target t i a o .
 Hom Functor target =>
 Covariant Endo Yoneda Functor target (T'II'I t i) =>
 Hom Functor target =>
 Initial target =>
 (forall e . Wrapper target (target Void e)) =>
 (Supertype (target Void o) ~ Unit) =>
 Supertyping target a =>
 (Supertype a ~ Void) =>
 (forall e ee . Wrapper target (T'II'I target e ee)) =>
 (forall e ee . Wrapper target (T'I'II target e ee)) =>
 (forall e ee . Wrapper target (T'I'II target e ee)) =>
 (forall e ee . Wrapper target (T'II'I target e ee)) =>
 (forall e ee . Wrapper target (T'II'I t e ee)) =>
 target (t a i) (target Unit (t o i))
yoi'st'vt = fai @target (fai @target (initial `compose` supertype) `compose` subtype @target @(target Void o)) `compose` yoi @target @target @t

yoi'ut
 :: forall target t i a o .
 Hom Functor target =>
 Covariant Endo Yoneda Functor target (T'II'I t i) =>
 Hom Functor target =>
 Terminal target =>
 (forall e . Wrapper target (target Unit e)) =>
 (Supertype (target Unit o) ~ o) =>
 (forall e ee . Wrapper target (T'II'I target e ee)) =>
 (forall e ee . Wrapper target (T'I'II target e ee)) =>
 (forall e ee . Wrapper target (T'I'II target e ee)) =>
 (forall e ee . Wrapper target (T'II'I target e ee)) =>
 (forall e ee . Wrapper target (T'II'I t e ee)) =>
 target (t a i) (target o (t o i))
yoi'ut = fai @target (fai @target terminal `compose` subtype @target @(target Unit o)) `compose` yoi @target @target @t

yoi'ut'st
 :: forall target t i a o .
 Hom Functor target =>
 Covariant Endo Yoneda Functor target (T'II'I t i) =>
 Terminal target =>
 (forall e . Wrapper target (target Unit e)) =>
 (Supertype (target Unit o) ~ o) =>
 (Wrapper target o) =>
 (forall e ee . Wrapper target (T'I'II target e ee)) =>
 (forall e ee . Wrapper target (T'II'I target e ee)) =>
 (forall e ee . Wrapper target (T'II'I t e ee)) =>
 target (t a i) (target o (t (Supertype o) i))
yoi'ut'st = fio @target (foi @target supertype)
 `compose` fai @target (fai @target terminal `compose` subtype @target @(target Unit o))
 `compose` yoi @target @target @t

infixl 7 `yoo`, `yoo'ut`

yoo :: forall source target t a o .
 Hom Functor target =>
 Covariant Yoneda Functor source target (T'I'I t) =>
 (forall e . Wrapper target (T'I'I t e)) =>
 (forall e ee . Wrapper target (T'I'II source e ee)) =>
 (forall e ee . Wrapper target (T'I'II target e ee)) =>
 (forall e ee . Wrapper target (T'II'I target e ee)) =>
 target (t a a) (target (source a o) (t o o))
yoo = fio @target supertype `compose` yo @source @target @(T'I'I t) `compose` subtype

yoo'ut :: forall target t a o .
 Terminal target =>
 Covariant Yoneda Functor target target (T'I'I t) =>
 Hom Functor target =>
 (forall e ee . Wrapper target (T'I'II target e ee)) =>
 (forall e ee . Wrapper target (T'II'I target e ee)) =>
 (forall e . Wrapper target (T'I'I t e)) =>
 (forall e . Wrapper target (target Unit e)) =>
 (Supertype (target Unit o) ~ o) =>
 target (t a a) (target o (t o o))
yoo'ut = fio @target supertype `compose` yo'ut @target `compose` subtype @target @(T'I'I t _)

infixl 8 `ya`, `ya'vt`, `ya'ut`

ya :: forall source target t a o .
 Hom Functor target =>
 Contravariant Yoneda Functor source target t =>
 (forall e ee . Wrapper target (T'II'I source e ee)) =>
 (forall e ee . Wrapper target (T'II'I target e ee)) =>
 target (t a) (target (source o a) (t o))
ya = fai @target subtype `compose` yoneda @T'II'I @Functor

ya'vt :: forall target t i a o .
 Hom Functor target =>
 Contravariant Endo Yoneda Functor target t =>
 Initial target =>
 (forall e . Wrapper target (target Void e)) =>
 (Supertype (target Void a) ~ Unit) =>
 (forall e ee . Wrapper target (T'I'II target e ee)) =>
 (forall e ee . Wrapper target (T'II'I target e ee)) =>
 target (t a) (target Unit (t Void))
ya'vt = fai @target (fai @target initial `compose` subtype @target @(target Void a))
 `compose` ya @target @target @t

ya'ut :: forall target t i a o .
 Hom Functor target =>
 Contravariant Endo Yoneda Functor target t =>
 Terminal target =>
 (forall e . Wrapper target (target Unit e)) =>
 (Supertype (target Unit a) ~ a) =>
 (forall e ee . Wrapper target (T'I'II target e ee)) =>
 (forall e ee . Wrapper target (T'II'I target e ee)) =>
 target (t a) (target a (t o))
ya'ut = fai @target (fai @target terminal `compose` subtype @target @(target Unit a))
 `compose` ya @target @target @t

infixl 7 `yai`, `yai'st`, `yai'vt`, `yai'ut`, `yai'ut'st`

infixl 9 `ha`, `ha'vt`, `ha'st'vt`, `ha'ut`, `ha'ut'st`, `ha'st`
infixl 8 `ha_`, `ha_'vt`, `ha_'st'vt`, `ha_'ut`, `ha_'ut'st`, `ha_'st`
infixl 7 `ha__`, `ha__'vt`, `ha__'st'vt`, `ha__'ut`, `ha__'ut'st`, `ha__'st`
infixl 6 `ha___`, `ha___'vt`, `ha___'st'vt`, `ha___'ut`, `ha___'ut'st`, `ha___'st`
infixl 5 `ha____`, `ha____'vt`, `ha____'st'vt`, `ha____'ut`, `ha____'ut'st`, `ha____'st`
infixl 4 `ha_____`, `ha_____'vt`, `ha_____'st'vt`, `ha_____'ut`, `ha_____'ut'st`, `ha_____'st`
infixl 3 `ha______`, `ha______'vt`, `ha______'st'vt`, `ha______'ut`, `ha______'ut'st`, `ha______'st`
infixl 2 `ha_______`, `ha_______'vt`, `ha_______'st'vt`, `ha_______'ut`, `ha_______'ut'st`, `ha_______'st`
infixl 1 `ha________`, `ha________'vt`, `ha________'st'vt`, `ha________'ut`, `ha________'ut'st`, `ha________'st`

yai, ha, ha_, ha__, ha___, ha____, ha_____, ha______, ha_______, ha________ :: forall source target t i a o .
 Hom Functor target =>
 Contravariant Yoneda Functor source target (T'II'I t i) =>
 (forall e ee . Wrapper target (T'II'I source e ee)) =>
 (forall e ee . Wrapper target (T'I'II target e ee)) =>
 (forall e ee . Wrapper target (T'II'I target e ee)) =>
 (forall e ee . Wrapper target (T'II'I t e ee)) =>
 target (t a i) (target (source o a) (t o i))
yai = fio @target supertype `compose` ya @source @target @(T'II'I t i) `compose` subtype

ha = yai
ha_ = yai
ha__ = yai
ha___ = yai
ha____ = yai
ha_____ = yai
ha______ = yai
ha_______ = yai
ha________ = yai

yai'st, ha'st, ha_'st, ha__'st, ha___'st, ha____'st, ha_____'st, ha______'st, ha_______'st, ha________'st
 :: forall source target t i a o .
 Contravariant Yoneda Functor source target (T'II'I t i) =>
 (forall e . Contravariant Semi Functor source target (T'II'I source e)) =>
 Hom Functor target =>
 (forall e . Covariant Endo Semi Functor target (T'I'II target e)) =>
 (forall e ee . Wrapper target (T'II'I t e ee)) =>
 (forall e ee . Wrapper target (T'II'I source e ee)) =>
 (forall e ee . Wrapper target (T'I'II target e ee)) =>
 (forall e ee . Wrapper target (T'II'I target e ee)) =>
 Wrapper source o =>
 target (t a i) (target (source (Supertype o) a) (t o i))
yai'st = fai (fai @source @target supertype) `compose` yai @source @target @t

ha'st = yai'st
ha_'st = yai'st
ha__'st = yai'st
ha___'st = yai'st
ha____'st = yai'st
ha_____'st = yai'st
ha______'st = yai'st
ha_______'st = yai'st
ha________'st = yai'st

yai'vt, ha'vt, ha_'vt, ha__'vt, ha___'vt, ha____'vt, ha_____'vt, ha______'vt, ha_______'vt, ha________'vt
 :: forall target t i a o .
 Hom Functor target =>
 Contravariant Endo Yoneda Functor target (T'II'I t i) =>
 Initial target =>
 (forall e . Wrapper target (target Void e)) =>
 (Supertype (target Void a) ~ Unit) =>
 (forall e ee . Wrapper target (T'I'II target e ee)) =>
 (forall e ee . Wrapper target (T'II'I target e ee)) =>
 (forall e ee . Wrapper target (T'II'I t e ee)) =>
 target (t a i) (target Unit (t Void i))
yai'vt = fai @target (fai @target initial `compose` subtype @target @(target Void a))
 `compose` yai @target @target @t

ha'vt = yai'vt @target @t @i @a @o
ha_'vt = yai'vt @target @t @i @a @o
ha__'vt = yai'vt @target @t @i @a @o
ha___'vt = yai'vt @target @t @i @a @o
ha____'vt = yai'vt @target @t @i @a @o
ha_____'vt = yai'vt @target @t @i @a @o
ha______'vt = yai'vt @target @t @i @a @o
ha_______'vt = yai'vt @target @t @i @a @o
ha________'vt = yai'vt @target @t @i @a @o

yai'ut, ha'ut, ha_'ut, ha__'ut, ha___'ut, ha____'ut, ha_____'ut, ha______'ut, ha_______'ut, ha________'ut
 :: forall target t i a o .
 Hom Functor target =>
 Contravariant Endo Yoneda Functor target (T'II'I t i) =>
 Terminal target =>
 (forall e . Wrapper target (target Unit e)) =>
 (Supertype (target Unit a) ~ a) =>
 (forall e ee . Wrapper target (T'I'II target e ee)) =>
 (forall e ee . Wrapper target (T'II'I target e ee)) =>
 (forall e ee . Wrapper target (T'II'I t e ee)) =>
 target (t a i) (target a (t o i))
yai'ut = fai @target (fai @target terminal `compose` subtype @target @(target Unit a))
 `compose` yai @target @target @t

ha'ut = yai'ut
ha_'ut = yai'ut
ha__'ut = yai'ut
ha___'ut = yai'ut
ha____'ut = yai'ut
ha_____'ut = yai'ut
ha______'ut = yai'ut
ha_______'ut = yai'ut
ha________'ut = yai'ut

yai'ut'st, ha'ut'st, ha_'ut'st, ha__'ut'st, ha___'ut'st, ha____'ut'st, ha_____'ut'st, ha______'ut'st, ha_______'ut'st, ha________'ut'st
 :: forall target t i a o .
 Hom Functor target =>
 Contravariant Endo Yoneda Functor target (T'II'I t i) =>
 Terminal target =>
 (forall e . Wrapper target (target Unit e)) =>
 (Supertype (target Unit a) ~ a) =>
 (Supertyping target (Supertype o)) =>
 (forall e ee . Wrapper target (T'I'II target e ee)) =>
 (forall e ee . Wrapper target (T'II'I target e ee)) =>
 (forall e ee . Wrapper target (T'II'I t e ee)) =>
 target (t a i) (target (a) (t (Supertype o) i))
yai'ut'st = fio @target (fai @target supertype)
 `compose` fai @target (fai @target terminal `compose` subtype @target @(target Unit a))
 `compose` yai @target @target @t

ha'ut'st = yai'ut'st @target @t @i @a @o
ha_'ut'st = yai'ut'st @target @t @i @a @o
ha__'ut'st = yai'ut'st @target @t @i @a @o
ha___'ut'st = yai'ut'st @target @t @i @a @o
ha____'ut'st = yai'ut'st @target @t @i @a @o
ha_____'ut'st = yai'ut'st @target @t @i @a @o
ha______'ut'st = yai'ut'st @target @t @i @a @o
ha_______'ut'st = yai'ut'st @target @t @i @a @o
ha________'ut'st = yai'ut'st @target @t @i @a @o

yai'st'vt, ha'st'vt, ha_'st'vt, ha__'st'vt, ha___'st'vt, ha____'st'vt, ha_____'st'vt, ha______'st'vt, ha_______'st'vt, ha________'st'vt
 :: forall target t i a o .
 Hom Functor target =>
 Contravariant Endo Yoneda Functor target (T'II'I t i) =>
 Hom Functor target =>
 Initial target =>
 (forall e . Wrapper target (target Void e)) =>
 (Supertype (target Void o) ~ Unit) =>
 Supertyping target a =>
 (Supertype a ~ Void) =>
 (forall e ee . Wrapper target (T'II'I target e ee)) =>
 (forall e ee . Wrapper target (T'I'II target e ee)) =>
 (forall e ee . Wrapper target (T'I'II target e ee)) =>
 (forall e ee . Wrapper target (T'II'I target e ee)) =>
 (forall e ee . Wrapper target (T'II'I t e ee)) =>
 target (t o i) (target Unit (t a i))
yai'st'vt = fai @target (fai @target (initial `compose` supertype) `compose` subtype @target @(target Void o)) `compose` yai @target @target @t

ha'st'vt = yai'st'vt
ha_'st'vt = yai'st'vt
ha__'st'vt = yai'st'vt
ha___'st'vt = yai'st'vt
ha____'st'vt = yai'st'vt
ha_____'st'vt = yai'st'vt
ha______'st'vt = yai'st'vt
ha_______'st'vt = yai'st'vt
ha________'st'vt = yai'st'vt

infixl 7 `yia`

yia :: forall source target t i a o .
 Hom Functor target =>
 (forall e . Covariant Endo Semi Functor target (T'I'II target e)) =>
 Contravariant Yoneda Functor source target (T'I'II t i) =>
 (forall e ee . Wrapper target (T'II'I source e ee)) =>
 (forall e ee . Wrapper target (T'II'I target e ee)) =>
 (forall e ee . Wrapper target (T'I'II target e ee)) =>
 (forall e ee . Wrapper target (T'I'II t e ee)) =>
 target (t i a) (target (source o a) (t i o))
yia = fio @target supertype `compose` ya @source @target @(T'I'II t i) `compose` subtype

infixl 7 `yok`
infixl 6 `yok_`
infixl 5 `yok__`
infixl 4 `yok___`
infixl 3 `yok____`
infixl 2 `yok_____`
infixl 1 `yok______`

yok, yok_, yok__, yok___, yok____, yok_____, yok______
 :: forall source target t tt ll a o .
 Hom Functor target =>
 Covariant Yoneda Functor source target t =>
 Component target (t `T'TT'I` tt `L` tt `T` ll) t =>
 (forall e ee . Wrapper target (T'I'II source e ee)) =>
 (forall e . Wrapper target (t `T'TT'I` tt `L` tt `T` ll `T'I_` e)) =>
 (forall e ee . Wrapper target (T'I'II target e ee)) =>
 (forall e ee . Wrapper target (T'II'I target e ee)) =>
 target (t a) (target (source a (tt `L` tt `T` ll `T` o)) (t o))
yok = fio (component @target @(T'TT'I t (tt `L` tt `T` ll)) `compose` subtype @target @(T'TT'I t (tt `L` tt `T` ll) _)) `compose` yo

yok_ = yok
yok__ = yok
yok___ = yok
yok____ = yok
yok_____ = yok
yok______ = yok

infixl 7 `yak`
infixl 6 `yak_`
infixl 5 `yak__`
infixl 4 `yak___`
infixl 3 `yak____`
infixl 2 `yak_____`
infixl 1 `yak______`

yak, yak_, yak__, yak___, yak____, yak_____, yak______
 :: forall source target t tt ll a o .
 Hom Functor target =>
 Contravariant Yoneda Functor source target t =>
 Component target (t `T'TT'I` tt `L` tt `T` ll) t =>
 (forall e . Wrapper target (t `T'TT'I` tt `L` tt `T` ll `T'I_` e)) =>
 (forall e ee . Wrapper target (T'II'I source e ee)) =>
 (forall e ee . Wrapper target (T'I'II target e ee)) =>
 (forall e ee . Wrapper target (T'II'I target e ee)) =>
 target (t a) (target (source (tt `L` tt `T` ll `T` o) a) (t o))
yak = fio (component @target @(T'TT'I t (tt `L` tt `T` ll))
 `compose` subtype @target @(T'TT'I t (tt `L` tt `T` ll) _)) `compose` ya

yak_ = yak
yak__ = yak
yak___ = yak
yak____ = yak
yak_____ = yak
yak______ = yak

infixl 7 `kyo`
infixl 6 `_kyo`
infixl 5 `__kyo`
infixl 4 `___kyo`
infixl 3 `____kyo`
infixl 2 `_____kyo`
infixl 1 `______kyo`

kyo, _kyo, __kyo, ___kyo, ____kyo, _____kyo, ______kyo :: forall source target t tt ll a o .
 Component target t (t `T'TT'I` tt `L` tt `T` ll) =>
 Covariant Yoneda Functor source target t =>
 Hom Functor target =>
 (forall e . Contravariant Semi Functor source target (T'II'I source e)) =>
 (forall e . Covariant Semi Functor source target (T'I'II source e)) =>
 (forall e ee . Wrapper target (T'I'II source e ee)) =>
 (forall e ee . Wrapper target (T'II'I source e ee)) =>
 (forall e ee . Wrapper target (T'II'I target e ee)) =>
 (forall e . Wrapper source (I e)) =>
 (forall e . Wrapper source (I `L` tt `T` ll `T'I` e)) =>
 (forall e . Wrapper source (tt `L` tt `T` ll `T'I` e)) =>
 (forall e . Wrapper target (t `T'TT'I` tt `L` tt `T` ll `T'I_` e)) =>
 target (t a) (target (source (tt a) (I `L` tt `T` ll `T` o)) (t o))
kyo = fai @target (fai @source supertype `compose` fio @source (supertype @_ @(I _) `compose` supertype))
 `compose` yo @source @target @t
 `compose` supertype `compose` component @target @t @(t `T'TT'I` tt `L` tt `T` ll)

_kyo = kyo
__kyo = kyo
___kyo = kyo
____kyo = kyo
_____kyo = kyo
______kyo = kyo

infixl 6 `yokl`
infixl 5 `yokl_`
infixl 4 `yokl__`
infixl 3 `yokl___`
infixl 2 `yokl____`
infixl 1 `yokl_____`

yokl, yokl_, yokl__, yokl___, yokl____, yokl_____ ::
 forall source target t tt l ll a o .
 Hom Functor target =>
 Covariant Yoneda Functor source target t =>
 Component target (t `T'TT'I` tt `L` tt `T` ll `L` t `T` l) (t `TT'T'I` tt) =>
 (forall i . Wrapper target (t `T'TT'I` tt `L` tt `T` ll `L` t `T` l `T'I_` i)) =>
 (forall i . Wrapper target ((t `TT'T'I` tt) i)) =>
 (forall e ee . Wrapper target (T'I'II source e ee)) =>
 (forall e ee . Wrapper target (T'I'II target e ee)) =>
 (forall e ee . Wrapper target (T'II'I target e ee)) =>
 target (t a) (target (source a (tt `L` tt `T` ll `L` t `T` l `T` o)) (tt (t o)))
yokl = fio (wrapped @target (component @target @(t `T'TT'I` tt `L` tt `T` ll `L` t `T` l) @(t `TT'T'I` tt))) `compose` yo

yokl_ = yokl
yokl__ = yokl
yokl___ = yokl
yokl____ = yokl
yokl_____ = yokl

infixl 5 `yoikl`

yoikl ::
 forall source target t tt i l ll a o .
 Hom Functor target =>
 Covariant Yoneda Functor source target (T'II'I t i) =>
 Covariant Endo Semi Functor target tt =>
 Component target (T'II'I t i `T'TT'I` tt `L` tt `T` ll `L` T'II'I t i `T` l) (T'II'I t i `TT'T'I` tt) =>
 (forall e ee . Wrapper target (T'II'I t e `T'TT'I` tt `L` tt `T` ll `L` T'II'I t e `T` l `T'I_` ee)) =>
 (forall e ee . Wrapper target (T'II'I t e `TT'T'I` tt `T'I_` ee)) =>
 (forall e ee . Wrapper target (T'I'II source e ee)) =>
 (forall e ee . Wrapper target (T'I'II target e ee)) =>
 (forall e ee . Wrapper target (T'II'I target e ee)) =>
 (forall e ee . Wrapper target (T'II'I t e ee)) =>
 target (t a i) (target (source a (tt `L` tt `T` ll `L` T'II'I t i `T` l `T` o)) (tt (t o i)))
yoikl = fio (fo @target supertype `compose` wrapped @target (component @target @(T'II'I t i `T'TT'I` tt `L` tt `T` ll `L` T'II'I t i `T` l) @(T'II'I t i `TT'T'I` tt)))
 `compose` yo `compose` subtype

infixl 5 `yiokl`

yiokl ::
 forall source target t tt i l ll a o .
 Hom Functor target =>
 Covariant Yoneda Functor source target (T'I'II t i) =>
 Covariant Endo Semi Functor target tt =>
 Component target (T'I'II t i `T'TT'I` tt `L` tt `T` ll `L` T'I'II t i `T` l) (T'I'II t i `TT'T'I` tt) =>
 (forall e ee . Wrapper target (T'I'II t e `T'TT'I` tt `L` tt `T` ll `L` T'I'II t e `T` l `T'I_` ee)) =>
 (forall e ee . Wrapper target (T'I'II t e `TT'T'I` tt `T'I_` ee)) =>
 (forall e ee . Wrapper target (T'I'II source e ee)) =>
 (forall e ee . Wrapper target (T'I'II target e ee)) =>
 (forall e ee . Wrapper target (T'II'I target e ee)) =>
 (forall e ee . Wrapper target (T'I'II t e ee)) =>
 target (t i a) (target (source a (tt `L` tt `T` ll `L` T'I'II t i `T` l `T` o)) (tt (t i o)))
yiokl = fio (fo @target supertype `compose` wrapped @target (component @target @(T'I'II t i `T'TT'I` tt `L` tt `T` ll `L` T'I'II t i `T` l) @(T'I'II t i `TT'T'I` tt)))
 `compose` yo `compose` subtype

infixl 5 `yookl`

yookl ::
 forall source target t tt l ll a o .
 Hom Functor target =>
 Covariant Yoneda Functor source target (T'I'I t) =>
 Covariant Endo Semi Functor target tt =>
 Component target (T'I'I t `T'TT'I` tt `L` tt `T` ll `L` T'I'I t `T` l) (T'I'I t `TT'T'I` tt) =>
 (forall e . Wrapper target (T'I'I t `T'TT'I` tt `L` tt `T` ll `L` T'I'I t `T` l `T'I_` e)) =>
 (forall e . Wrapper target (T'I'I t `TT'T'I` tt `T'I_` e)) =>
 (forall e ee . Wrapper target (T'I'II source e ee)) =>
 (forall e ee . Wrapper target (T'I'II target e ee)) =>
 (forall e ee . Wrapper target (T'II'I target e ee)) =>
 (forall e . Wrapper target (T'I'I t e)) =>
 target (t a a) (target (source a (tt `L` tt `T` ll `L` T'I'I t `T` l `T` o)) (tt (t o o)))
yookl = fio (fo @target supertype `compose` wrapped @target (component @target @(T'I'I t `T'TT'I` tt `L` tt `T` ll `L` T'I'I t `T` l) @(T'I'I t `TT'T'I` tt)))
 `compose` yo `compose` subtype

infixl 6 `yakl`
infixl 5 `yakl_`
infixl 4 `yakl__`
infixl 3 `yakl___`
infixl 2 `yakl____`
infixl 1 `yakl_____`

yakl, yakl_, yakl__, yakl___, yakl____, yakl_____ ::
 forall source target t tt l ll a o .
 Hom Functor source =>
 Hom Functor target =>
 Contravariant Yoneda Functor source target t =>
 (forall e . Contravariant Semi Functor source target (T'II'I target e)) =>
 Component target (t `T'TT'I` tt `L` tt `T` ll `L` t `T` l) (t `TT'T'I` tt) =>
 (forall e . Wrapper target (t `T'TT'I` tt `L` tt `T` ll `L` t `T` l `T'I_` e)) =>
 (forall e . Wrapper target (t `TT'T'I` tt `T'I_` e)) =>
 (forall e . Wrapper source (tt `L` tt `T` ll `L` t `T` l `T'I_` e)) =>
 (forall e . Wrapper source (I `L` tt `T` ll `L` t `T` l `T'I_` e)) =>
 (forall e . Wrapper source (I `L` tt `T` ll `T'I_` e)) =>
 (forall e . Wrapper source (tt `L` tt `T` ll `T'I_` e)) =>
 (forall e . Wrapper source (I `T'I_` e)) =>
 (forall e ee . Wrapper source (T'I'II source e ee)) =>
 (forall e ee . Wrapper source (T'II'I source e ee)) =>
 (forall e ee . Wrapper target (T'I'II source e ee)) =>
 (forall e ee . Wrapper target (T'II'I source e ee)) =>
 (forall e ee . Wrapper target (T'I'II target e ee)) =>
 (forall e ee . Wrapper target (T'II'I target e ee)) =>
 target (t a) (target (source (tt o) (I `L` tt `T` ll `L` t `T` l `T` a)) (tt (t o)))
yakl = fio (wrapped @target (component @target @(t `T'TT'I` tt `L` tt `T` ll `L` t `T` l) @(t `TT'T'I` tt)))
 `compose` fai @source (fai @source (supertype `compose` supertype) `compose` fio @source (supertype `compose` supertype `compose` supertype))
 `compose` ya

yakl_ = yakl
yakl__ = yakl
yakl___ = yakl
yakl____ = yakl
yakl_____ = yakl

infixl 6 `yo'nt'yo`
infixl 5 `yo'nt_'yo`
infixl 4 `yo'nt__'yo`
infixl 3 `yo'nt___'yo`
infixl 2 `yo'nt____'yo`
infixl 1 `yo'nt_____'yo`

yo'nt'yo, yo'nt_'yo, yo'nt__'yo, yo'nt___'yo, yo'nt____'yo, yo'nt_____'yo
 :: forall source target t tt ll a o .
 Hom Functor source =>
 Hom Functor target =>
 Covariant Yoneda Functor source target t =>
 Component target (t `L` tt `T` ll) tt =>
 (forall e . Contravariant Functor source target (T'II'I target e)) =>
 (forall e ee . Wrapper source (T'I'II source e ee)) =>
 (forall e ee . Wrapper target (T'I'II source e ee)) =>
 (forall e ee . Wrapper target (T'II'I target e ee)) =>
 (forall e ee . Wrapper target (T'I'II target e ee)) =>
 (forall e . Wrapper source (I e)) =>
 (forall e . Wrapper source (I `L` tt `T` ll `T` e)) =>
 (forall e . Wrapper target (t `L` tt `T` ll `T` e)) =>
 target (t a) (target (source a (I `L` tt `T` ll `T` o)) (tt o))
yo'nt'yo = fio (component @target @(t `L` tt `T` ll) @tt `compose` subtype @target)
 `compose` (fai @source `compose` fio @source) (supertype `compose` supertype)
 `compose` yo

yo'nt_'yo = yo'nt'yo
yo'nt__'yo = yo'nt'yo
yo'nt___'yo = yo'nt'yo
yo'nt____'yo = yo'nt'yo
yo'nt_____'yo = yo'nt'yo

infixl 5 `yo'nt'yoo`
infixl 4 `yo'nt_'yoo`
infixl 3 `yo'nt__'yoo`
infixl 2 `yo'nt___'yoo`
infixl 1 `yo'nt____'yoo`

yo'nt'yoo, yo'nt_'yoo, yo'nt__'yoo, yo'nt___'yoo, yo'nt____'yoo
 :: forall source target t tt ll a o .
 Hom Functor source =>
 Hom Functor target =>
 Covariant Yoneda Functor source target t =>
 Component target (t `L` T'I'I tt `T` ll) (T'I'I tt) =>
 (forall e . Contravariant Functor source target (T'II'I target e)) =>
 (forall e . Wrapper target (T'I'I tt e)) =>
 (forall e ee . Wrapper source (T'I'II source e ee)) =>
 (forall e ee . Wrapper target (T'I'II source e ee)) =>
 (forall e ee . Wrapper target (T'II'I target e ee)) =>
 (forall e ee . Wrapper target (T'I'II target e ee)) =>
 (forall e . Wrapper source (I e)) =>
 (forall e . Wrapper source (I `L` T'I'I tt `T` ll `T` e)) =>
 (forall e . Wrapper target (t `L` T'I'I tt `T` ll `T` e)) =>
 target (t a) (target (source a (I `L` T'I'I tt `T` ll `T` o)) (tt o o))
yo'nt'yoo = fio (supertype `compose` component @target @(t `L` T'I'I tt `T` ll) @(T'I'I tt) `compose` subtype @target)
 `compose` (fai @source `compose` fio @source) (supertype `compose` supertype)
 `compose` yo

yo'nt_'yoo = yo'nt'yoo
yo'nt__'yoo = yo'nt'yoo
yo'nt___'yoo = yo'nt'yoo
yo'nt____'yoo = yo'nt'yoo

{-
infixl 6 `yo'nt'yo'yo'nt'yo`
infixl 5 `yo'nt_'yo'yo'nt'yo`
infixl 4 `yo'nt__'yo'yo'nt'yo`
infixl 3 `yo'nt___'yo'yo'nt'yo`
infixl 2 `yo'nt____'yo'yo'nt'yo`
infixl 1 `yo'nt_____'yo'yo'nt'yo`

yo'nt'yo'yo'nt'yo, yo'nt_'yo'yo'nt'yo, yo'nt__'yo'yo'nt'yo, yo'nt___'yo'yo'nt'yo, yo'nt____'yo'yo'nt'yo, yo'nt_____'yo'yo'nt'yo
 :: forall source target t tt ttt ll lll a o .
 Hom Functor source =>
 Hom Functor target =>
 Covariant Yoneda Functor source target t =>
 Component target (t `L` tt `T` ll) tt =>
 (forall e . Contravariant Functor source target (T'II'I target e)) =>
 (forall e ee . Wrapper source (T'I'II source e ee)) =>
 (forall e ee . Wrapper target (T'I'II source e ee)) =>
 (forall e ee . Wrapper target (T'II'I target e ee)) =>
 (forall e ee . Wrapper target (T'I'II target e ee)) =>
 (forall e . Wrapper source (I e)) =>
 (forall e . Wrapper source (I `L` tt `T` ll `T` e)) =>
 (forall e . Wrapper target (t `L` tt `T` ll `T` e)) =>
 target (t a) (target (source a (I `L` tt `T` ll `T'TT` I `L` ttt `T` lll `T'I` o)) (tt (ttt o)))
yo'nt'yo'yo'nt'yo = fio (component @target @(t `L` tt `T` ll) @tt `compose` subtype @target)
 `compose` (fai @source `compose` fio @source) (supertype `compose` supertype `compose` supertype)
 `compose` yo

yo'nt_'yo'yo'nt'yo = yo'nt'yo'yo'nt'yo
yo'nt__'yo'yo'nt'yo = yo'nt'yo'yo'nt'yo
yo'nt___'yo'yo'nt'yo = yo'nt'yo'yo'nt'yo
yo'nt____'yo'yo'nt'yo = yo'nt'yo'yo'nt'yo
yo'nt_____'yo'yo'nt'yo = yo'nt'yo'yo'nt'yo
-}

infixl 6 `ya'nt'ya`
infixl 5 `ya'nt_'ya`
infixl 4 `ya'nt__'ya`
infixl 3 `ya'nt___'ya`
infixl 2 `ya'nt____'ya`
infixl 1 `ya'nt_____'ya`

ya'nt'ya, ya'nt_'ya, ya'nt__'ya, ya'nt___'ya, ya'nt____'ya, ya'nt_____'ya
 :: forall source target t tt ll a o .
 Hom Functor source =>
 Hom Functor target =>
 Contravariant Yoneda Functor source target t =>
 Component target (t `L` tt `T` ll) tt =>
 (forall e . Contravariant Functor source target (T'II'I target e)) =>
 (forall e ee . Wrapper target (T'II'I source e ee)) =>
 (forall e ee . Wrapper source (T'I'II source e ee)) =>
 (forall e ee . Wrapper target (T'II'I target e ee)) =>
 (forall e ee . Wrapper target (T'I'II target e ee)) =>
 (forall e . Wrapper source (I e)) =>
 (forall e . Wrapper source (I `L` tt `T` ll `T` e)) =>
 (forall e . Wrapper target (t `L` tt `T` ll `T` e)) =>
 target (t a) (target (source o (I `L` tt `T` ll `T` a)) (tt o))
ya'nt'ya = fio (component @target @(t `L` tt `T` ll) @tt `compose` subtype @target)
 `compose` (fai @source `compose` fio @source) (supertype `compose` supertype)
 `compose` ya

ya'nt_'ya = ya'nt'ya
ya'nt__'ya = ya'nt'ya
ya'nt___'ya = ya'nt'ya
ya'nt____'ya = ya'nt'ya
ya'nt_____'ya = ya'nt'ya

infixl 5 `yio'nt'yo`

infixl 7 `ho'nt'yo`
infixl 6 `ho'nt_'yo`
infixl 5 `ho'nt__'yo`
infixl 3 `ho'nt___'yo`
infixl 2 `ho'nt____'yo`
infixl 1 `ho'nt_____'yo`

yio'nt'yo, ho'nt'yo, ho'nt_'yo, ho'nt__'yo, ho'nt___'yo, ho'nt____'yo, ho'nt_____'yo
 :: forall source target t tt ll a o i .
 Hom Functor source =>
 Hom Functor target =>
 (forall e . Covariant Yoneda Functor source target (T'I'II t e)) =>
 Component target (T'I'II t i `L` tt `T` ll) tt =>
 (forall e . Contravariant Functor source target (T'II'I target e)) =>
 (forall e ee . Wrapper target (T'I'II source e ee)) =>
 (forall e ee . Wrapper source (T'I'II source e ee)) =>
 (forall e ee . Wrapper target (T'II'I target e ee)) =>
 (forall e ee . Wrapper target (T'I'II target e ee)) =>
 (forall e ee . Wrapper target (T'I'II t e ee)) =>
 (forall e . Wrapper source (I e)) =>
 (forall e . Wrapper source (I `L` tt `T` ll `T` e)) =>
 (forall e ee . Wrapper target (T'I'II t ee `L` tt `T` ll `T` e)) =>
 target (t i a) (target (source a (I `L` tt `T` ll `T` o)) (tt o))
yio'nt'yo = fio (component @target @(T'I'II t i `L` tt `T` ll) @tt `compose` subtype @target)
 `compose` (fai @source `compose` fio @source) (supertype `compose` supertype)
 `compose` yo
 `compose` subtype

ho'nt'yo = yio'nt'yo
ho'nt_'yo = yio'nt'yo
ho'nt__'yo = yio'nt'yo
ho'nt___'yo = yio'nt'yo
ho'nt____'yo = yio'nt'yo
ho'nt_____'yo = yio'nt'yo

{-
ho'nt'yo --, ho'nt_'yo, ho'nt__'yo, ho'nt___'yo, ho'nt____'yo, ho'nt_____'yo
 :: forall source target t tt ll a o i .
 Hom Functor source =>
 Hom Functor target =>
 (forall e . Covariant Yoneda Functor source target (T'I'II t e)) =>
 Component target (T'I'II t i `L` tt `T` ll) tt =>
 (forall e . Contravariant Functor source target (T'II'I target e)) =>
 (forall e ee . Wrapper target (T'I'II source e ee)) =>
 (forall e ee . Wrapper source (T'I'II source e ee)) =>
 (forall e ee . Wrapper target (T'II'I target e ee)) =>
 (forall e ee . Wrapper target (T'I'II target e ee)) =>
 (forall e ee . Wrapper target (T'I'II t e ee)) =>
 (forall e . Wrapper source (I e)) =>
 (forall e . Wrapper source (I `L` tt `T` ll `T` e)) =>
 (forall e ee . Wrapper target (T'I'II t ee `L` tt `T` ll `T` e)) =>
 target (t i a) (target (source a (I `L` tt `T` ll `T` o)) (tt o))
yio'nt'yo = fio (component @target @(T'I'II t i `L` tt `T` ll) @tt `compose` subtype @target)
 `compose` (fai @source `compose` fio @source) (supertype `compose` supertype)
 `compose` yo
-}

infixl 4 `yio'nt'yio`

infixl 6 `ho'nt'yio`
infixl 5 `ho'nt_'yio`
infixl 4 `ho'nt__'yio`
infixl 3 `ho'nt___'yio`
infixl 2 `ho'nt____'yio`
infixl 1 `ho'nt_____'yio`

yio'nt'yio, ho'nt'yio, ho'nt_'yio, ho'nt__'yio, ho'nt___'yio, ho'nt____'yio, ho'nt_____'yio
 :: forall source target t tt ll a o i ii .
 Hom Functor source =>
 Hom Functor target =>
 (forall e . Covariant Yoneda Functor source target (T'I'II t e)) =>
 Component target (T'I'II t i `L` T'I'II tt ii `T` ll) (T'I'II tt ii) =>
 (forall e . Contravariant Functor source target (T'II'I target e)) =>
 (forall e ee . Wrapper target (T'I'II source e ee)) =>
 (forall e ee . Wrapper source (T'I'II source e ee)) =>
 (forall e ee . Wrapper target (T'II'I target e ee)) =>
 (forall e ee . Wrapper target (T'I'II target e ee)) =>
 (forall e ee . Wrapper target (T'I'II t e ee)) =>
 (forall e ee . Wrapper target (T'I'II tt e ee)) =>
 (forall e . Wrapper source (I e)) =>
 (forall e . Wrapper source (I `L` T'I'II tt ii `T` ll `T` e)) =>
 (forall e ee . Wrapper target (T'I'II t ee `L` T'I'II tt ii `T` ll `T` e)) =>
 target (t i a) (target (source a (I `L` T'I'II tt ii `T` ll `T` o)) (tt ii o))
yio'nt'yio = fio (wrapped (component @target @(T'I'II t i `L` T'I'II tt ii `T` ll) @(T'I'II tt ii)))
 `compose` (fai @source `compose` fio @source) (supertype `compose` supertype)
 `compose` yo
 `compose` subtype

ho'nt'yio = yio'nt'yio
ho'nt_'yio = yio'nt'yio
ho'nt__'yio = yio'nt'yio
ho'nt___'yio = yio'nt'yio
ho'nt____'yio = yio'nt'yio
ho'nt_____'yio = yio'nt'yio

infixl 4 `yio'nt'yoo`

infixl 6 `ho'nt'yoo`
infixl 5 `ho'nt_'yoo`
infixl 4 `ho'nt__'yoo`
infixl 3 `ho'nt___'yoo`
infixl 2 `ho'nt____'yoo`
infixl 1 `ho'nt_____'yoo`

yio'nt'yoo, ho'nt'yoo, ho'nt_'yoo, ho'nt__'yoo, ho'nt___'yoo, ho'nt____'yoo, ho'nt_____'yoo
 :: forall source target t tt ll a o i .
 Hom Functor source =>
 Hom Functor target =>
 (forall e . Covariant Yoneda Functor source target (T'I'II t e)) =>
 (forall e . Contravariant Functor source target (T'II'I target e)) =>
 Component target (T'I'II t i `L` T'I'I tt `T` ll) (T'I'I tt) =>
 (forall e ee . Wrapper target (T'I'II source e ee)) =>
 (forall e ee . Wrapper source (T'I'II source e ee)) =>
 (forall e ee . Wrapper target (T'II'I target e ee)) =>
 (forall e ee . Wrapper target (T'I'II target e ee)) =>
 (forall e ee . Wrapper target (T'I'II t e ee)) =>
 (forall e . Wrapper target (T'I'I tt e)) =>
 (forall e . Wrapper source (I e)) =>
 (forall e . Wrapper source (I `L` T'I'I tt `T` ll `T` e)) =>
 (forall e ee . Wrapper target (T'I'II t ee `L` T'I'I tt `T` ll `T` e)) =>
 target (t i a) (target (source a (I `L` T'I'I tt `T` ll `T` o)) (tt o o))
yio'nt'yoo = fio (wrapped (component @target @(T'I'II t i `L` T'I'I tt `T` ll) @(T'I'I tt)))
 `compose` (fai @source `compose` fio @source) (supertype `compose` supertype)
 `compose` yo
 `compose` subtype

ho'nt'yoo = yio'nt'yoo
ho'nt_'yoo = yio'nt'yoo
ho'nt__'yoo = yio'nt'yoo
ho'nt___'yoo = yio'nt'yoo
ho'nt____'yoo = yio'nt'yoo
ho'nt_____'yoo = yio'nt'yoo

infixl 5 `yai'nt'ya`

infixl 7 `ha'nt'ya`
infixl 6 `ha'nt_'ya`
infixl 5 `ha'nt__'ya`
infixl 3 `ha'nt___'ya`
infixl 2 `ha'nt____'ya`
infixl 1 `ha'nt_____'ya`

yai'nt'ya, ha'nt'ya, ha'nt_'ya, ha'nt__'ya, ha'nt___'ya, ha'nt____'ya, ha'nt_____'ya
 :: forall source target t tt ll a o i .
 Hom Functor source =>
 Hom Functor target =>
 (forall e . Contravariant Yoneda Functor source target (T'II'I t e)) =>
 Component target (T'II'I t i `L` tt `T` ll) tt =>
 (forall e . Contravariant Functor source target (T'II'I target e)) =>
 (forall e ee . Wrapper target (T'II'I source e ee)) =>
 (forall e ee . Wrapper source (T'I'II source e ee)) =>
 (forall e ee . Wrapper target (T'II'I target e ee)) =>
 (forall e ee . Wrapper target (T'I'II target e ee)) =>
 (forall e ee . Wrapper target (T'II'I t e ee)) =>
 (forall e . Wrapper source (I e)) =>
 (forall e . Wrapper source (I `L` tt `T` ll `T` e)) =>
 (forall e ee . Wrapper target (T'II'I t ee `L` tt `T` ll `T` e)) =>
 target (t a i) (target (source o (I `L` tt `T` ll `T` a)) (tt o))
yai'nt'ya = fio (component @target @(T'II'I t i `L` tt `T` ll) @tt `compose` subtype @target)
 `compose` (fai @source `compose` fio @source) (supertype `compose` supertype)
 `compose` ya
 `compose` subtype

ha'nt'ya = yai'nt'ya
ha'nt_'ya = yai'nt'ya
ha'nt__'ya = yai'nt'ya
ha'nt___'ya = yai'nt'ya
ha'nt____'ya = yai'nt'ya
ha'nt_____'ya = yai'nt'ya

infixl 7 `yo'nt'ho`, `yo'nt'ho'st`, `ya'nt'ha`, `ya'nt'ha'st`
infixl 6 `yo'nt_'ho`, `yo'nt_'ho'st`, `ya'nt_'ha`, `ya'nt_'ha'st`
infixl 5 `yo'nt__'ho`, `yo'nt__'ho'st`, `ya'nt__'ha`, `ya'nt__'ha'st`
infixl 4 `yo'nt___'ho`, `yo'nt___'ho'st`, `ya'nt___'ha`, `ya'nt___'ha'st`
infixl 3 `yo'nt____'ho`, `yo'nt____'ho'st`, `ya'nt____'ha`, `ya'nt____'ha'st`

yo'nt'ho, yo'nt_'ho, yo'nt__'ho, yo'nt___'ho, yo'nt____'ho
 :: forall target t tt ii a o .
 Hom Functor target =>
 Covariant Yoneda Functor target target t =>
 Component target (t `L` T'I'II tt ii `T` (Void)) (T'I'II tt ii) =>
 (forall e ee . Wrapper target (T'II'I target e ee)) =>
 (forall e ee . Wrapper target (T'I'II target e ee)) =>
 (forall e ee . Wrapper target (T'I'II tt e ee)) =>
 (forall e . Wrapper target (I e)) =>
 (forall e . Wrapper target (I `L` T'I'II tt ii `T` (Void) `T` e)) =>
 (forall e . Wrapper target (t `L` T'I'II tt ii `T` (Void) `T` e)) =>
 target (t o) (tt ii o)
yo'nt'ho = supertype `compose` component @target @(t `L` T'I'II tt ii `T` (Void)) @(T'I'II tt ii) `compose` subtype @target

yo'nt_'ho = yo'nt'ho
yo'nt__'ho = yo'nt'ho
yo'nt___'ho = yo'nt'ho
yo'nt____'ho = yo'nt'ho

yo'nt'ho'st, yo'nt_'ho'st, yo'nt__'ho'st, yo'nt___'ho'st, yo'nt____'ho'st
 :: forall target t tt ii a o .
 Hom Functor target =>
 Covariant Yoneda Functor target target t =>
 Covariant Endo Semi Functor target (T'I'II tt ii) =>
 Component target (t `L` T'I'II tt ii `T` (Void)) (T'I'II tt ii) =>
 (forall e ee . Wrapper target (T'II'I target e ee)) =>
 (forall e ee . Wrapper target (T'I'II target e ee)) =>
 (forall e ee . Wrapper target (T'I'II tt e ee)) =>
 (forall e . Wrapper target (I e)) =>
 (forall e . Wrapper target (I `L` T'I'II tt ii `T` (Void) `T` e)) =>
 (forall e . Wrapper target (t `L` T'I'II tt ii `T` (Void) `T` e)) =>
 Subtyping target o =>
 target (t (Supertype o)) (tt ii o)
yo'nt'ho'st = fio @target @target subtype `compose` supertype `compose` component @target @(t `L` T'I'II tt ii `T` (Void)) @(T'I'II tt ii) `compose` subtype @target

yo'nt_'ho'st = yo'nt'ho'st
yo'nt__'ho'st = yo'nt'ho'st
yo'nt___'ho'st = yo'nt'ho'st
yo'nt____'ho'st = yo'nt'ho'st

ya'nt'ha, ya'nt_'ha, ya'nt__'ha, ya'nt___'ha, ya'nt____'ha
 :: forall target t tt ii a o .
 Hom Functor target =>
 Contravariant Yoneda Functor target target t =>
 Component target (t `L` T'II'I tt ii `T` (Void)) (T'II'I tt ii) =>
 (forall e ee . Wrapper target (T'II'I target e ee)) =>
 (forall e ee . Wrapper target (T'I'II target e ee)) =>
 (forall e ee . Wrapper target (T'II'I tt e ee)) =>
 (forall e . Wrapper target (I e)) =>
 (forall e . Wrapper target (I `L` T'II'I tt ii `T` (Void) `T` e)) =>
 (forall e . Wrapper target (t `L` T'II'I tt ii `T` (Void) `T` e)) =>
 target (t a) (tt a ii)
ya'nt'ha = supertype `compose` component @target @(t `L` T'II'I tt ii `T` (Void)) @(T'II'I tt ii) `compose` subtype @target

ya'nt_'ha = ya'nt'ha
ya'nt__'ha = ya'nt'ha
ya'nt___'ha = ya'nt'ha
ya'nt____'ha = ya'nt'ha

ya'nt'ha'st, ya'nt_'ha'st, ya'nt__'ha'st, ya'nt___'ha'st, ya'nt____'ha'st
 :: forall target t tt ii a o .
 Hom Functor target =>
 Contravariant Yoneda Functor target target t =>
 Contravariant Endo Semi Functor target (T'II'I tt ii) =>
 Component target (t `L` T'II'I tt ii `T` (Void)) (T'II'I tt ii) =>
 (forall e ee . Wrapper target (T'II'I target e ee)) =>
 (forall e ee . Wrapper target (T'I'II target e ee)) =>
 (forall e ee . Wrapper target (T'II'I tt e ee)) =>
 (forall e . Wrapper target (I e)) =>
 (forall e . Wrapper target (I `L` T'II'I tt ii `T` (Void) `T` e)) =>
 (forall e . Wrapper target (t `L` T'II'I tt ii `T` (Void) `T` e)) =>
 Supertyping target a =>
 target (t (Supertype a)) (tt a ii)
ya'nt'ha'st = fai @target @target supertype `compose` supertype `compose` component @target @(t `L` T'II'I tt ii `T` (Void)) @(T'II'I tt ii) `compose` subtype @target

ya'nt_'ha'st = ya'nt'ha'st
ya'nt__'ha'st = ya'nt'ha'st
ya'nt___'ha'st = ya'nt'ha'st
ya'nt____'ha'st = ya'nt'ha'st

infixl 8 `ho'nt'ho`, `ho'nt'ho'st`
infixl 7 `ho'nt_'ho`, `ho'nt_'ho'st`
infixl 6 `ho'nt__'ho`, `ho'nt__'ho'st`
infixl 5 `ho'nt___'ho`, `ho'nt___'ho'st`
infixl 4 `ho'nt____'ho`, `ho'nt____'ho'st`
infixl 3 `ho'nt_____'ho`, `ho'nt_____'ho'st`
infixl 2 `ho'nt______'ho`, `ho'nt______'ho'st`

ho'nt'ho, ho'nt_'ho, ho'nt__'ho, ho'nt___'ho, ho'nt____'ho, ho'nt_____'ho, ho'nt______'ho
 :: forall target t tt o i ii .
 (forall e . Covariant Yoneda Functor target target (T'I'II t e)) =>
 Component target (T'I'II t i `L` T'I'II tt ii `T` (Void)) (T'I'II tt ii) =>
 (forall e ee . Wrapper target (T'I'II t e ee)) =>
 (forall e ee . Wrapper target (T'I'II tt e ee)) =>
 (forall e ee . Wrapper target (T'I'II t ee `L` T'I'II tt ii `T` (Void) `T` e)) =>
 target (t i o) (tt ii o)
ho'nt'ho = (wrapped (component @target @(T'I'II t i `L` T'I'II tt ii `T` (Void)) @(T'I'II tt ii))) `compose` subtype

ho'nt_'ho = ho'nt'ho
ho'nt__'ho = ho'nt'ho
ho'nt___'ho = ho'nt'ho
ho'nt____'ho = ho'nt'ho
ho'nt_____'ho = ho'nt'ho
ho'nt______'ho = ho'nt'ho

ho'nt'ho'st, ho'nt_'ho'st, ho'nt__'ho'st, ho'nt___'ho'st, ho'nt____'ho'st, ho'nt_____'ho'st, ho'nt______'ho'st
 :: forall target t tt o i ii .
 (forall e . Covariant Endo Yoneda Functor target (T'I'II t e)) =>
 (forall e . Covariant Endo Yoneda Functor target (T'I'II tt e)) =>
 Component target (T'I'II t i `L` T'I'II tt ii `T` (Void)) (T'I'II tt ii) =>
 (forall e ee . Wrapper target (T'I'II t e ee)) =>
 (forall e ee . Wrapper target (T'I'II tt e ee)) =>
 (forall e ee . Wrapper target (T'I'II t ee `L` T'I'II tt ii `T` (Void) `T` e)) =>
 Subtyping target o =>
 target (t i (Supertype o)) (tt ii o)
ho'nt'ho'st = fio @target @target subtype `compose` (wrapped (component @target @(T'I'II t i `L` T'I'II tt ii `T` (Void)) @(T'I'II tt ii))) `compose` subtype

ho'nt_'ho'st = ho'nt'ho'st
ho'nt__'ho'st = ho'nt'ho'st
ho'nt___'ho'st = ho'nt'ho'st
ho'nt____'ho'st = ho'nt'ho'st
ho'nt_____'ho'st = ho'nt'ho'st
ho'nt______'ho'st = ho'nt'ho'st

infixl 8 `ha'nt'ha`, `ha'nt'ha'st`, `st'ha'nt'ha`, `st'ha'nt'ha'st`, `bt'ha'nt'ha`, `bt'ha'nt'ha'st`
infixl 7 `ha'nt_'ha`, `ha'nt_'ha'st`, `st'ha'nt_'ha`, `st'ha'nt_'ha'st`, `bt'ha'nt_'ha`, `bt'ha'nt_'ha'st`
infixl 6 `ha'nt__'ha`, `ha'nt__'ha'st`, `st'ha'nt__'ha`, `st'ha'nt__'ha'st`, `bt'ha'nt__'ha`, `bt'ha'nt__'ha'st`
infixl 5 `ha'nt___'ha`, `ha'nt___'ha'st`, `st'ha'nt___'ha`, `st'ha'nt___'ha'st`, `bt'ha'nt___'ha`, `bt'ha'nt___'ha'st`
infixl 4 `ha'nt____'ha`, `ha'nt____'ha'st`, `st'ha'nt____'ha`, `st'ha'nt____'ha'st`, `bt'ha'nt____'ha`, `bt'ha'nt____'ha'st`
infixl 3 `ha'nt_____'ha`, `ha'nt_____'ha'st`, `st'ha'nt_____'ha`, `st'ha'nt_____'ha'st`, `bt'ha'nt_____'ha`, `bt'ha'nt_____'ha'st`
infixl 2 `ha'nt______'ha`, `ha'nt______'ha'st`, `st'ha'nt______'ha`, `st'ha'nt______'ha'st`, `bt'ha'nt______'ha`, `bt'ha'nt______'ha'st`

ha'nt'ha, ha'nt_'ha, ha'nt__'ha, ha'nt___'ha, ha'nt____'ha, ha'nt_____'ha, ha'nt______'ha
 :: forall target t tt a i ii .
 (forall e . Contravariant Yoneda Functor target target (T'II'I t e)) =>
 Component target (T'II'I t i `L` T'II'I tt ii `T` (Void)) (T'II'I tt ii) =>
 (forall e ee . Wrapper target (T'II'I t e ee)) =>
 (forall e ee . Wrapper target (T'II'I tt e ee)) =>
 (forall e ee . Wrapper target (T'II'I t ee `L` T'II'I tt ii `T` (Void) `T` e)) =>
 target (t a i) (tt a ii)
ha'nt'ha = (wrapped (component @target @(T'II'I t i `L` T'II'I tt ii `T` (Void)) @(T'II'I tt ii))) `compose` subtype

ha'nt_'ha = ha'nt'ha
ha'nt__'ha = ha'nt'ha
ha'nt___'ha = ha'nt'ha
ha'nt____'ha = ha'nt'ha
ha'nt_____'ha = ha'nt'ha
ha'nt______'ha = ha'nt'ha

ha'nt'ha'st, ha'nt_'ha'st, ha'nt__'ha'st, ha'nt___'ha'st, ha'nt____'ha'st, ha'nt_____'ha'st, ha'nt______'ha'st
 :: forall target t tt a i ii .
 (forall e . Contravariant Endo Yoneda Functor target (T'II'I t e)) =>
 (forall e . Contravariant Endo Yoneda Functor target (T'II'I tt e)) =>
 Component target (T'II'I t i `L` T'II'I tt ii `T` (Void)) (T'II'I tt ii) =>
 (forall e ee . Wrapper target (T'II'I t e ee)) =>
 (forall e ee . Wrapper target (T'II'I tt e ee)) =>
 (forall e ee . Wrapper target (T'II'I t ee `L` T'II'I tt ii `T` (Void) `T` e)) =>
 Supertyping target a =>
 target (t (Supertype a) i) (tt a ii)
ha'nt'ha'st = fai @target @target supertype `compose` (wrapped (component @target @(T'II'I t i `L` T'II'I tt ii `T` (Void)) @(T'II'I tt ii))) `compose` subtype

ha'nt_'ha'st = ha'nt'ha'st
ha'nt__'ha'st = ha'nt'ha'st
ha'nt___'ha'st = ha'nt'ha'st
ha'nt____'ha'st = ha'nt'ha'st
ha'nt_____'ha'st = ha'nt'ha'st
ha'nt______'ha'st = ha'nt'ha'st

st'ha'nt'ha, st'ha'nt_'ha, st'ha'nt__'ha, st'ha'nt___'ha, st'ha'nt____'ha, st'ha'nt_____'ha, st'ha'nt______'ha
 :: forall target e t tt a i ii .
 (forall e . Contravariant Yoneda Functor target target (T'II'I t e)) =>
 Component target (T'II'I t i `L` T'II'I tt ii `T` (Void)) (T'II'I tt ii) =>
 (forall e ee . Wrapper target (T'II'I t e ee)) =>
 (forall e ee . Wrapper target (T'II'I tt e ee)) =>
 (forall e ee . Wrapper target (T'II'I t ee `L` T'II'I tt ii `T` (Void) `T` e)) =>
 Supertyping target e =>
 (Supertype e ~ t a i) =>
 target e (tt a ii)
st'ha'nt'ha = wrapped (component @target @(T'II'I t i `L` T'II'I tt ii `T` (Void)) @(T'II'I tt ii)) `compose` subtype `compose` supertype

st'ha'nt_'ha = st'ha'nt'ha
st'ha'nt__'ha = st'ha'nt'ha
st'ha'nt___'ha = st'ha'nt'ha
st'ha'nt____'ha = st'ha'nt'ha
st'ha'nt_____'ha = st'ha'nt'ha
st'ha'nt______'ha = st'ha'nt'ha

st'ha'nt'ha'st, st'ha'nt_'ha'st, st'ha'nt__'ha'st, st'ha'nt___'ha'st, st'ha'nt____'ha'st, st'ha'nt_____'ha'st, st'ha'nt______'ha'st
 :: forall target e t tt a i ii .
 (forall e . Contravariant Endo Yoneda Functor target (T'II'I t e)) =>
 (forall e . Contravariant Endo Yoneda Functor target (T'II'I tt e)) =>
 Component target (T'II'I t i `L` T'II'I tt ii `T` (Void)) (T'II'I tt ii) =>
 (forall e ee . Wrapper target (T'II'I t e ee)) =>
 (forall e ee . Wrapper target (T'II'I tt e ee)) =>
 (forall e ee . Wrapper target (T'II'I t ee `L` T'II'I tt ii `T` (Void) `T` e)) =>
 Supertyping target e =>
 Supertyping target a =>
 (Supertype e ~ t (Supertype a) i) =>
 target e (tt a ii)
st'ha'nt'ha'st = fai @target @target supertype `compose` wrapped (component @target @(T'II'I t i `L` T'II'I tt ii `T` (Void)) @(T'II'I tt ii)) `compose` subtype `compose` supertype

st'ha'nt_'ha'st = st'ha'nt'ha'st
st'ha'nt__'ha'st = st'ha'nt'ha'st
st'ha'nt___'ha'st = st'ha'nt'ha'st
st'ha'nt____'ha'st = st'ha'nt'ha'st
st'ha'nt_____'ha'st = st'ha'nt'ha'st
st'ha'nt______'ha'st = st'ha'nt'ha'st

bt'ha'nt'ha, bt'ha'nt_'ha, bt'ha'nt__'ha, bt'ha'nt___'ha, bt'ha'nt____'ha, bt'ha'nt_____'ha, bt'ha'nt______'ha
 :: forall target e t tt a i ii .
 (forall e . Contravariant Yoneda Functor target target (T'II'I t e)) =>
 Component target (T'II'I t i `L` T'II'I tt ii `T` (Void)) (T'II'I tt ii) =>
 (forall e ee . Wrapper target (T'II'I t e ee)) =>
 (forall e ee . Wrapper target (T'II'I tt e ee)) =>
 (forall e ee . Wrapper target (T'II'I t ee `L` T'II'I tt ii `T` (Void) `T` e)) =>
 Covariant Objective target e (t a i) =>
 (Basetype e ~ t a i) =>
 target e (tt a ii)
bt'ha'nt'ha = wrapped (component @target @(T'II'I t i `L` T'II'I tt ii `T` (Void)) @(T'II'I tt ii)) `compose` subtype `compose` basetype

bt'ha'nt_'ha = bt'ha'nt'ha
bt'ha'nt__'ha = bt'ha'nt'ha
bt'ha'nt___'ha = bt'ha'nt'ha
bt'ha'nt____'ha = bt'ha'nt'ha
bt'ha'nt_____'ha = bt'ha'nt'ha
bt'ha'nt______'ha = bt'ha'nt'ha

bt'ha'nt'ha'st, bt'ha'nt_'ha'st, bt'ha'nt__'ha'st, bt'ha'nt___'ha'st, bt'ha'nt____'ha'st, bt'ha'nt_____'ha'st, bt'ha'nt______'ha'st
 :: forall target e t tt a i ii .
 (forall e . Contravariant Endo Yoneda Functor target (T'II'I t e)) =>
 (forall e . Contravariant Endo Yoneda Functor target (T'II'I tt e)) =>
 Component target (T'II'I t i `L` T'II'I tt ii `T` (Void)) (T'II'I tt ii) =>
 (forall e ee . Wrapper target (T'II'I t e ee)) =>
 (forall e ee . Wrapper target (T'II'I tt e ee)) =>
 (forall e ee . Wrapper target (T'II'I t ee `L` T'II'I tt ii `T` (Void) `T` e)) =>
 Covariant Objective target e (t (Supertype a) i) =>
 Supertyping target a =>
 (Basetype e ~ t (Supertype a) i) =>
 target e (tt a ii)
bt'ha'nt'ha'st = fai @target @target supertype `compose` wrapped (component @target @(T'II'I t i `L` T'II'I tt ii `T` (Void)) @(T'II'I tt ii)) `compose` subtype `compose` basetype

bt'ha'nt_'ha'st = bt'ha'nt'ha'st
bt'ha'nt__'ha'st = bt'ha'nt'ha'st
bt'ha'nt___'ha'st = bt'ha'nt'ha'st
bt'ha'nt____'ha'st = bt'ha'nt'ha'st
bt'ha'nt_____'ha'st = bt'ha'nt'ha'st
bt'ha'nt______'ha'st = bt'ha'nt'ha'st

infixl 8 `yo'yo'nt'yo`

yo'yo'nt'yo
 :: forall source target t tt ttt lll a o .
 Hom Functor source =>
 Hom Functor target =>
 Covariant Yoneda Functor source target t =>
 Covariant Yoneda Functor source source tt =>
 Covariant Yoneda Functor source source ttt =>
 Component source (tt `L` ttt `T` lll) ttt =>
 (forall e . Contravariant Functor source target (T'II'I target e)) =>
 (forall e . Contravariant Functor (AR) target (T'II'I target e)) =>
 (forall e ee . Wrapper source (T'I'II source e ee)) =>
 (forall e ee . Wrapper target (T'I'II source e ee)) =>
 (forall e ee . Wrapper target (T'II'I target e ee)) =>
 (forall e ee . Wrapper target (T'I'II target e ee)) =>
 (forall e . Wrapper source (I e)) =>
 (forall e . Wrapper source (I `L` ttt `T` lll `T` e)) =>
 (forall e . Wrapper source (tt `L` ttt `T` lll `T` e)) =>
 target (t (tt a)) (target (source a (I `L` ttt `T` lll `T` o)) (t (ttt o)))
yo'yo'nt'yo = fai (fo'nt'fo) `compose` yo @source @target

infixl 7 `yio'yo'nt'yo`
infixl 9 `ho'yo'nt'yo`
infixl 8 `ho_'yo'nt'yo`
infixl 7 `ho__'yo'nt'yo`
infixl 6 `ho___'yo'nt'yo`
infixl 5 `ho____'yo'nt'yo`
infixl 4 `ho_____'yo'nt'yo`
infixl 3 `ho______'yo'nt'yo`
infixl 2 `ho_______'yo'nt'yo`

yio'yo'nt'yo, ho'yo'nt'yo, ho_'yo'nt'yo, ho__'yo'nt'yo, ho___'yo'nt'yo, ho____'yo'nt'yo, ho_____'yo'nt'yo, ho______'yo'nt'yo, ho_______'yo'nt'yo
 :: forall source target t tt ttt lll i a o .
 Hom Functor source =>
 Hom Functor target =>
 Covariant Yoneda Functor source target (T'I'II t i) =>
 Covariant Yoneda Functor source source tt =>
 Covariant Yoneda Functor source source ttt =>
 Component source (tt `L` ttt `T` lll) ttt =>
 (forall e . Contravariant Functor source target (T'II'I target e)) =>
 (forall e . Contravariant Functor (AR) target (T'II'I target e)) =>
 (forall e ee . Wrapper source (T'I'II source e ee)) =>
 (forall e ee . Wrapper target (T'I'II source e ee)) =>
 (forall e ee . Wrapper target (T'II'I target e ee)) =>
 (forall e ee . Wrapper target (T'I'II target e ee)) =>
 (forall e . Wrapper source (I e)) =>
 (forall e . Wrapper target (T'I'II t i e)) =>
 (forall e . Wrapper source (I `L` ttt `T` lll `T` e)) =>
 (forall e . Wrapper source (tt `L` ttt `T` lll `T` e)) =>
 target (t i (tt a)) (target (source a (I `L` ttt `T` lll `T` o)) (t i (ttt o)))
yio'yo'nt'yo = fai (fo'nt'fo) `compose` yio @source @target

ho'yo'nt'yo = yio'yo'nt'yo
ho_'yo'nt'yo = yio'yo'nt'yo
ho__'yo'nt'yo = yio'yo'nt'yo
ho___'yo'nt'yo = yio'yo'nt'yo
ho____'yo'nt'yo = yio'yo'nt'yo
ho_____'yo'nt'yo = yio'yo'nt'yo
ho______'yo'nt'yo = yio'yo'nt'yo
ho_______'yo'nt'yo = yio'yo'nt'yo

infixl 7 `yio'yio'nt'yo`
infixl 9 `ho'yio'nt'yo`, `ho'ho'nt'yo`
infixl 8 `ho_'yio'nt'yo`, `ho_'ho'nt'yo`
infixl 7 `ho__'yio'nt'yo`, `ho__'ho'nt'yo`
infixl 6 `ho___'yio'nt'yo`, `ho___'ho'nt'yo`
infixl 5 `ho____'yio'nt'yo`, `ho____'ho'nt'yo`
infixl 4 `ho_____'yio'nt'yo`, `ho_____'ho'nt'yo`
infixl 3 `ho______'yio'nt'yo`, `ho______'ho'nt'yo`
infixl 2 `ho_______'yio'nt'yo`, `ho_______'ho'nt'yo`

yio'yio'nt'yo, ho'yio'nt'yo, ho_'yio'nt'yo, ho__'yio'nt'yo, ho___'yio'nt'yo, ho____'yio'nt'yo, ho_____'yio'nt'yo, ho______'yio'nt'yo, ho_______'yio'nt'yo, ho'ho'nt'yo, ho_'ho'nt'yo, ho__'ho'nt'yo, ho___'ho'nt'yo, ho____'ho'nt'yo, ho_____'ho'nt'yo, ho______'ho'nt'yo, ho_______'ho'nt'yo
 :: forall source target t tt ttt lll i ii a o .
 Hom Functor source =>
 Hom Functor target =>
 Covariant Yoneda Functor source target (T'I'II t i) =>
 (forall e . Covariant Yoneda Functor source source (T'I'II tt e)) =>
 Covariant Yoneda Functor source source ttt =>
 Component source (T'I'II tt ii `L` ttt `T` lll) ttt =>
 (forall e . Contravariant Functor source target (T'II'I target e)) =>
 (forall e . Contravariant Functor (AR) target (T'II'I target e)) =>
 (forall e ee . Wrapper source (T'I'II source e ee)) =>
 (forall e ee . Wrapper target (T'I'II source e ee)) =>
 (forall e ee . Wrapper target (T'II'I target e ee)) =>
 (forall e ee . Wrapper target (T'I'II target e ee)) =>
 (forall e . Wrapper source (I e)) =>
 (forall e . Wrapper target (T'I'II t i e)) =>
 (forall e . Wrapper source (T'I'II tt ii e)) =>
 (forall e . Wrapper source (I `L` ttt `T` lll `T` e)) =>
 (forall e . Wrapper source (T'I'II tt ii `L` ttt `T` lll `T` e)) =>
 target (t i (tt ii a)) (target (source a (I `L` ttt `T` lll `T` o)) (t i (ttt o)))
yio'yio'nt'yo = fai (fio'nt'fo) `compose` yio @source @target

ho'yio'nt'yo = yio'yio'nt'yo
ho_'yio'nt'yo = yio'yio'nt'yo
ho__'yio'nt'yo = yio'yio'nt'yo
ho___'yio'nt'yo = yio'yio'nt'yo
ho____'yio'nt'yo = yio'yio'nt'yo
ho_____'yio'nt'yo = yio'yio'nt'yo
ho______'yio'nt'yo = yio'yio'nt'yo
ho_______'yio'nt'yo = yio'yio'nt'yo

ho'ho'nt'yo = yio'yio'nt'yo
ho_'ho'nt'yo = yio'yio'nt'yo
ho__'ho'nt'yo = yio'yio'nt'yo
ho___'ho'nt'yo = yio'yio'nt'yo
ho____'ho'nt'yo = yio'yio'nt'yo
ho_____'ho'nt'yo = yio'yio'nt'yo
ho______'ho'nt'yo = yio'yio'nt'yo
ho_______'ho'nt'yo = yio'yio'nt'yo

infixl 8 `ya'yo'nt'yo`

ya'yo'nt'yo
 :: forall source target t tt ttt lll a o .
 Hom Functor source =>
 Hom Functor target =>
 Contravariant Yoneda Functor source target t =>
 Covariant Yoneda Functor source source tt =>
 Covariant Yoneda Functor source source ttt =>
 Component source (tt `L` ttt `T` lll) ttt =>
 (forall e . Contravariant Functor source target (T'II'I target e)) =>
 (forall e . Contravariant Functor (AR) target (T'II'I target e)) =>
 (forall e ee . Wrapper source (T'I'II source e ee)) =>
 (forall e ee . Wrapper target (T'II'I source e ee)) =>
 (forall e ee . Wrapper target (T'II'I target e ee)) =>
 (forall e ee . Wrapper target (T'I'II target e ee)) =>
 (forall e . Wrapper source (I e)) =>
 (forall e . Wrapper source (I `L` ttt `T` lll `T` e)) =>
 (forall e . Wrapper source (tt `L` ttt `T` lll `T` e)) =>
 target (t (ttt a)) (target (source o (I `L` ttt `T` lll `T` a)) (t (tt o)))
ya'yo'nt'yo = fai (fo'nt'fo) `compose` ya @source @target

infixl 7 `ho'dc'ho'nt'ho`

ho'dc'ho'nt'ho :: forall target a aa i t .
 Category target =>
 Hom Functor target =>
 (forall e . Covariant Endo Semi Functor target (T'I'II (P) e)) =>
 (forall e . Component (AR) (I `L` (T'I'II target e `T'TT'I` T'II'I (P) e) `T` (Void)) (T'I'II target e `T'TT'I` T'II'I (P) e)) =>
 (forall e . Component target (I `L` (T'I'II target e `T'TT'I` T'II'I (P) e) `T` (Void)) (T'I'II target e `T'TT'I` T'II'I (P) e)) =>
 (forall e ee . Component target ((T'I'II target ((P) e ee) `P'T'I'TT'I` T'I' ((P) (T'I'II t i e) (T'I'II t i ee))) `L` T'I'I (P) `T` (Void) `L` T'I'II t i `T` (Void)) (T'I'II t i)) =>
 (forall e ee . Wrapper target (T'II'I (P) e ee)) =>
 (forall e ee . Wrapper target (T'I'II (P) e ee)) =>
 (forall e ee . Wrapper target ((T'I'II target ((P) e ee) `P'T'I'TT'I` T'I' ((P) (T'I'II t i e) (T'I'II t i ee))) ((P) e ee))) =>
 (forall e ee . Wrapper target ((T'I'II target ((P) e ee) `P'T'I'TT'I` T'I' ((P) (T'I'II t i e) (T'I'II t i ee))) `L` T'I'I (P) `T` (Void) `T` (P) e ee)) =>
 (forall e ee . Wrapper target ((T'I'II target ((P) e ee) `P'T'I'TT'I` T'I' ((P) (T'I'II t i e) (T'I'II t i ee))) `L` T'I'I (P) `T` (Void) `L` T'I'II t i `T` (Void) `T` (P) e ee)) =>
 (forall e ee . Wrapper target (T'I' ((P) (T'I'II t i e) (T'I'II t i ee)) ((P) e ee))) =>
 (forall e . Wrapper target (I e)) =>
 (forall e ee . Wrapper target (T'I'II t e ee)) =>
 (forall e ee . Wrapper target (T'I'II t e ee)) =>
 (forall e ee . Wrapper target (T'I'II t e ee)) =>
 (forall e ee . Wrapper target (T'II'I (P) e ee)) =>
 (forall e ee . Wrapper target (T'I'II target e ee)) =>
 (forall e ee . Wrapper target (T'I'II target e `T'TT'I` T'II'I (P) e `T'I_` ee)) =>
 (forall e ee . Wrapper target (I `L` (T'I'II target e `T'TT'I` T'II'I (P) e) `T` (Void) `T` ee)) =>
 -- target (tttt (t i a) (t i aa)) (t i ((P) a aa))
 target (t i a) (target (t i aa) (t i ((P) a aa)))
ho'dc'ho'nt'ho = fio
 (supertype `compose` component @target @((T'I'II target ((P) a aa) `P'T'I'TT'I` T'I' ((P) (T'I'II t i a) (T'I'II t i aa))) `L` T'I'I (P) `T` (Void) `L` T'I'II t i `T` (Void)) @(T'I'II t i)
 `compose` subtype `compose` subtype
 `compose` subtype @target @((T'I'II target ((P) a aa) `P'T'I'TT'I` T'I' ((P) (T'I'II t i a) (T'I'II t i aa))) _)
 `compose` supertype `compose` (wrapped `compose` wrapped)
  (component @(AR) @(I `L` (T'I'II target ((T'I' ((P) (T'I'II t i a) (T'I'II t i aa)) ((P) a aa))) `T'TT'I` T'II'I (P) ((T'I' ((P) (T'I'II t i a) (T'I'II t i aa)) ((P) a aa)))) `T` (Void))
   @(T'I'II target (T'I' ((P) (T'I'II t i a) (T'I'II t i aa)) ((P) a aa)) `T'TT'I` T'II'I (P) (T'I' ((P) (T'I'II t i a) (T'I'II t i aa)) ((P) a aa))))
   (T'I'II identity)
 `compose` subtype @target @(T'I' ((P) (T'I'II t i a) (T'I'II t i aa)) ((P) a aa))
 `compose` fio (subtype @target @(T'I'II t i aa))
 `compose` supertype @target @(T'II'I (P) (t i aa) (T'I'II t i a)))
 `compose` (wrapped `compose` wrapped) (component @target @(I `L` (T'I'II target (t i aa) `T'TT'I` T'II'I (P) (t i aa)) `T` (Void)) @(T'I'II target (t i aa) `T'TT'I` T'II'I (P) (t i aa)))
 `compose` subtype @target @(T'I'II t i a)

infixl 7 `ha'dc'ha'nt'ha`
infixl 6 `ha'dc'ha'nt_'ha`
infixl 5 `ha'dc'ha'nt__'ha`
infixl 4 `ha'dc'ha'nt___'ha`
infixl 3 `ha'dc'ha'nt____'ha`
infixl 2 `ha'dc'ha'nt_____'ha`
infixl 1 `ha'dc'ha'nt______'ha`

ha'dc'ha'nt'ha, ha'dc'ha'nt_'ha , ha'dc'ha'nt__'ha, ha'dc'ha'nt___'ha, ha'dc'ha'nt____'ha, ha'dc'ha'nt_____'ha, ha'dc'ha'nt______'ha :: forall target a aa i t .
 Category target =>
 Hom Functor target =>
 (forall e . Covariant Endo Semi Functor target (T'I'II (P) e)) =>
 (forall e . Component (AR) (I `L` (T'I'II target e `T'TT'I` T'II'I (P) e) `T` (Void)) (T'I'II target e `T'TT'I` T'II'I (P) e)) =>
 (forall e . Component target (I `L` (T'I'II target e `T'TT'I` T'II'I (P) e) `T` (Void)) (T'I'II target e `T'TT'I` T'II'I (P) e)) =>
 Component target ((T'II'I target ((S) a aa) `P'T'I'TT'I` T'I' ((P) (T'II'I t i a) (T'II'I t i aa))) `L` T'I'I (S) `T` (Void) `L` T'II'I t i `T` (Void)) (T'II'I t i) =>
 (forall e ee . Wrapper target (T'II'I (P) e ee)) =>
 (forall e ee . Wrapper target (T'I'II (P) e ee)) =>
 (forall e ee . Wrapper target ((T'II'I target ((S) e ee) `P'T'I'TT'I` T'I' ((P) (T'II'I t i e) (T'II'I t i ee))) ((S) e ee))) =>
 (forall e ee . Wrapper target ((T'II'I target ((S) e ee) `P'T'I'TT'I` T'I' ((P) (T'II'I t i e) (T'II'I t i ee))) `L` T'I'I (S) `T` (Void) `T` (S) e ee)) =>
 (forall e ee . Wrapper target ((T'II'I target ((S) e ee) `P'T'I'TT'I` T'I' ((P) (T'II'I t i e) (T'II'I t i ee))) `L` T'I'I (S) `T` (Void) `L` T'II'I t i `T` (Void) `T` (S) e ee)) =>
 (forall e ee . Wrapper target (T'I' ((P) (T'II'I t i e) (T'II'I t i ee)) ((S) e ee))) =>
 (forall e . Wrapper target (I e)) =>
 (forall e ee . Wrapper target (T'II'I t e ee)) =>
 (forall e ee . Wrapper target (T'II'I t e ee)) =>
 (forall e ee . Wrapper target (T'II'I t e ee)) =>
 (forall e ee . Wrapper target (T'II'I (P) e ee)) =>
 (forall e ee . Wrapper target (T'I'II target e ee)) =>
 (forall e ee . Wrapper target (T'I'II target e `T'TT'I` T'II'I (P) e `T'I_` ee)) =>
 (forall e ee . Wrapper target (I `L` (T'I'II target e `T'TT'I` T'II'I (P) e) `T` (Void) `T` ee)) =>
 target (t a i) (target (t aa i) (t ((S) a aa) i))
ha'dc'ha'nt'ha = fio
 (supertype `compose` component @target @((T'II'I target ((S) a aa) `P'T'I'TT'I` T'I' ((P) (T'II'I t i a) (T'II'I t i aa))) `L` T'I'I (S) `T` (Void) `L` T'II'I t i `T` (Void)) @(T'II'I t i)
 `compose` subtype `compose` subtype
 `compose` subtype @target @((T'II'I target ((S) a aa) `P'T'I'TT'I` T'I' ((P) (T'II'I t i a) (T'II'I t i aa))) _)
 `compose` supertype `compose` (wrapped `compose` wrapped)
  (component @(AR) @(I `L` (T'I'II target ((T'I' ((P) (T'II'I t i a) (T'II'I t i aa)) ((S) a aa))) `T'TT'I` T'II'I (P) ((T'I' ((P) (T'II'I t i a) (T'II'I t i aa)) ((S) a aa)))) `T` (Void))
   @(T'I'II target (T'I' ((P) (T'II'I t i a) (T'II'I t i aa)) ((S) a aa)) `T'TT'I` T'II'I (P) (T'I' ((P) (T'II'I t i a) (T'II'I t i aa)) ((S) a aa))))
   (T'II'I identity)
 `compose` subtype @target @(T'I' ((P) (T'II'I t i a) (T'II'I t i aa)) ((S) a aa))
 `compose` fio (subtype @target @(T'II'I t i aa))
 `compose` supertype @target @(T'II'I (P) (t aa i) (T'II'I t i a)))
 `compose` (wrapped `compose` wrapped) (component @target @(I `L` (T'I'II target (t aa i) `T'TT'I` T'II'I (P) (t aa i)) `T` (Void)) @(T'I'II target (t aa i) `T'TT'I` T'II'I (P) (t aa i)))
 `compose` subtype @target @(T'II'I t i a)

ha'dc'ha'nt_'ha = ha'dc'ha'nt'ha
ha'dc'ha'nt__'ha = ha'dc'ha'nt'ha
ha'dc'ha'nt___'ha = ha'dc'ha'nt'ha
ha'dc'ha'nt____'ha = ha'dc'ha'nt'ha
ha'dc'ha'nt_____'ha = ha'dc'ha'nt'ha
ha'dc'ha'nt______'ha = ha'dc'ha'nt'ha

infixl 4 `yo'dc'yo'nt'yo`, `st'yo'dc'yo'nt'yo`

yo'dc'yo'nt'yo :: forall source target a aa o t tt ttt tttt ttttt lll lllll .
 Hom Functor source =>
 Hom Functor target =>
 (forall e . Covariant Endo Semi Functor target (T'II'I (P) e)) =>
 (forall e . Covariant Endo Semi Functor target (T'I'II source e)) =>
 (forall e . Component target (I
  `L` (T'I'II target (source (ttttt a aa) (I `L` T'I'I ttttt `T` lllll `L` ttt `T` lll `T` o)) `T'TT'I` T'I'II (P) (source (ttttt a aa) (I `L` T'I'I ttttt `T` lllll `L` ttt `T` lll `T` o))) `T` (Void))
  (T'I'II target (source (ttttt a aa) (I `L` T'I'I ttttt `T` lllll `L` ttt `T` lll `T` o)) `T'TT'I` T'I'II (P) (source (ttttt a aa) (I `L` T'I'I ttttt `T` lllll `L` ttt `T` lll `T` o)))) =>
 (forall e ee . Component target ((T'I'II source (ttttt e ee) `P'T'I'TT'I` T'I' (tttt (t e) (tt ee))) `L` T'I'I ttttt `T` lllll `L` ttt `T` lll) ttt) =>
 (forall e ee . Wrapper target (T'I' (tttt (t e) (tt ee)) o)) =>
 (forall e . Wrapper source (I e)) =>
 (forall e . Wrapper target (I e)) =>
 (forall e . Wrapper source (I `L` T'I'I ttttt `T` lllll `T` e)) =>
 (forall e . Wrapper target (I `L` T'I'I ttttt `T` lllll `T` e)) =>
 (forall e . Wrapper source (I `L` T'I'I ttttt `T` lllll `L` ttt `T` lll `T` e)) =>
 (forall e . Wrapper target (I `L` T'I'I ttttt `T` lllll `L` ttt `T` lll `T` e)) =>
 (forall e . Wrapper target (T'I'II target (source (ttttt a aa) (I `L` T'I'I ttttt `T` lllll `L` ttt `T` lll `T` o)) e)) =>
 (forall e . Wrapper target (T'I'II (P) (source (ttttt a aa) (I `L` T'I'I ttttt `T` lllll `L` ttt `T` lll `T` o)) e)) =>
 (Wrapper target (T'I'II (P) (T'I' (tttt (t a) (tt aa)) o) (T'I'II source (ttttt a aa) o))) =>
 (forall e . Wrapper target (I `L` (T'I'II target (source (ttttt a aa) (I `L` T'I'I ttttt `T` lllll `L` ttt `T` lll `T` o)) `T'TT'I` T'I'II (P) (source (ttttt a aa) (I `L` T'I'I ttttt `T` lllll `L` ttt `T` lll `T` o))) `T` (Void) `T` e)) =>
 (forall e . Wrapper target ((T'I'II target (source (ttttt a aa) (I `L` T'I'I ttttt `T` lllll `L` ttt `T` lll `T` o)) `T'TT'I` T'I'II (P) (source (ttttt a aa) (I `L` T'I'I ttttt `T` lllll `L` ttt `T` lll `T` o))) e)) =>
 (forall e . Wrapper target (T'II'I (P) (T'I' (tttt (t a) (tt aa)) o) e)) =>
 (forall e . Wrapper target (T'I'II source (ttttt a aa) e)) =>
 (forall e ee eee . Wrapper target ((T'I'II source (ttttt e ee) `P'T'I'TT'I` T'I' (tttt (t e) (tt ee))) eee)) =>
 (forall e ee eee . Wrapper target ((T'I'II source (ttttt e ee) `P'T'I'TT'I` T'I' (tttt (t e) (tt ee))) `L` T'I'I ttttt `T` lllll `T` eee)) =>
 (forall e ee eee . Wrapper target ((T'I'II source (ttttt e ee) `P'T'I'TT'I` T'I' (tttt (t e) (tt ee))) `L` T'I'I ttttt `T` lllll `L` ttt `T` lll `T` eee)) =>
 target (tttt (t a) (tt aa)) (target (source (ttttt a aa) (I `L` T'I'I ttttt `T` lllll `L` ttt `T` lll `T` o)) (ttt o))
yo'dc'yo'nt'yo = fio @target
  (component @target @((T'I'II source (ttttt a aa) `P'T'I'TT'I` T'I' (tttt (t a) (tt aa))) `L` T'I'I ttttt `T` lllll `L` ttt `T` lll) @ttt
  `compose` subtype `compose` subtype `compose` subtype
  `compose` foi @target (subtype)
  `compose` (foi @target `compose` fio @target) (supertype `compose` supertype `compose` supertype)
  `compose` supertype)
 `compose` (wrapped `compose` wrapped) (component @target
  @(I `L` (T'I'II target (source (ttttt a aa) (I `L` T'I'I ttttt `T` lllll `L` ttt `T` lll `T` o)) `T'TT'I` T'I'II (P) (source (ttttt a aa) (I `L` T'I'I ttttt `T` lllll `L` ttt `T` lll `T` o))) `T` (Void))
  @(T'I'II target (source (ttttt a aa) (I `L` T'I'I ttttt `T` lllll `L` ttt `T` lll `T` o)) `T'TT'I` T'I'II (P) (source (ttttt a aa) (I `L` T'I'I ttttt `T` lllll `L` ttt `T` lll `T` o))))
 `compose` subtype @target @(T'I' (tttt (t a) (tt aa)) o)

st'yo'dc'yo'nt'yo :: forall source target e a aa o t tt ttt tttt ttttt lll lllll .
 Hom Functor source =>
 Hom Functor target =>
 (forall e . Covariant Endo Semi Functor target (T'II'I (P) e)) =>
 (forall e . Covariant Endo Semi Functor target (T'I'II source e)) =>
 (forall e . Component target (I
  `L` (T'I'II target (source (ttttt a aa) (I `L` T'I'I ttttt `T` lllll `L` ttt `T` lll `T` o)) `T'TT'I` T'I'II (P) (source (ttttt a aa) (I `L` T'I'I ttttt `T` lllll `L` ttt `T` lll `T` o))) `T` (Void))
  (T'I'II target (source (ttttt a aa) (I `L` T'I'I ttttt `T` lllll `L` ttt `T` lll `T` o)) `T'TT'I` T'I'II (P) (source (ttttt a aa) (I `L` T'I'I ttttt `T` lllll `L` ttt `T` lll `T` o)))) =>
 (forall e ee . Component target ((T'I'II source (ttttt e ee) `P'T'I'TT'I` T'I' (tttt (t e) (tt ee))) `L` T'I'I ttttt `T` lllll `L` ttt `T` lll) ttt) =>
 (forall e ee . Wrapper target (T'I' (tttt (t e) (tt ee)) o)) =>
 (forall e . Wrapper source (I e)) =>
 (forall e . Wrapper target (I e)) =>
 (forall e . Wrapper source (I `L` T'I'I ttttt `T` lllll `T` e)) =>
 (forall e . Wrapper target (I `L` T'I'I ttttt `T` lllll `T` e)) =>
 (forall e . Wrapper source (I `L` T'I'I ttttt `T` lllll `L` ttt `T` lll `T` e)) =>
 (forall e . Wrapper target (I `L` T'I'I ttttt `T` lllll `L` ttt `T` lll `T` e)) =>
 (forall e . Wrapper target (T'I'II target (source (ttttt a aa) (I `L` T'I'I ttttt `T` lllll `L` ttt `T` lll `T` o)) e)) =>
 (forall e . Wrapper target (T'I'II (P) (source (ttttt a aa) (I `L` T'I'I ttttt `T` lllll `L` ttt `T` lll `T` o)) e)) =>
 (Wrapper target (T'I'II (P) (T'I' (tttt (t a) (tt aa)) o) (T'I'II source (ttttt a aa) o))) =>
 (forall e . Wrapper target (I `L` (T'I'II target (source (ttttt a aa) (I `L` T'I'I ttttt `T` lllll `L` ttt `T` lll `T` o)) `T'TT'I` T'I'II (P) (source (ttttt a aa) (I `L` T'I'I ttttt `T` lllll `L` ttt `T` lll `T` o))) `T` (Void) `T` e)) =>
 (forall e . Wrapper target ((T'I'II target (source (ttttt a aa) (I `L` T'I'I ttttt `T` lllll `L` ttt `T` lll `T` o)) `T'TT'I` T'I'II (P) (source (ttttt a aa) (I `L` T'I'I ttttt `T` lllll `L` ttt `T` lll `T` o))) e)) =>
 (forall e . Wrapper target (T'II'I (P) (T'I' (tttt (t a) (tt aa)) o) e)) =>
 (forall e . Wrapper target (T'I'II source (ttttt a aa) e)) =>
 (forall e ee eee . Wrapper target ((T'I'II source (ttttt e ee) `P'T'I'TT'I` T'I' (tttt (t e) (tt ee))) eee)) =>
 (forall e ee eee . Wrapper target ((T'I'II source (ttttt e ee) `P'T'I'TT'I` T'I' (tttt (t e) (tt ee))) `L` T'I'I ttttt `T` lllll `T` eee)) =>
 (forall e ee eee . Wrapper target ((T'I'II source (ttttt e ee) `P'T'I'TT'I` T'I' (tttt (t e) (tt ee))) `L` T'I'I ttttt `T` lllll `L` ttt `T` lll `T` eee)) =>
 Supertyping target e =>
 (Supertype e ~ tttt (t a) (tt aa)) =>
 target e (target (source (ttttt a aa) (I `L` T'I'I ttttt `T` lllll `L` ttt `T` lll `T` o)) (ttt o))
st'yo'dc'yo'nt'yo = fio @target
  (component @target @((T'I'II source (ttttt a aa) `P'T'I'TT'I` T'I' (tttt (t a) (tt aa))) `L` T'I'I ttttt `T` lllll `L` ttt `T` lll) @ttt
  `compose` subtype `compose` subtype `compose` subtype
  `compose` foi @target (subtype)
  `compose` (foi @target `compose` fio @target) (supertype `compose` supertype `compose` supertype)
  `compose` supertype)
 `compose` (wrapped `compose` wrapped) (component @target
  @(I `L` (T'I'II target (source (ttttt a aa) (I `L` T'I'I ttttt `T` lllll `L` ttt `T` lll `T` o)) `T'TT'I` T'I'II (P) (source (ttttt a aa) (I `L` T'I'I ttttt `T` lllll `L` ttt `T` lll `T` o))) `T` (Void))
  @(T'I'II target (source (ttttt a aa) (I `L` T'I'I ttttt `T` lllll `L` ttt `T` lll `T` o)) `T'TT'I` T'I'II (P) (source (ttttt a aa) (I `L` T'I'I ttttt `T` lllll `L` ttt `T` lll `T` o))))
 `compose` subtype @target @(T'I' (tttt (t a) (tt aa)) o)
 `compose` supertype @target
