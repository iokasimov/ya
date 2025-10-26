{-# LANGUAGE AllowAmbiguousTypes #-}
module Ya.Operators.Mappings where

import Ya.Algebra.Abstract
import Ya.Algebra.Definition
import Ya.Algebra.Instances ()

fo :: forall source target t a o .
 Covariant Semi Functor source target t =>
 source a o -> target (t a) (t o)
fo = map @T'I'II @T'I'II

foi :: forall source target t a o i .
 Covariant Semi Functor source target (T'II'I t i) =>
 (forall e . Wrapper target (T'II'I t i e)) =>
 source a o -> target (t a i) (t o i)
foi source = wrapped (fo @_ @_ @(T'II'I _ _) source)

fio :: forall source target t a o i .
 Covariant Semi Functor source target (T'I'II t i) =>
 (forall e . Wrapper target (T'I'II t i e)) =>
 source a o -> target (t i a) (t i o)
fio source = wrapped (fo @_ @_ @(T'I'II _ _) source)

foo :: forall source target t a o .
 Covariant Semi Functor source target (T'I'I t) =>
 (forall e . Wrapper target (T'I'I t e)) =>
 source a o -> target (t a a) (t o o)
foo source = wrapped (fo @_ @_ @(T'I'I _) source)

fuu :: forall source target t a aa o .
 Covariant Functor source target (T'I'II t a) =>
 Covariant Functor source target (T'II'I t o) =>
 (forall e ee . Wrapper target (T'I'II t e ee)) =>
 (forall e ee . Wrapper target (T'II'I t e ee)) =>
 (forall e . Wrapper (AR) (source Unit e)) =>
 Terminal source =>
 Supertype (source Unit o) -> target (t a aa) (t o o)
fuu source = fui @source @target source `compose` fiu @source @target source

fa :: forall source target t a o .
 Contravariant Semi Functor source target t =>
 source a o -> target (t o) (t a)
fa = map @T'II'I @T'I'II

faa :: forall source target t a o .
 Contravariant Semi Functor source target (T'I'I t) =>
 (forall e . Wrapper target (T'I'I t e)) =>
 source a o -> target (t o o) (t a a)
faa source = wrapped (fa @_ @_ @(T'I'I _) source)

fai :: forall source target t a o i .
 Contravariant Semi Functor source target (T'II'I t i) =>
 (forall e . Wrapper target (T'II'I t i e)) =>
 source a o -> target (t o i) (t a i)
fai source = wrapped (fa @_ @_ @(T'II'I _ _) source)

fia :: forall source target t a o i .
 Contravariant Semi Functor source target (T'I'II t i) =>
 (forall e . Wrapper target (T'I'II t i e)) =>
 source a o -> target (t i o) (t i a)
fia source = wrapped (fa @_ @_ @(T'I'II _ _) source)

fu :: forall target t a o .
 Constant Functor (AR) target t =>
 Wrapper target (I o) =>
 o -> target (t a) (t o)
fu = map @T''II @T'I'II @AR

fok :: forall source target t tt l a o .
 Component target (t `T'TT'I` tt `L` tt `T` l) t =>
 Covariant Functor source target t =>
 (forall e . Wrapper target (t `T'TT'I` tt `L` tt `T` l `T'I_` e)) =>
 source a (tt `L` tt `T` l `T` o) -> target (t a) (t o)
fok source = component @target @(t `T'TT'I` tt `L` tt `T` l) @t
 `compose` wrap `compose` fo source

fuk :: forall target t tt l a o .
 Constant Functor (AR) target t =>
 Covariant Endo Transformation Functor target (t `T'TT'I` tt `L` tt `T` l) t =>
 (forall e . Wrapper target (t `T'TT'I` tt `L` tt `T` l `T'I_` e)) =>
 (forall e . Wrapper target (I `T'I` tt `L` tt `T` l `T` e)) =>
 (tt `L` tt `T` l) o -> target (t a) (t o)
fuk source = map @T'I'II @T'I'II @target @target @(t `T'TT'I` tt `L` tt `T` l) @t identity
 `compose` wrap `compose` fu @target source

kfo :: forall source target t tt l a o .
 Component target t (t `T'TT'I` tt `L` tt `T` l) =>
 Covariant Functor source target t =>
 (forall e . Wrapper target (t `T'TT'I` tt `L` tt `T` l `T'I_` e)) =>
 source (tt `L` tt `T` l `T` a) o -> target (t a) (t o)
kfo source = fo source `compose` unwrap `compose` component @target @t @(t `T'TT'I` tt `L` tt `T` l)

fokl :: forall source target t tt l ll a o .
 Covariant Semi Functor source target t =>
 Covariant Endo Transformation Functor target (t `T'TT'I` tt `L` tt `T` ll `L` t `T` l) (t `TT'T'I` tt) =>
 (forall e . Wrapper target (t `T'TT'I` tt `L` tt `T` ll `L` t `T` l `T'I_` e)) =>
 (forall e . Wrapper target (t `TT'T'I` tt `T'I_` e)) =>
 source a (tt `L` tt `T` ll `L` t `T` l `T` o) -> target (t a) (tt (t o))
fokl source = wrapped (component @target @(t `T'TT'I` tt `L` tt `T` ll `L` t `T` l) @(t `TT'T'I` tt)) `compose` fo source

foikl :: forall source target t tt l ll a o i .
 Covariant Semi Functor source target (T'II'I t i) =>
 Covariant Endo Semi Functor target tt =>
 Covariant Endo Transformation Functor target (T'II'I t i `T'TT'I` tt `L` tt `T` ll `L` T'II'I t i `T` l) (T'II'I t i `TT'T'I` tt) =>
 (forall e . Wrapper target (T'II'I t i `T'TT'I` tt `L` tt `T` ll `L` T'II'I t i `T` l `T'I_` e)) =>
 (forall e . Wrapper target (T'II'I t i `TT'T'I` tt `T'I_` e)) =>
 (forall e . Wrapper target (T'II'I t i e)) =>
 source a (tt `L` tt `T` ll `L` T'II'I t i `T` l `T` o) -> target (t a i) (tt (t o i))
foikl source = fo @target @target unwrap `compose` fokl source `compose` wrap @_ @(T'II'I t i _)

fukl :: forall target t tt l ll a o .
 Constant Functor (AR) target t =>
 Covariant Endo Transformation Functor target (t `T'TT'I` tt `L` tt `T` ll `L` t `T` l) (t `TT'T'I` tt) =>
 (forall e . Wrapper target (t `T'TT'I` tt `L` tt `T` ll `L` t `T` l `T'I_` e)) =>
 (forall e . Wrapper target (t `TT'T'I` tt `T'I_` e)) =>
 (forall e . Wrapper target (I `T'I_` tt `L` tt `T` ll `L` t `T` l `T'I` e)) =>
 tt `L` tt `T` ll `L` t `T` l `T` o `AR__` target (t a) (tt (t o))
fukl source = wrapped (component @target @(t `T'TT'I` tt `L` tt `T` ll `L` t `T` l) @(t `TT'T'I` tt)) `compose` fu @target source

kfokl :: forall source target t tt ttt l ll lll a o .
 Covariant Semi Functor source target t =>
 Covariant Endo Transformation Functor target t (t `T'TT'I` ttt `L` ttt `T` lll) =>
 Covariant Endo Transformation Functor target (t `T'TT'I` tt `L` tt `T` ll `L` t `T` l) (t `TT'T'I` tt) =>
 (forall e . Wrapper target (t `T'TT'I` ttt `L` ttt `T` lll `T'I_` e)) =>
 (forall e . Wrapper target (t `T'TT'I` tt `L` tt `T` ll `L` t `T` l `T'I_` e)) =>
 (forall e . Wrapper target (t `TT'T'I` tt `T'I_` e)) =>
 source (ttt `L` ttt `T` lll `T` a) (tt `L` tt `T` ll `L` t `T` l `T` o) -> target (t a) (tt (t o))
kfokl source = wrapped (component @target @(t `T'TT'I` tt `L` tt `T` ll `L` t `T` l) @(t `TT'T'I` tt))
 `compose` fo source
 `compose` unwrap @target `compose` component @target @t @(t `T'TT'I` ttt `L` ttt `T` lll)

fo'fo :: forall source target t tt a o .
 Covariant Semi Functor source target tt =>
 Covariant Endo Semi Functor target t =>
 source a o -> target (t (tt a)) (t (tt o))
fo'fo source = fo @target @target (fo @source @target source)

fo'fo'fo :: forall source target t tt h a o .
 Covariant Semi Functor source target h =>
 Covariant Endo Semi Functor target tt =>
 Covariant Endo Semi Functor target t =>
 source a o -> target (t (tt (h a))) (t (tt (h o)))
fo'fo'fo source = fo @target @target (fo @target @target (fo @source @target source))

fioi :: forall source target t a o i ii .
 Covariant Semi Functor source target (W_III_I_II t ii i) =>
 (forall e . Wrapper target (W_III_I_II t ii i e)) =>
 source a o -> target (t i a ii) (t i o ii)
fioi source = wrapped (fo @_ @_ @(W_III_I_II _ _ _) source)

fiu :: forall source target t a o i .
 Terminal source =>
 Covariant Functor source target (T'I'II t i) =>
 (forall e . Wrapper target (T'I'II t i e)) =>
 (forall e . Wrapper (AR) (source Unit e)) =>
 Supertype (source Unit o) -> target (t i a) (t i o)
fiu source = fio (wrap @(AR) @(source Unit o) source `compose` terminal)

fui :: forall source target t a o i .
 Terminal source =>
 Covariant Functor source target (T'II'I t i) =>
 (forall e . Wrapper target (T'II'I t i e)) =>
 (forall e . Wrapper (AR) (source Unit e)) =>
 Supertype (source Unit o) -> target (t a i) (t o i)
fui source = foi (wrap @(AR) @(source Unit o) source `compose` terminal)

fd :: forall source target t tt a o .
 Adjoint Functor source source t tt =>
 Covariant Functor target source t =>
 (forall e . Wrapper source (t `T'TT'I` tt `T'I_` e)) =>
 (forall e . Wrapper source (I e)) =>
 target a (tt o) -> source (t a) o
fd source = wrapped (component @source @(t `T'TT'I` tt) @I) `compose` fo @target @source source

fdi :: forall source target t tt i ii a o .
 Adjoint Functor source source (T'II'I t i) (T'I'II tt ii) =>
 Covariant Functor target source (T'II'I t i) =>
 (forall e . Wrapper target (T'I'II tt ii e)) =>
 (forall e . Wrapper source (T'II'I t i `T'TT'I` T'I'II tt ii `T'I_` e)) =>
 (forall e . Wrapper source (T'II'I t i e)) =>
 (forall e . Wrapper source (I e)) =>
 target a (tt ii o) -> source (t a i) o
fdi source = wrapped (component @source @(T'II'I t i `T'TT'I` T'I'II tt ii) @I)
 `compose` fo @target @source (wrap `compose` source) `compose` wrap

fj :: forall source target t tt a o .
 Covariant Functor source target tt =>
 Adjoint Functor target target t tt =>
 (forall e . Wrapper target (tt `T'TT'I` t `T'I_` e)) =>
 (forall e . Wrapper target (I e)) =>
 source (t a) o -> target a (tt o)
fj source = fo source `compose` wrapped (component @target @I @(tt `T'TT'I` t))

fij :: forall source target t tt i ii a o .
 Covariant Functor source target (T'I'II tt ii) =>
 Adjoint Functor target target (T'II'I t i) (T'I'II tt ii) =>
 (forall e . Wrapper target (T'I'II tt ii `T'TT'I` T'II'I t i `T'I_` e)) =>
 (forall e . Wrapper target (T'I'II tt ii e)) =>
 (forall e . Wrapper source (T'II'I t i e)) =>
 (forall e . Wrapper target (I e)) =>
 source (t a i) o -> target a (tt ii o)
fij source = unwrap `compose` fo (source `compose` unwrap)
 `compose` wrapped (component @target @I @(T'I'II tt ii `T'TT'I` T'II'I t i))

-- TODO: effects are executed in reverse order, we can use it
-- to alter execution order, in Scrolling List for example
fc :: forall t a o .
 Covariant Endo Semi Functor (AR) t =>
 Covariant Endo Semi Functor (AR) (T'I'II (AR) a) =>
 Adjoint Functor (AR) (AR) (P'I'II (t a)) (T'I'II (AR) (t a)) =>
 Adjoint Functor (AR) (AR) (P'I'II a) (T'I'II (AR) a) =>
 Adjoint Functor (AR) (AR) (P'I'II (t a `P` t (AR a o))) (T'I'II (AR) (t a `P` t (AR a o))) =>
 Covariant Lax Monoidal Functor (AR) (AR) (P) P Void t =>
 t (AR a o) -> (AR) (t a) (t o)
fc = unwrap @(AR) @(T'I'II (AR) (t a) _)
 `compose` (fo @(AR) @(AR) `compose` fo @(AR) @(AR))
 (fd @(AR) @(AR) (wrap @_ @(T'I'II _ _ _)) `compose` wrap @_ @(T'I'II _ _ _))
 `compose` fj @(AR) @(AR) @(P'I'II (t a)) @(T'I'II (AR) _)
 (day @T'I'II @(AR) @Void @t @t @(P) @P identity identity
 `compose` unwrap @(AR) @(P'I'II (t a) ((t `L` t `T` Void) (AR a o))) `compose` fo @(AR) wrap)
