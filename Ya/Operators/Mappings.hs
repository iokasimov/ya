{-# LANGUAGE AllowAmbiguousTypes #-}
module Ya.Operators.Mappings where

import Ya.Algebra.Abstract
import Ya.Algebra.Definition
import Ya.Algebra.Instances ()

fo :: forall source into t a o .
 Covariant Semi Functor source into t =>
 source a o -> into (t a) (t o)
fo = map @T'I'II @T'I'II

foi :: forall source into t a o i .
 Covariant Semi Functor source into (T'II'I t i) =>
 (forall e . Wrapper into (T'II'I t i e)) =>
 source a o -> into (t a i) (t o i)
foi source = wrapped (fo @_ @_ @(T'II'I _ _) source)

fio :: forall source into t a o i .
 Covariant Semi Functor source into (T'I'II t i) =>
 (forall e . Wrapper into (T'I'II t i e)) =>
 source a o -> into (t i a) (t i o)
fio source = wrapped (fo @_ @_ @(T'I'II _ _) source)

foo :: forall source into t a o .
 Covariant Semi Functor source into (T'I'I t) =>
 (forall e . Wrapper into (T'I'I t e)) =>
 source a o -> into (t a a) (t o o)
foo source = wrapped (fo @_ @_ @(T'I'I _) source)

fuu :: forall source into t a aa o .
 Covariant Functor source into (T'I'II t a) =>
 Covariant Functor source into (T'II'I t o) =>
 (forall e ee . Wrapper into (T'I'II t e ee)) =>
 (forall e ee . Wrapper into (T'II'I t e ee)) =>
 (forall e . Wrapper (AR) (source Unit e)) =>
 Terminal source =>
 Supertype (source Unit o) -> into (t a aa) (t o o)
fuu source = fui @source @into source `compose` fiu @source @into source

fa :: forall source into t a o .
 Contravariant Semi Functor source into t =>
 source a o -> into (t o) (t a)
fa = map @T'II'I @T'I'II

faa :: forall source into t a o .
 Contravariant Semi Functor source into (T'I'I t) =>
 (forall e . Wrapper into (T'I'I t e)) =>
 source a o -> into (t o o) (t a a)
faa source = wrapped (fa @_ @_ @(T'I'I _) source)

fai :: forall source into t a o i .
 Contravariant Semi Functor source into (T'II'I t i) =>
 (forall e . Wrapper into (T'II'I t i e)) =>
 source a o -> into (t o i) (t a i)
fai source = wrapped (fa @_ @_ @(T'II'I _ _) source)

fia :: forall source into t a o i .
 Contravariant Semi Functor source into (T'I'II t i) =>
 (forall e . Wrapper into (T'I'II t i e)) =>
 source a o -> into (t i o) (t i a)
fia source = wrapped (fa @_ @_ @(T'I'II _ _) source)

fu :: forall into t a o .
 Constant Functor (AR) into t =>
 Wrapper into (I o) =>
 o -> into (t a) (t o)
fu = map @T''II @T'I'II @AR

fok :: forall source into t tt l a o .
 Component into (t `T'TT'I` tt `L` tt `T` l) t =>
 Covariant Functor source into t =>
 (forall e . Wrapper into (t `T'TT'I` tt `L` tt `T` l `T'I_` e)) =>
 source a (tt `L` tt `T` l `T` o) -> into (t a) (t o)
fok source = component @into @(t `T'TT'I` tt `L` tt `T` l) @t
 `compose` wrap `compose` fo source

fuk :: forall into t tt l a o .
 Constant Functor (AR) into t =>
 Covariant Endo Transformation Functor into (t `T'TT'I` tt `L` tt `T` l) t =>
 (forall e . Wrapper into (t `T'TT'I` tt `L` tt `T` l `T'I_` e)) =>
 (forall e . Wrapper into (I `T'I` tt `L` tt `T` l `T` e)) =>
 (tt `L` tt `T` l) o -> into (t a) (t o)
fuk source = map @T'I'II @T'I'II @into @into @(t `T'TT'I` tt `L` tt `T` l) @t identity
 `compose` wrap `compose` fu @into source

fokl :: forall source into t tt l ll a o .
 Covariant Semi Functor source into t =>
 Covariant Endo Transformation Functor into (t `T'TT'I` tt `L` tt `T` ll `L` t `T` l) (t `TT'T'I` tt) =>
 (forall e . Wrapper into (t `T'TT'I` tt `L` tt `T` ll `L` t `T` l `T'I_` e)) =>
 (forall e . Wrapper into (t `TT'T'I` tt `T'I_` e)) =>
 source a (tt `L` tt `T` ll `L` t `T` l `T` o) -> into (t a) (tt (t o))
fokl source = wrapped (component @into @(t `T'TT'I` tt `L` tt `T` ll `L` t `T` l) @(t `TT'T'I` tt)) `compose` fo source

foikl :: forall source into t tt l ll a o i .
 Covariant Semi Functor source into (T'II'I t i) =>
 Covariant Endo Semi Functor into tt =>
 Covariant Endo Transformation Functor into (T'II'I t i `T'TT'I` tt `L` tt `T` ll `L` T'II'I t i `T` l) (T'II'I t i `TT'T'I` tt) =>
 (forall e . Wrapper into (T'II'I t i `T'TT'I` tt `L` tt `T` ll `L` T'II'I t i `T` l `T'I_` e)) =>
 (forall e . Wrapper into (T'II'I t i `TT'T'I` tt `T'I_` e)) =>
 (forall e . Wrapper into (T'II'I t i e)) =>
 source a (tt `L` tt `T` ll `L` T'II'I t i `T` l `T` o) -> into (t a i) (tt (t o i))
foikl source = fo @into @into unwrap `compose` fokl source `compose` wrap @_ @(T'II'I t i _)

fukl :: forall into t tt l ll a o .
 Constant Functor (AR) into t =>
 Covariant Endo Transformation Functor into (t `T'TT'I` tt `L` tt `T` ll `L` t `T` l) (t `TT'T'I` tt) =>
 (forall e . Wrapper into (t `T'TT'I` tt `L` tt `T` ll `L` t `T` l `T'I_` e)) =>
 (forall e . Wrapper into (t `TT'T'I` tt `T'I_` e)) =>
 (forall e . Wrapper into (I `T'I_` tt `L` tt `T` ll `L` t `T` l `T'I` e)) =>
 tt `L` tt `T` ll `L` t `T` l `T` o `AR__` into (t a) (tt (t o))
fukl source = wrapped (component @into @(t `T'TT'I` tt `L` tt `T` ll `L` t `T` l) @(t `TT'T'I` tt)) `compose` fu @into source

fo'fo :: forall source into t tt a o .
 Covariant Semi Functor source into tt =>
 Covariant Endo Semi Functor into t =>
 source a o -> into (t (tt a)) (t (tt o))
fo'fo source = fo @into @into (fo @source @into source)

fo'fo'fo :: forall source into t tt h a o .
 Covariant Semi Functor source into h =>
 Covariant Endo Semi Functor into tt =>
 Covariant Endo Semi Functor into t =>
 source a o -> into (t (tt (h a))) (t (tt (h o)))
fo'fo'fo source = fo @into @into (fo @into @into (fo @source @into source))

fioi :: forall source into t a o i ii .
 Covariant Semi Functor source into (W_III_I_II t ii i) =>
 (forall e . Wrapper into (W_III_I_II t ii i e)) =>
 source a o -> into (t i a ii) (t i o ii)
fioi source = wrapped (fo @_ @_ @(W_III_I_II _ _ _) source)

fiu :: forall source into t a o i .
 Terminal source =>
 Covariant Functor source into (T'I'II t i) =>
 (forall e . Wrapper into (T'I'II t i e)) =>
 (forall e . Wrapper (AR) (source Unit e)) =>
 Supertype (source Unit o) -> into (t i a) (t i o)
fiu source = fio (wrap @(AR) @(source Unit o) source `compose` terminal)

fui :: forall source into t a o i .
 Terminal source =>
 Covariant Functor source into (T'II'I t i) =>
 (forall e . Wrapper into (T'II'I t i e)) =>
 (forall e . Wrapper (AR) (source Unit e)) =>
 Supertype (source Unit o) -> into (t a i) (t o i)
fui source = foi (wrap @(AR) @(source Unit o) source `compose` terminal)

fd :: forall source into t tt a o .
 Adjoint Functor source source t tt =>
 Covariant Functor into source t =>
 (forall e . Wrapper source (t `T'TT'I` tt `T'I_` e)) =>
 (forall e . Wrapper source (I e)) =>
 into a (tt o) -> source (t a) o
fd source = wrapped (component @source @(t `T'TT'I` tt) @I) `compose` fo @into @source source

fdi :: forall source into t tt i ii a o .
 Adjoint Functor source source (T'II'I t i) (T'I'II tt ii) =>
 Covariant Functor into source (T'II'I t i) =>
 (forall e . Wrapper into (T'I'II tt ii e)) =>
 (forall e . Wrapper source (T'II'I t i `T'TT'I` T'I'II tt ii `T'I_` e)) =>
 (forall e . Wrapper source (T'II'I t i e)) =>
 (forall e . Wrapper source (I e)) =>
 into a (tt ii o) -> source (t a i) o
fdi source = wrapped (component @source @(T'II'I t i `T'TT'I` T'I'II tt ii) @I)
 `compose` fo @into @source (wrap `compose` source) `compose` wrap

fj :: forall source into t tt a o .
 Covariant Functor source into tt =>
 Adjoint Functor into into t tt =>
 (forall e . Wrapper into (tt `T'TT'I` t `T'I_` e)) =>
 (forall e . Wrapper into (I e)) =>
 source (t a) o -> into a (tt o)
fj source = fo source `compose` wrapped (component @into @I @(tt `T'TT'I` t))

fij :: forall source into t tt i ii a o .
 Covariant Functor source into (T'I'II tt ii) =>
 Adjoint Functor into into (T'II'I t i) (T'I'II tt ii) =>
 (forall e . Wrapper into (T'I'II tt ii `T'TT'I` T'II'I t i `T'I_` e)) =>
 (forall e . Wrapper into (T'I'II tt ii e)) =>
 (forall e . Wrapper source (T'II'I t i e)) =>
 (forall e . Wrapper into (I e)) =>
 source (t a i) o -> into a (tt ii o)
fij source = unwrap `compose` fo (source `compose` unwrap)
 `compose` wrapped (component @into @I @(T'I'II tt ii `T'TT'I` T'II'I t i))

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
