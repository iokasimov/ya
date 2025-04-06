{-# LANGUAGE AllowAmbiguousTypes #-}
module Ya.Algebra.Operators.Functions where

import Ya.Algebra.Abstract
import Ya.Algebra.Definition
import Ya.Algebra.Instances ()

k :: forall into t o .
 Covariant Monoidal Functor into into P P t =>
 Component into I (U_I_II into Unit) =>
 Wrapper into (U_I_II into Unit o) =>
 Wrapper into (I o) =>
 into o (t o)
k = component @into @(U_I_II into Unit) @t
 `compose` wrap `compose` constant

d :: forall into t tt o .
 Adjoint Functor into into t tt =>
 (forall e . Wrapper into (t `T'TT'I` tt `WR_` e)) =>
 (forall e . Wrapper into (I e)) =>
 into (t (tt o)) o
d = wrapped `identity` component @into @(t `T'TT'I` tt) @I

di :: forall into t tt i ii o .
 Adjoint Functor into into (U_II_I t i) (U_I_II tt ii) =>
 (forall e . Wrapper into (U_II_I t i `T'TT'I` U_I_II tt ii `WR_` e)) =>
 (forall e . Wrapper into (U_II_I t i e)) =>
 (forall e . Wrapper into (U_I_II tt ii e)) =>
 (forall e . Wrapper into (I e)) =>
 into (t (tt ii o) i) o
di = wrapped `identity` component @into @(U_II_I t i `T'TT'I` U_I_II tt ii) @I `compose` fo @into wrap `compose` wrap

j :: forall into t tt o .
 Adjoint Functor into into t tt =>
 (forall e . Wrapper into (tt `T'TT'I` t `WR_` e)) =>
 (forall e . Wrapper into (I e)) =>
 into o (tt (t o))
j = wrapped `identity` component @into @I @(tt `T'TT'I` t)

ij :: forall into t tt i ii o .
 Adjoint Functor into into (U_II_I t i) (U_I_II tt ii) =>
 (forall e . Wrapper into (U_I_II tt ii `T'TT'I` U_II_I t i `WR_` e)) =>
 (forall e . Wrapper into (U_II_I t i e)) =>
 (forall e . Wrapper into (U_I_II tt ii e)) =>
 (forall e . Wrapper into (I e)) =>
 into o (tt ii (t o i))
ij = unwrap @into `compose` fo @into unwrap
 `compose` (wrapped (component @into @I @(U_I_II tt ii `T'TT'I` U_II_I t i)))

fo :: forall from into t a o .
 Covariant Semi Functor from into t =>
 from a o -> into (t a) (t o)
fo = map @U_I_II @U_I_II

fa :: forall from into t a o .
 Contravariant Semi Functor from into t =>
 from a o -> into (t o) (t a)
fa = map @U_II_I @U_I_II

fu :: forall from into t a o .
 Covariant Functor from into t =>
 Component (->) I (U_I_II from a) =>
 Wrapper into (I o) =>
 o -> into (t a) (t o)
fu = fo @from @into @t
 `compose` constant @from @(->)

fok :: forall from into t tt l a o .
 Component into (t `T'TT'I` l `L` tt) t =>
 Covariant Functor from into t =>
 Elicitable U_II_I into (t `T'TT'I` l `L` tt `WR_` o) =>
 from a (L l tt o) -> into (t a) (t o)
fok from = component @into @(t `T'TT'I` l `L` tt) @t
 `compose` wrap `compose` fo from

fuk :: forall into t tt ll a o .
 Component (->) I (U_I_II into a) =>
 Covariant Endo Transformation Functor into (t `T'TT'I` ll `L` tt) t =>
 Constant Semi Functor into into t =>
 Wrapper into (t `T'TT'I` ll `L` tt `WR__` o) =>
 Wrapper into (I `WR_` ll `L` tt `WR` o) =>
 (ll `L` tt) o -> into (t a) (t o)
fuk from = map @U_I_II @U_I_II @into @into @(t `T'TT'I` ll `L` tt) @t identity
 `compose` wrap `compose` fu @into from

fokl :: forall from into t tt l ll a o .
 Covariant Semi Functor from into t =>
 Covariant Endo Transformation Functor into (t `T'TT'I` l `L` ll `L` tt) (t `TT'T'I` tt) =>
 Elicitable U_II_I into ((t `T'TT'I` l `L` ll `L` tt) o) =>
 Elicitable U_I_II into (TT'T'I t tt o) =>
 from a (l `L` ll `L` tt `WR` o) -> into (t a) (tt (t o))
fokl from = wrapped (component @into @(t `T'TT'I` l `L` ll `L` tt) @(t `TT'T'I` tt)) `compose` fo from

fukl :: forall into t tt l ll a o .
 Covariant Semi Functor into into t =>
 Covariant Endo Transformation Functor into (t `T'TT'I` l `L` ll `L` tt) (t `TT'T'I` tt) =>
 Component (->) I (U_I_II into a) =>
 Wrapper into (t `T'TT'I` l `L` ll `L` tt `WR_` o) =>
 Wrapper into (t `TT'T'I` tt `WR_` o) =>
 Wrapper into (I `WR_` l `L` ll `L` tt `WR` o) =>
 l `L` ll `L` tt `WR` o `AR__` into (t a) (tt (t o))
fukl from = wrapped (component @into @(t `T'TT'I` l `L` ll `L` tt) @(t `TT'T'I` tt)) `compose` fu @into from

fo'fo :: forall from into t tt a o .
 Covariant Semi Functor from into tt =>
 Covariant Endo Semi Functor into t =>
 from a o -> into (t (tt a)) (t (tt o))
fo'fo from = fo @into @into (fo @from @into from)

fo'fo'fo :: forall from into t tt h a o .
 Covariant Semi Functor from into h =>
 Covariant Endo Semi Functor into tt =>
 Covariant Endo Semi Functor into t =>
 from a o -> into (t (tt (h a))) (t (tt (h o)))
fo'fo'fo from = fo @into @into (fo @into @into (fo @from @into from))

fioi :: forall from into t a o i i_ .
 Covariant Semi Functor from into (W_III_I_II t i_ i) =>
 Wrapper into (W_III_I_II t i_ i a) =>
 Wrapper into (W_III_I_II t i_ i o) =>
 from a o -> into (t i a i_) (t i o i_)
fioi from = wrapped (fo @_ @_ @(W_III_I_II _ _ _) from)

foi :: forall from into t a o i .
 Covariant Semi Functor from into (U_II_I t i) =>
 (forall e . Wrapper into (U_II_I t i e)) =>
 from a o -> into (t a i) (t o i)
foi from = wrapped (fo @_ @_ @(U_II_I _ _) from)

fio :: forall from into t a o i .
 Covariant Semi Functor from into (U_I_II t i) =>
 (forall e ee . Wrapper into (U_I_II t e ee)) =>
 from a o -> into (t i a) (t i o)
fio from = wrapped (fo @_ @_ @(U_I_II _ _) from)

fai :: forall from into t a o i .
 Contravariant Semi Functor from into (U_II_I t i) =>
 (forall e . Wrapper into (U_II_I t i e)) =>
 from a o -> into (t o i) (t a i)
fai from = wrapped (fa @_ @_ @(U_II_I _ _) from)

fia :: forall from into t a o i .
 Contravariant Semi Functor from into (U_I_II t i) =>
 (forall e . Wrapper into (U_I_II t i e)) =>
 from a o -> into (t i o) (t i a)
fia from = wrapped (fa @_ @_ @(U_I_II _ _) from)

fiu :: forall from into t a o i .
 Terminal from =>
 Covariant Functor from into (U_I_II t i) =>
 (forall e ee . Wrapper into (U_I_II t e ee)) =>
 Wrapper (->) (from Unit o) =>
 Supertype (from Unit o) -> into (t i a) (t i o)
fiu from = fio (wrap @(->) @(from Unit o) from `compose` terminal)

fui :: forall from into t a o i .
 Terminal from =>
 Covariant Functor from into (U_II_I t i) =>
 (forall e ee . Wrapper into (U_II_I t i ee)) =>
 Wrapper (->) (from Unit o) =>
 Supertype (from Unit o) -> into (t a i) (t o i)
fui from = foi (wrap @(->) @(from Unit o) from `compose` terminal)

fd :: forall from into t tt a o .
 Adjoint Functor from from t tt =>
 Covariant Functor into from t =>
 Elicitable U_II_I from ((T'TT'I t tt) o) =>
 Elicitable U_I_II from (I o) =>
 into a (tt o) -> from (t a) o
fd from = wrapped (component @from @(t `T'TT'I` tt) @I) `compose` fo @into @from from

fdi :: forall from into t tt i ii a o .
 Adjoint Functor from from (U_II_I t i) (U_I_II tt ii) =>
 Covariant Functor into from (U_II_I t i) =>
 (forall e . Wrapper into (U_I_II tt ii e)) =>
 (forall e . Wrapper from ((U_II_I t i `T'TT'I` U_I_II tt ii) e)) =>
 (forall e . Wrapper from (U_II_I t i e)) =>
 (forall e . Wrapper from (I e)) =>
 into a (tt ii o) -> from (t a i) o
fdi from = wrapped (component @from @(U_II_I t i `T'TT'I` U_I_II tt ii) @I)
 `compose` fo @into @from (wrap `compose` from) `compose` wrap

fj :: forall from into t tt a o .
 Covariant Functor from into tt =>
 Adjoint Functor into into t tt =>
 Elicitable U_I_II into (tt `T'TT'I` t `WR_` a) =>
 Elicitable U_II_I into (I a) =>
 from (t a) o -> into a (tt o)
fj from = fo from `compose` wrapped (component @into @I @(tt `T'TT'I` t))

fij :: forall from into t tt i ii a o .
 Covariant Functor from into (U_I_II tt ii) =>
 Adjoint Functor into into (U_II_I t i) (U_I_II tt ii) =>
 (forall e . Wrapper into (U_I_II tt ii `T'TT'I` U_II_I t i `WR__` e)) =>
 (forall e . Wrapper into (U_I_II tt ii e)) =>
 (forall e . Wrapper from (U_II_I t i e)) =>
 Elicitable U_II_I into (I a) =>
 from (t a i) o -> into a (tt ii o)
fij from = unwrap `compose` fo (from `compose` unwrap)
 `compose` wrapped (component @into @I @(U_I_II tt ii `T'TT'I` U_II_I t i))

-- TODO: effects are executed in reverse order, we can use it
-- to alter execution order, in Scrolling List for example
fc :: forall into t a o .
 Covariant Endo Semi Functor (->) t =>
 Covariant Endo Semi Functor (->) (U_I_II into a) =>
 Adjoint Functor (->) (->) (U_I_II P (t a)) (U_I_II into (t a)) =>
 Adjoint Functor (->) (->) (U_I_II P a) (U_I_II into a) =>
 Adjoint Functor (->) (->) (U_I_II P (t a `P` t (into a o))) (U_I_II (->) (t a `P` t (into a o))) =>
 Monoidal U_I_II Functor into AR P P t =>
 t (into a o) -> into (t a) (t o)
fc = unwrap @(->) @(U_I_II into (t a) _)
 `compose` (fo @(->) @(->) `compose` fo @(->) @(->))
 (fd @(->) @(->) (wrap @_ @(U_I_II _ _ _)) `compose` wrap @_ @(U_I_II _ _ _))
 `compose` fj @(->) @(->) @(U_I_II P (t a)) @(U_I_II into _)
 (monoidal_ @U_I_II @into @(->) @t @P @P identity (wrap identity)
 `compose` unwrap @(->) @(U_I_II P (t a) (t (into a o))))
