{-# LANGUAGE AllowAmbiguousTypes #-}
module Ya.Operators.Mappings where

import Ya.Algebra.Abstract
import Ya.Algebra.Definition
import Ya.Algebra.Instances ()

-- k :: forall into t o .
 -- Covariant Monoidal Functor into into (P) P t =>
 -- Component into I (T'I'II into Unit) =>
 -- Wrapper into (T'I'II into Unit o) =>
 -- Wrapper into (I o) =>
 -- into o (t o)
-- k = component @into @(T'I'II into Unit) @t
 -- `compose` wrap `compose` constant

d :: forall into t tt o .
 Adjoint Functor into into t tt =>
 (forall e . Wrapper into (t `T'TT'I` tt `T'I_` e)) =>
 (forall e . Wrapper into (I e)) =>
 into (t (tt o)) o
d = wrapped `identity` component @into @(t `T'TT'I` tt) @I

di :: forall into t tt i ii o .
 Adjoint Functor into into (T'II'I t i) (T'I'II tt ii) =>
 (forall e . Wrapper into (T'II'I t i `T'TT'I` T'I'II tt ii `T'I_` e)) =>
 (forall e . Wrapper into (T'II'I t i e)) =>
 (forall e . Wrapper into (T'I'II tt ii e)) =>
 (forall e . Wrapper into (I e)) =>
 into (t (tt ii o) i) o
di = wrapped `identity` component @into @(T'II'I t i `T'TT'I` T'I'II tt ii) @I `compose` fo @into wrap `compose` wrap

j :: forall into t tt o .
 Adjoint Functor into into t tt =>
 (forall e . Wrapper into (tt `T'TT'I` t `T'I_` e)) =>
 (forall e . Wrapper into (I e)) =>
 into o (tt (t o))
j = wrapped `identity` component @into @I @(tt `T'TT'I` t)

ij :: forall into t tt i ii o .
 Adjoint Functor into into (T'II'I t i) (T'I'II tt ii) =>
 (forall e . Wrapper into (T'I'II tt ii `T'TT'I` T'II'I t i `T'I_` e)) =>
 (forall e . Wrapper into (T'II'I t i e)) =>
 (forall e . Wrapper into (T'I'II tt ii e)) =>
 (forall e . Wrapper into (I e)) =>
 into o (tt ii (t o i))
ij = unwrap @into `compose` fo @into unwrap
 `compose` (wrapped (component @into @I @(T'I'II tt ii `T'TT'I` T'II'I t i)))

fo :: forall from into t a o .
 Covariant Semi Functor from into t =>
 from a o -> into (t a) (t o)
fo = map @T'I'II @T'I'II

fa :: forall from into t a o .
 Contravariant Semi Functor from into t =>
 from a o -> into (t o) (t a)
fa = map @T'II'I @T'I'II

fu :: forall from into t a o .
 Covariant Functor from into t =>
 Component (AR) I (T'I'II from a) =>
 Wrapper into (I o) =>
 o -> into (t a) (t o)
fu = fo @from @into @t
 `compose` constant @from @(AR)

fok :: forall from into t tt l a o .
 Component into (t `T'TT'I` l `L` tt) t =>
 Covariant Functor from into t =>
 Elicitable T'II'I into (t `T'TT'I` l `L` tt `T'I_` o) =>
 from a (l `L` tt `T'I` o) -> into (t a) (t o)
fok from = component @into @(t `T'TT'I` l `L` tt) @t
 `compose` wrap `compose` fo from

fuk :: forall into t tt ll a o .
 Component (AR) I (T'I'II into a) =>
 Covariant Endo Transformation Functor into (t `T'TT'I` ll `L` tt) t =>
 Constant Semi Functor into into t =>
 Wrapper into (t `T'TT'I` ll `L` tt `T'I_` o) =>
 Wrapper into (I `T'I_` ll `L` tt `T'I` o) =>
 (ll `L` tt) o -> into (t a) (t o)
fuk from = map @T'I'II @T'I'II @into @into @(t `T'TT'I` ll `L` tt) @t identity
 `compose` wrap `compose` fu @into from

fokl :: forall from into t tt l ll a o .
 Covariant Semi Functor from into t =>
 Covariant Endo Transformation Functor into (t `T'TT'I` l `L` ll `L` tt) (t `TT'T'I` tt) =>
 Elicitable T'II'I into ((t `T'TT'I` l `L` ll `L` tt) o) =>
 Elicitable T'I'II into (TT'T'I t tt o) =>
 from a (l `L` ll `L` tt `T'I` o) -> into (t a) (tt (t o))
fokl from = wrapped (component @into @(t `T'TT'I` l `L` ll `L` tt) @(t `TT'T'I` tt)) `compose` fo from

fukl :: forall into t tt l ll a o .
 Covariant Semi Functor into into t =>
 Covariant Endo Transformation Functor into (t `T'TT'I` l `L` ll `L` tt) (t `TT'T'I` tt) =>
 Component (AR) I (T'I'II into a) =>
 Wrapper into (t `T'TT'I` l `L` ll `L` tt `T'I_` o) =>
 Wrapper into (t `TT'T'I` tt `T'I_` o) =>
 Wrapper into (I `T'I_` l `L` ll `L` tt `T'I` o) =>
 l `L` ll `L` tt `T'I` o `AR__` into (t a) (tt (t o))
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
 Covariant Semi Functor from into (T'II'I t i) =>
 (forall e . Wrapper into (T'II'I t i e)) =>
 from a o -> into (t a i) (t o i)
foi from = wrapped (fo @_ @_ @(T'II'I _ _) from)

fio :: forall from into t a o i .
 Covariant Semi Functor from into (T'I'II t i) =>
 (forall e ee . Wrapper into (T'I'II t e ee)) =>
 from a o -> into (t i a) (t i o)
fio from = wrapped (fo @_ @_ @(T'I'II _ _) from)

fai :: forall from into t a o i .
 Contravariant Semi Functor from into (T'II'I t i) =>
 (forall e . Wrapper into (T'II'I t i e)) =>
 from a o -> into (t o i) (t a i)
fai from = wrapped (fa @_ @_ @(T'II'I _ _) from)

fia :: forall from into t a o i .
 Contravariant Semi Functor from into (T'I'II t i) =>
 (forall e . Wrapper into (T'I'II t i e)) =>
 from a o -> into (t i o) (t i a)
fia from = wrapped (fa @_ @_ @(T'I'II _ _) from)

fiu :: forall from into t a o i .
 Terminal from =>
 Covariant Functor from into (T'I'II t i) =>
 (forall e ee . Wrapper into (T'I'II t e ee)) =>
 Wrapper (AR) (from Unit o) =>
 Supertype (from Unit o) -> into (t i a) (t i o)
fiu from = fio (wrap @(AR) @(from Unit o) from `compose` terminal)

fui :: forall from into t a o i .
 Terminal from =>
 Covariant Functor from into (T'II'I t i) =>
 (forall e ee . Wrapper into (T'II'I t i ee)) =>
 Wrapper (AR) (from Unit o) =>
 Supertype (from Unit o) -> into (t a i) (t o i)
fui from = foi (wrap @(AR) @(from Unit o) from `compose` terminal)

fd :: forall from into t tt a o .
 Adjoint Functor from from t tt =>
 Covariant Functor into from t =>
 Elicitable T'II'I from ((T'TT'I t tt) o) =>
 Elicitable T'I'II from (I o) =>
 into a (tt o) -> from (t a) o
fd from = wrapped (component @from @(t `T'TT'I` tt) @I) `compose` fo @into @from from

fdi :: forall from into t tt i ii a o .
 Adjoint Functor from from (T'II'I t i) (T'I'II tt ii) =>
 Covariant Functor into from (T'II'I t i) =>
 (forall e . Wrapper into (T'I'II tt ii e)) =>
 (forall e . Wrapper from ((T'II'I t i `T'TT'I` T'I'II tt ii) e)) =>
 (forall e . Wrapper from (T'II'I t i e)) =>
 (forall e . Wrapper from (I e)) =>
 into a (tt ii o) -> from (t a i) o
fdi from = wrapped (component @from @(T'II'I t i `T'TT'I` T'I'II tt ii) @I)
 `compose` fo @into @from (wrap `compose` from) `compose` wrap

fj :: forall from into t tt a o .
 Covariant Functor from into tt =>
 Adjoint Functor into into t tt =>
 Elicitable T'I'II into (tt `T'TT'I` t `T'I_` a) =>
 Elicitable T'II'I into (I a) =>
 from (t a) o -> into a (tt o)
fj from = fo from `compose` wrapped (component @into @I @(tt `T'TT'I` t))

fij :: forall from into t tt i ii a o .
 Covariant Functor from into (T'I'II tt ii) =>
 Adjoint Functor into into (T'II'I t i) (T'I'II tt ii) =>
 (forall e . Wrapper into (T'I'II tt ii `T'TT'I` T'II'I t i `T'I_` e)) =>
 (forall e . Wrapper into (T'I'II tt ii e)) =>
 (forall e . Wrapper from (T'II'I t i e)) =>
 Elicitable T'II'I into (I a) =>
 from (t a i) o -> into a (tt ii o)
fij from = unwrap `compose` fo (from `compose` unwrap)
 `compose` wrapped (component @into @I @(T'I'II tt ii `T'TT'I` T'II'I t i))

-- TODO: effects are executed in reverse order, we can use it
-- to alter execution order, in Scrolling List for example
fc :: forall t a o .
 Covariant Endo Semi Functor (AR) t =>
 Covariant Endo Semi Functor (AR) (T'I'II (AR) a) =>
 Adjoint Functor (AR) (AR) (T'I'II (P) (t a)) (T'I'II (AR) (t a)) =>
 Adjoint Functor (AR) (AR) (T'I'II (P) a) (T'I'II (AR) a) =>
 Adjoint Functor (AR) (AR) (T'I'II (P) (t a `P` t (AR a o))) (T'I'II (AR) (t a `P` t (AR a o))) =>
 Monoidal T'I'II Functor (AR) (AR) (P) P Void t =>
 t (AR a o) -> (AR) (t a) (t o)
fc = unwrap @(AR) @(T'I'II (AR) (t a) _)
 `compose` (fo @(AR) @(AR) `compose` fo @(AR) @(AR))
 (fd @(AR) @(AR) (wrap @_ @(T'I'II _ _ _)) `compose` wrap @_ @(T'I'II _ _ _))
 `compose` fj @(AR) @(AR) @(T'I'II (P) (t a)) @(T'I'II (AR) _)
 (day @T'I'II @(AR) @Void @t @t @(P) @P identity identity
 `compose` unwrap @(AR) @(T'I'II (P) (t a) ((Void `L` t) (AR a o))) `compose` fo @(AR) wrap)
