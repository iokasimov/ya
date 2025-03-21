{-# LANGUAGE AllowAmbiguousTypes #-}
module Ya.Algebra.Operators.Functions where

import Ya.Algebra.Abstract
import Ya.Algebra.Definition
import Ya.Algebra.Instances ()

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
fu = fo @from @into @t `compose` constant @from @(->)

fok :: forall from into t tt l a o .
 Component into (t `T'TT'I` l `L` tt) t =>
 Covariant Functor from into t =>
 Elicitable U_II_I into ((t `T'TT'I` L l tt) o) =>
 from a (L l tt o) -> into (t a) (t o)
fok from = component @into @(t `T'TT'I` L l tt) @t
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
 Covariant Endo Transformation Functor into (t `T'TT'I` L l (L ll tt)) (t `TT'T'I` tt) =>
 Elicitable U_II_I into ((t `T'TT'I` l `L` ll `L` tt) o) =>
 Elicitable U_I_II into (TT'T'I t tt o) =>
 from a (L l (L ll tt) o) -> into (t a) (tt (t o))
fokl from = wrapped
 (component @into @(t `T'TT'I` l `L` ll `L` tt) @(t `TT'T'I` tt))
 `compose` fo from

fukl :: forall into t tt l ll a o .
 Covariant Semi Functor into into t =>
 Covariant Endo Transformation Functor into (t `T'TT'I` L l (L ll tt)) (t `TT'T'I` tt) =>
 Component (->) I (U_I_II into a) =>
 Elicitable U_II_I into ((t `T'TT'I` l `L` ll `L` tt) o) =>
 Elicitable U_I_II into (TT'T'I t tt o) =>
 Wrapper into (I `WR_` l `L` ll `L` tt `WR` o) =>
 L l (L ll tt) o -> into (t a) (tt (t o))
fukl from = wrapped
 (component @into @(t `T'TT'I` l `L` ll `L` tt) @(t `TT'T'I` tt))
 `compose` fu @into from

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
fioi from = unwrap `compose` fo @_ @_ @(W_III_I_II _ _ _) from `compose` wrap

foi :: forall from into t a o i .
 Covariant Semi Functor from into (U_II_I t i) =>
 (forall e . Wrapper into (U_II_I t i e)) =>
 from a o -> into (t a i) (t o i)
foi from = unwrap `compose` fo @_ @_ @(U_II_I _ _) from `compose` wrap

fio :: forall from into t a o i .
 Covariant Semi Functor from into (U_I_II t i) =>
 (forall e ee . Wrapper into (U_I_II t e ee)) =>
 from a o -> into (t i a) (t i o)
fio from = unwrap `compose` fo @_ @_ @(U_I_II _ _) from `compose` wrap

fai :: forall from into t a o i .
 Contravariant Semi Functor from into (U_II_I t i) =>
 (forall e . Wrapper into (U_II_I t i e)) =>
 from a o -> into (t o i) (t a i)
fai from = unwrap `compose` fa @_ @_ @(U_II_I _ _) from `compose` wrap

fia :: forall from into t a o i .
 Contravariant Semi Functor from into (U_I_II t i) =>
 (forall e . Wrapper into (U_I_II t i e)) =>
 from a o -> into (t i o) (t i a)
fia from = unwrap `compose` fa @_ @_ @(U_I_II _ _) from `compose` wrap

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

