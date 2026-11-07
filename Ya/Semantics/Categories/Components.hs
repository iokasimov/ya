{-# OPTIONS_GHC -fno-warn-orphans #-}
{-# LANGUAGE UndecidableInstances #-}
module Ya.Semantics.Categories.Components where

import Ya.Semantics.Structures
import Ya.Semantics.Denotation
import Ya.Semantics.Categories.Mappings

instance (Covariant Functor (AR) (AR) t, forall e . Covariant Semi Functor target (AR) (T'I'II (AR) e)) =>
 Component (AR) t (Covariant Embedding target (AR) t r) where
 component x = Embedding `identity` \e -> map @T'I'II @(AR) (wrapped (map @T'I'II @target @(AR) @(T'I'II (AR) _) (supertype e)) identity) x

instance (Contravariant Functor (AR) (AR) t, forall e . Contravariant Semi Functor target (AR) (T'II'I (AR) e)) =>
 Component (AR) t (Contravariant Embedding target (AR) t r) where
 component x = Embedding `identity` \e -> map @T'II'I @(AR) (wrapped (map @T'II'I @target @(AR) @(T'II'I (AR) _) (supertype e)) identity) x

instance (i ~ ii) => Component (AR) (T'I'II (AR) i `L` T'I'II (AR) ii `T` (Void)) (T'I'II (AR) ii) where
 component = rewrap `identity` supertype

instance (i ~ ii) => Component (AR) (T'II'I (AR) i `L` T'II'I (AR) ii `T` (Void)) (T'II'I (AR) ii) where
 component = rewrap `identity` supertype

instance (i ~ ii) => Component (AR) (T'I'II (AT) i `L` T'I'II (AR) ii `T` (Void)) (T'I'II (AR) ii) where
 component = rewrap `identity` \origin -> this `compose` supertype (supertype origin)

instance (i ~ ii) => Component (AR) (T'II'I (AT) i `L` T'II'I (AR) ii `T` (Void)) (T'II'I (AR) ii) where
 component = rewrap `identity` \origin -> this `compose` supertype (supertype origin)

instance (i ~ ii) => Component (AR) (T'I'II (TR) i `L` T'I'II (AR) ii `T` (Void)) (T'I'II (AR) ii) where
 component = rewrap `identity` \origin -> this `compose` supertype (supertype origin)

instance Component (AR) (T'I'II (P) i `L` T'I'II (AR) Unit `T` (Void)) (T'I'II (AR) Unit) where
 component = rewrap `identity` \(T'I'II (These _ x)) _ -> x

instance Component (AR) (T'II'I (P) i `L` T'I'II (AR) Unit `T` (Void)) (T'I'II (AR) Unit) where
 component = rewrap `identity` \(T'II'I (These x _)) _ -> x

instance Component (AR) (T'I'I (P) `L` T'I'II (AR) (Unit `S` Unit) `T` (Void)) (T'I'II (AR) (Unit `S` Unit)) where
 component = rewrap `identity` \(T'I'I (These x xx)) -> \case { This _ -> x; That _ -> xx }

instance Component (AR) (T'I'II (AR) (Unit `S` Unit) `L` T'I'I (P) `T` (Void)) (T'I'I (P)) where
 component = rewrap `identity` \(T'I'II x) -> These (x (This Unit)) (x (That Unit))

instance Component (AR) (T'I'II (AR) Unit `L` T'I'II (S) i `T` (Void)) (T'I'II (S) i) where
 component = rewrap `identity` \(T'I'II f) -> That (f Unit)

instance Component (AR) (T'I'II (AR) Unit `L` T'II'I (S) i `T` (Void)) (T'II'I (S) i) where
 component = rewrap `identity` \(T'I'II f) -> This (f Unit)

instance Component (AR) (T'I'II (AR) Void `L` T'I'II (S) Unit `T` (Void)) (T'I'II (S) Unit) where
 component = rewrap `identity` \_ -> This Unit

instance Component (AR) (T'I'II (AR) Unit `L` T'I'II (TR) i `T` (Void)) (T'I'II (TR) i) where
 component = rewrap `compose` rewrap `identity` \f x -> These (f Unit) x

instance Component (AR) (T'I'I (S) `L` T'I'II (AR) Unit `T` (Void)) (T'I'II (AR) Unit) where
 component = rewrap `identity` \(T'I'I x) -> case x of
  This i -> \_ -> i
  That i -> \_ -> i

instance Component (AR) (T'I'II (S) i `T'TT'I` T'I'II (S) i `L` T'I'II (S) i `T` (Void)) (T'I'II (S) i) where
 component = rewrap `identity` \case
  T'I'II (This x) -> This x
  T'I'II (That (Label (T'I'II (This x)))) -> This x
  T'I'II (That (Label (T'I'II (That x)))) -> That x

instance Component (AR) (T'II'I (S) i `T'TT'I` T'II'I (S) i `L` T'II'I (S) i `T` (Void)) (T'II'I (S) i) where
 component = rewrap `identity` \case
  T'II'I (That x) -> That x
  T'II'I (This (Label (T'II'I (That x)))) -> That x
  T'II'I (This (Label (T'II'I (This x)))) -> This x

instance Component (AR) (T'II'I (S) i `T'TT'I` T'I'II (S) i `L` T'I'II (S) i `T` (Void)) (T'II'I (S) i) where
 component = rewrap `identity` \case
  T'II'I (That x) -> That x
  T'II'I (This (Label (T'I'II (This x)))) -> That x
  T'II'I (This (Label (T'I'II (That x)))) -> This x

instance Component (AR) (T'II'I (P) i) (T'II'I (P) i `T'TT'I` T'II'I (P) i `L` T'II'I (P) i `T` (Void)) where
 component = rewrap `identity` \(These i ii) -> T'II'I (These (Label (T'II'I (These i ii))) ii)

instance Component (AR) (T'I'II (P) i) (T'I'II (P) i `T'TT'I` T'II'I (P) i `L` T'II'I (P) i `T` (Void)) where
 component = rewrap `identity` \(These i ii) -> T'I'II (These i (Label (T'II'I (These ii i))))

instance Component (AR) (T'I'II (AR) Unit `L` I `T` (Void)) I where
 component = rewrap (\(T'I'II f) -> f Unit)

-- TODO: `Match` doesn't fit here
instance
 ( forall e . Wrapper target (I e)
 , forall e . Wrapper target (t `L` t `T` l `L` I `T` ll `T` e)
 , forall e . Wrapper target (t `L` t `T` l `T` e)
 , forall e . Wrapper target (I `TT'T'I` t `T'I_` e)
 , forall e . Wrapper target (I `T'TT'I` t `L` t `T` l `L` I `T` ll `T'I_` e)
 , Covariant Endo Semi Functor target t
 ) => Component target (I `T'TT'I` t `L` t `T` l `L` I `T` ll) (I `TT'T'I` t) where
 component = rewrap `identity`
  (map @T'I'II @target @target (subtype @target @(I _))
   `compose` supertype @target @(t `L` t `T` l `T` _)
   `compose` supertype @target @(t `L` t `T` l `L` I `T` ll `T` _)
   `compose` supertype @target @(I _))

instance Component (AR) (T'I'II (AR) Unit `L` t `T` l) t => Component (AR) (I `L` t `T` l) t where
 component (Label (Identity x)) = component @(AR) @(T'I'II (AR) Unit `L` t `T` l) @t (Label (T'I'II (\_ -> x)))

instance Covariant Endo Semi Functor (AR) tt =>
 Component (AR) (T'I'II (P) i `T'TT'I` tt `L` tt `T` (Void) `L` T'I'II (P) i `T` (Void)) (T'I'II (P) i `TT'T'I` tt) where
 component = rewrap `identity` \(T'I'II (These i x)) -> map @T'I'II @(AR) @(AR) (T'I'II `compose` (i `These`)) (supertype (supertype x))

instance Covariant Endo Semi Functor (AR) tt =>
 Component (AR) (T'II'I (P) i `T'TT'I` tt `L` tt `T` (Void) `L` T'II'I (P) i `T` (Void)) (T'II'I (P) i `TT'T'I` tt) where
 component = rewrap `identity` \(T'II'I (These x i)) -> map @T'I'II @(AR) @(AR) (T'II'I `compose` (`These` i)) (supertype (supertype x))

instance
 ( Covariant Endo Semi Functor (AR) tt
 , Component (AR) (T'I'II (AR) Unit `L` tt `T` (Void)) tt
 ) => Component (AR) (T'I'II (S) i `T'TT'I` tt `L` tt `T` (Void) `L` T'I'II (S) i `T` (Void)) (T'I'II (S) i `TT'T'I` tt) where
 component = rewrap `identity` \case
  T'I'II (This x) -> component @(AR) @(T'I'II (AR) Unit `L` tt `T` (Void)) (Label (T'I'II (\_ -> T'I'II (This x))))
  T'I'II (That x) -> map @T'I'II @(AR) @(AR) (T'I'II `compose` That) (supertype (supertype x))

instance
 ( Covariant Endo Semi Functor (AR) tt
 , Component (AR) (T'I'II (AR) Unit `L` tt `T` (Void)) tt
 ) => Component (AR) (T'II'I (S) i `T'TT'I` tt `L` tt `T` (Void) `L` T'II'I (S) i `T` (Void)) (T'II'I (S) i `TT'T'I` tt) where
 component = rewrap `identity` \case
  T'II'I (This x) -> map @T'I'II @(AR) @(AR) (T'II'I `compose` This) (supertype (supertype x))
  T'II'I (That x) -> component @(AR) @(T'I'II (AR) Unit `L` tt `T` (Void)) (Label (T'I'II (\_ -> T'II'I (That x))))

{-
instance Component (AR) (t `L` T'I'II (AR) Unit `T` l) (T'I'II (AR) Unit) => Component (AR) (t `L` I `T` l) I where

 component (Label (T'I'II x)) = component @(AR) @(t `L` T'I'II (AR) Unit `T` l) @t 

 (Label (T'I'II (\_ -> x)))
-}

instance
 ( Precategory target
 , forall e . Wrapper target (I `T` e)
 , forall e . Wrapper target (I `L` I `T` (Void) `T` e)
 , forall e . Wrapper target (I `T'TT'I` I `L` I `T` (Void) `T'I_` e)
 ) => Component target (I `T'TT'I` I `L` I `T` (Void)) I where
 component = rewrap (supertype `compose` supertype `compose` supertype)

instance
 ( Precategory target
 , forall e . Wrapper target (I `T` e)
 , forall e . Wrapper target (I `L` I `T` (Void) `T` e)
 , forall e . Wrapper target (I `T'TT'I` I `L` I `T` (Void) `T'I_` e)
 ) => Component target I (I `T'TT'I` I `L` I `T` (Void)) where
 component = rewrap (subtype `compose` subtype `compose` subtype)

instance
 Component (AR) ((T'I'II (AR) (i `P` ii) `P'T'I'TT'I` T'I' (I i `P` I ii)) `L` T'I'I (P) `T` (Void) `L` I `T` (Void)) I where
 component (supertype `compose` supertype `compose` supertype -> These (T'I'II f) (T'I' (These (Identity i) (Identity ii)))) = Identity (f (These i ii))

instance Covariant Endo Semi Functor (AR) t =>
 Component (AR) ((T'I'II (AR) (i `S` ii) `P'T'I'TT'I` T'I' (t i `S` t ii)) `L` T'I'I (S) `T` (Void) `L` t `T` (Void)) t where
 component (supertype `compose` supertype `compose` supertype -> These (T'I'II f) x) = case supertype x of
  This xx -> map @T'I'II @AR @AR @t (f `compose` This) `identity` xx
  That xx -> map @T'I'II @AR @AR @t (f `compose` That) `identity` xx

instance
 Component (AR) ((T'I'II (AR) (i `P` ii) `P'T'I'TT'I` T'I' (T'I'II (AR) e i `P` T'I'II (AR) e ii)) `L` T'I'I (P) `T` (Void) `L` T'I'II (AR) e `T` (Void)) (T'I'II (AR) e) where
 component (supertype `compose` supertype `compose` supertype -> These (T'I'II f) x) = case supertype x of
  These (T'I'II g) (T'I'II h) -> T'I'II (\e -> f (These (g e) (h e)))

instance
 Component (AR) ((T'II'I (AR) (i `S` ii) `P'T'I'TT'I` T'I' (T'II'I (AR) e i `P` T'II'I (AR) e ii)) `L` T'I'I (S) `T` (Void) `L` T'II'I (AR) e `T` (Void)) (T'II'I (AR) e) where
 component (supertype `compose` supertype `compose` supertype -> These (T'II'I f) x) = case supertype x of
  These (T'II'I g) (T'II'I h) -> T'II'I ((\case { This i -> g i; That ii -> h ii; }) `compose` f)

{-
instance
 Component (AR) ((T'II'I (AR) (i `P` ii) `P'T'I'TT'I` T'I'II (S) e) `L` T'I'I (P) `T` (Void) `L` T'I'II (S) e `T` (Void)) (T'I' (T'I'II (S) e i `P` T'I'II (S) e ii)) where
 component (supertype `compose` supertype `compose` supertype -> These (T'II'I f) x) = T'I' (These (map @T'I'II @T'I'II (this `compose` f) x) (map @T'I'II @T'I'II (that `compose` f) x))

instance
 Component (AR) ((T'II'I (AR) (i `S` ii) `P'T'I'TT'I` T'I'II (AR) e) `L` T'I'I (P) `T` (Void) `L` T'I'II (AR) e `T` (Void)) (T'I' (T'I'II (AR) e i `P` T'I'II (AR) e ii)) where

 component (supertype `compose` supertype `compose` supertype -> These (T'I'II f) (T'I'II g)) = T'I' (These () ())

  -- T'I' (These (map @T'I'II @T'I'II (this `compose` f) x) (map @T'I'II @T'I'II (that `compose` f) x))

-- f: i `S` ii `AR` o


-- f: o `AR` i `S` ii
-- g: e `AR` o

-- e `AR` i
-- e `AR` ii
-}

{-
 Component (AR) (T'II'I (AR) e) ((T'I'II (AR) (i `S` ii) `P'T'I'TT'I` T'I' (T'II'I (AR) e i `P` T'II'I (AR) e ii)) `L` T'I'I (P) `T` (Void) `L` T'I'II (AR) e `T` (Void)) where
 -- component (supertype `compose` supertype `compose` supertype -> These (T'II'I f) x) = case supertype x of
 component = rewrap `identity` \x -> These
  ()
  ()
--
-- f: i `S` ii `AR` o
-}

instance
 Component (AR) ((T'I'II (AR) (i `P` ii) `P'T'I'TT'I` T'I' (T'I'II (S) e i `P` T'I'II (S) e ii)) `L` T'I'I (P) `T` (Void) `L` T'I'II (S) e `T` (Void)) (T'I'II (S) e) where
 component (supertype `compose` supertype `compose` supertype -> These (T'I'II f) x) = case supertype x of
  These (T'I'II (That ii)) (T'I'II (That iii)) -> T'I'II (That (f (These ii iii)))
  These (T'I'II (This i)) _ -> T'I'II (This i)
  These _ (T'I'II (This i)) -> T'I'II (This i)

instance
 Component (AR) ((T'I'II (AR) (i `S` ii) `P'T'I'TT'I` T'I' (T'I'II (S) e i `P` T'I'II (S) e ii)) `L` T'I'I (S) `T` (Void) `L` T'I'II (S) e `T` (Void)) (T'I'II (S) e) where
 component (supertype `compose` supertype `compose` supertype -> These (T'I'II f) x) = case supertype x of
  These (T'I'II (This i)) (T'I'II (This ii)) -> T'I'II (This i)
  These (T'I'II (This i)) (T'I'II (That ii)) -> T'I'II (That (f (That ii)))
  These (T'I'II (That i)) _ -> T'I'II (That (f (This i)))

instance
 Component (AR) ((T'I'II (AR) (i `W` ii) `P'T'I'TT'I` T'I' (T'I'II (S) e i `P` T'I'II (S) e ii)) `L` T'I'I (W) `T` (Void) `L` T'I'II (S) e `T` (Void)) (T'I'II (S) e) where
 component (supertype `compose` supertype `compose` supertype -> These (T'I'II f) x) = case supertype x of
  These (T'I'II (That ee)) (T'I'II (That eee)) -> T'I'II (That (f (T'T'I'II'TT'I'II (That (These ee eee)))))
  These (T'I'II (That ee)) (T'I'II (This e)) -> T'I'II (That (f (T'T'I'II'TT'I'II (This (This ee)))))
  These (T'I'II (This i)) (T'I'II (That ii)) -> T'I'II (That (f (T'T'I'II'TT'I'II (This (That ii)))))
  These (T'I'II (This i)) (T'I'II (This _)) -> T'I'II (This i)

{-
instance
 Component (AR) ((T'I'II (AR) (i `P` ii) `P'T'I'TT'I` T'I' (T'I'II (TR) e i `P` T'I'II (TR) e ii)) `L` T'I'I (P) `T` (Void) `L` T'I'II (TR) e `T` (Void)) (T'I'II (TR) e) where
 component (supertype `compose` supertype `compose` supertype -> These (T'I'II f) (T'I' (These (T'I'II (T'I'TT'II'I x)) (T'I'II (T'I'TT'II'I xx))))) =
  T'I'II `compose` T'I'TT'II'I `identity` \old ->
   let These i new = x old in
   let These ii upd  = xx new in
   (f (i `These` ii)) `These` upd
-}

instance -- TODO: make one `Plain` and another one `Stack`?
 Component (AR) (T'I'II (AR) Unit `L` (T'I'II (AR) i `T'TT'I` T'II'I (P) i) `T` (Void)) (T'I'II (AR) i `T'TT'I` T'II'I (P) i) where
 component = rewrap `compose` rewrap `identity` \f x -> T'II'I (These (f Unit) x)

instance
 Component (AR) (T'I'II (AR) Unit `L` (T'I'II (AR) i `T'TT'I` T'I'II (P) i) `T` (Void)) (T'I'II (AR) i `T'TT'I` T'I'II (P) i) where
 component = rewrap `compose` rewrap `identity` \f x -> T'I'II (These x (f Unit))

instance
 Component (AR) (T'I'II (AR) Void `L` t `T` (Void)) t =>
 Component (AR) (T'I'II (AR) Unit `L` F'T'I'TT (T'II'I P) t `T` (Void `P` Void)) (F'T'I'TT (T'II'I P) t) where
 component = rewrap `compose` rewrap `identity` \f -> T'TT'I `compose` T'II'I `identity` (component @(AR) @(T'I'II (AR) Void `L` t `T` (Void)) @t (Label (T'I'II initial)) `These` f Unit)

instance
 Component (AR) (T'I'II (AR) (i `S` Unit) `L` F'T'I'TT (T'II'I P) (T'I'II (S) Unit) `T` (Void `P` Void)) (F'T'I'TT (T'II'I P) (T'I'II (S) Unit)) =>
 Component (AR) (T'I'II (AR) (i `S` Unit) `L` ((T'I'II (S) Unit) `T'TT'I` F'T'I'TT (T'II'I P) (T'I'II (S) Unit)) `T` (Void `P` Void)) ((T'I'II (S) Unit) `T'TT'I` F'T'I'TT (T'II'I P) (T'I'II (S) Unit)) where
 component = T'TT'I `compose` T'I'II `compose` That
  `compose` component @(AR) @(T'I'II (AR) (i `S` Unit) `L` F'T'I'TT (T'II'I P) (T'I'II (S) Unit) `T` (Void `P` Void)) @(F'T'I'TT (T'II'I P) (T'I'II (S) Unit))
  `compose` rewrap @(AR)
    @(T'I'II (AR) (i `S` Unit) `L` ((T'I'II (S) Unit) `T'TT'I` F'T'I'TT (T'II'I P) (T'I'II (S) Unit)) `T` (Void `P` Void) `T` _)
    @(T'I'II (AR) (i `S` Unit) `L` F'T'I'TT (T'II'I P) (T'I'II (S) Unit) `T` (Void `P` Void) `T` _)
    identity

instance
 Component (AR) (T'I'II (AR) i `L` (T'I'II (S) Unit `T'TT'I` F'T'I'TT (T'II'I P) (T'I'II (S) Unit)) `T` (Void `P` Void)) (T'I'II (S) Unit `T'TT'I` F'T'I'TT (T'II'I P) (T'I'II (S) Unit)) =>
 Component (AR) (T'I'II (AR) (i `S` Unit) `L` F'T'I'TT (T'II'I P) (T'I'II (S) Unit) `T` (Void `P` Void)) (F'T'I'TT (T'II'I P) (T'I'II (S) Unit)) where
 component (Label (T'I'II f)) = boundtype
  (map @T'I'II @(AR) @(AR) supertype (supertype (component @(AR)
   @(T'I'II (AR) i `L` (T'I'II (S) Unit `T'TT'I` F'T'I'TT (T'II'I P) (T'I'II (S) Unit)) `T` (Void `P` Void))
   @(T'I'II (S) Unit `T'TT'I` F'T'I'TT (T'II'I P) (T'I'II (S) Unit))
   `identity` (Label `compose` T'I'II `identity` (f `compose` This))))
  `These` supertype (f `compose` That))

instance Component (AR) (T'I'II (AR) Unit `L` F'T'I'TT (T'II'I (P)) (T'I'II (S) Unit) `T` (Void `P` Void)) (F'T'I'TT (T'II'I P) (T'I'II (S) Unit)) where
 component = rewrap `identity` \(T'I'II f) -> boundtype ((T'I'II (This Unit)) `These` supertype f)

instance Component (AR) (T'I'II (AR) Unit `L` (T'I'II (S) Unit `T'TT'I` F'T'I'TT (T'II'I P) (T'I'II (S) Unit)) `T` (Void `P` Void)) (T'I'II (S) Unit `T'TT'I` F'T'I'TT (T'II'I P) (T'I'II (S) Unit)) where
 component (Label (T'I'II f)) = T'TT'I `compose` T'I'II `compose` That `identity` boundtype ((T'I'II `compose` This `identity` Unit) `These` supertype f)

instance
 Component (AR) (T'I'II (AR) Void `L` t `T` (Void)) t =>
 Component (AR) (T'I'II (AR) Unit `L` F'T'I'TT (T'II'I P) t `T` (Void)) (F'T'I'TT (T'II'I P) t) where
 component = rewrap `compose` rewrap `identity` \f -> T'TT'I `compose` T'II'I `identity` (component @(AR) @(T'I'II (AR) Void `L` t `T` (Void)) @t (Label (T'I'II initial)) `These` f Unit)
