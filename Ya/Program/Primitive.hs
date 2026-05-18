{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE UndecidableSuperClasses #-}
{-# LANGUAGE QuantifiedConstraints #-}
module Ya.Program.Primitive where

import Ya.Algebra
import Ya.Operators
import Ya.Program.Patterns

mirror :: Supertype (i `AT` i)
mirror x = x `hjd` identity

-- TODO: remove
sub :: forall tt t e .
 (tt ~ Construction t) =>
 Covariant Endo Semi Functor (AR) t =>
 Supertype (Construction t e `AT` t (Construction t e))
sub (F'T'I'TT (Recursive (T'TT'I (T'II'I (These xs x))))) = These
 (xs `yo` subtype @(AR) @(F'T'I'TT _ _ _))
 (\new -> new `yo` supertype @Arrow @(F'T'I'TT _ _ _) `hjd'tb` x)

embed :: forall f g e .
 Component (AR) g (f `JNT` g) =>
 g e -> (f `JNT` g) e
embed = component @(AR) @g @(f `JNT` g) @e

-- TODO: replace this expression with a label
joint :: forall f g e .
 Component (AR) (f `T'TT'I` g) (f `JNT` g)  =>
 Wrapper (AR) (f `T'TT'I` g `T'I_` e) =>
 f `T'I` g `T` e `AR_______` f `JNT` g `T'I_` e
joint = subtype @(AR) @((f `T'TT'I` g) e) `ho` component @(AR) @(f `T'TT'I` g) @(f `JNT` g) @e

-- TODO: remove
index :: forall t r e .
 (r ~ Representation t) =>
 Setoid Arrow (Representation t) =>
 Covariant Naperian Functor (AR) (AR) t =>
 Representation t `AR_` Supertype (Attribute `T'I` t e `T'I` e)
index index origin =
 let idx = map @T'I'II @T'I'II @Arrow @Arrow @t @(T'I'II (AR) (Representation t)) identity in
 let tbt = map @T'I'II @T'I'II @Arrow @Arrow @(T'I'II (AR) (Representation t)) @t identity in
 idx origin `bt'har` index `hjd`
  (\x -> tbt `ha` T'I'II `har`
   (\index' -> is `ho'ut` (idx origin `bt'har` index') `has` is `ho'ut` x `har__` index' `hjd'eq` index)
  )

derive :: forall t tt ll i .
 Multicomponent (AR) t tt ll =>
 t `L` tt `T` ll `T` i `AR____` tt `T` i
derive = multicomponent @(AR) @t @tt @ll

within :: forall t tt ll i .
 Unlabelable (AR) (t `L` tt `T` ll) =>
 Multicomponent (AT) t tt ll =>
 t `L` tt `T` ll `T` i `AR____` tt `T` i `P__` tt `T` i `AR` Unlabeled (t `L` tt `T` ll) `T` i
within = supertype @(AR) `har` multicomponent @(AT) @t @tt @ll `yio'yio'yio` unlabel @(AR)

happen :: forall t tt ll i .
 Unlabelable (AR) (t `L` tt `T` ll) =>
 Multicomponent (TR) t tt ll =>
 t `L` tt `T` ll `T` i `AR____` tt `T` i `P__` Unlabeled (t `L` tt `T` ll) `T` i
happen = supertype @(AR) `har` multicomponent @(TR) @t @tt @ll `yio'yio` unlabel @(AR)
