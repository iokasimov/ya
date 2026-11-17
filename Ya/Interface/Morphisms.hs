{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE UndecidableInstances #-}
module Ya.Interface.Morphisms where

import Ya.Semantics
import Ya.Operators

class Multicomponent target t tt ll where
 multicomponent :: target (t `L` tt `T` ll `T` i) (tt i)

instance {-# OVERLAPPABLE #-}
 ( Component target (t `L` tt `T` ll) tt
 ) => Multicomponent target t tt ll where
 multicomponent = component @target @(t `L` tt `T` ll) @tt

instance {-# OVERLAPPABLE #-}
 ( Semicategory target
 , forall e . Wrapper target (tt `L` ttt `T` lll `T` e)
 , forall e . Wrapper target (t `L` tt `T` ll `L` ttt `T` lll `T` e)
 , Component target (t `L` tt `T` ll) tt
 , Component target (tt `L` ttt `T` lll) ttt
 ) => Multicomponent target (t `L` tt `T` ll) ttt lll where
 multicomponent = component @target @(tt `L` ttt `T` lll) @ttt
  `compose` subtype @target @(tt `L` ttt `T` lll `T` _)
  `compose` component @target @(t `L` tt `T` ll) @tt
  `compose` supertype @target @(t `L` tt `T` ll `L` ttt `T` lll `T` _)

instance {-# OVERLAPPABLE #-}
 ( Semicategory target
 , forall e . Wrapper target (tt `L` ttt `T` lll `T` e)
 , forall e . Wrapper target (ttt `L` tttt `T` llll `T` e)
 , forall e . Wrapper target (t `L` tt `T` ll `L` ttt `T` lll `T` e)
 , forall e . Wrapper target (tt `L` ttt `T` lll `L` tttt `T` llll `T` e)
 , forall e . Wrapper target (t `L` tt `T` ll `L` ttt `T` lll `L` tttt `T` llll `T` e)
 , Component target (t `L` tt `T` ll) tt
 , Component target (tt `L` ttt `T` lll) ttt
 , Component target (ttt `L` tttt `T` llll) tttt
 ) => Multicomponent target (t `L` tt `T` ll `L` ttt `T` lll) tttt llll where
 multicomponent = component @target @(ttt `L` tttt `T` llll) @tttt
  `compose` rewrap (component @target @(tt `L` ttt `T` lll) @ttt)
  `compose` subtype @target @(tt `L` ttt `T` lll `L` tttt `T` llll `T` _)
  `compose` subtype @target @(tt `L` ttt `T` lll `T` _)
  `compose` component @target @(t `L` tt `T` ll) @tt
  `compose` supertype @target @(t `L` tt `T` ll `L` ttt `T` lll `T` _)
  `compose` supertype @target @(t `L` tt `T` ll `L` ttt `T` lll `L` tttt `T` llll `T` _)

type family Unlabeled t where
 Unlabeled (t `L` tt `T` l) = Unlabeled t
 Unlabeled t = t

class Unlabelable target t where
 unlabel :: target (t i) (Unlabeled t i)

instance {-# OVERLAPPABLE #-}
 ( Semicategory target
 , forall i . Wrapper target (t `L` tt `T` l `T` i)
 , Unlabeled (t `L` tt `T` l) ~ t
 ) => Unlabelable target (t `L` tt `T` l) where
 unlabel = supertype @target

instance {-# OVERLAPPABLE #-}
 ( Semicategory target
 , forall i . Wrapper target (t `L` tt `T` l `T` i)
 , forall i . Wrapper target (t `L` tt `T` l `L` ttt `T` ll `T` i)
 , Unlabeled (t `L` tt `T` l `L` ttt `T` ll) ~ t
 ) => Unlabelable target (t `L` tt `T` l `L` ttt `T` ll) where
 unlabel = supertype @target `compose` supertype @target

instance {-# OVERLAPPABLE #-}
 ( Semicategory target
 , forall i . Wrapper target (t `L` tt `T` l `T` i)
 , forall i . Wrapper target (t `L` tt `T` l `L` ttt `T` ll `T` i)
 , forall i . Wrapper target (t `L` tt `T` l `L` ttt `T` ll `L` tttt `T` lll `T` i)
 , Unlabeled (t `L` tt `T` l `L` ttt `T` ll `L` tttt `T` lll) ~ t
 ) => Unlabelable target (t `L` tt `T` l `L` ttt `T` ll `L` tttt `T` lll) where
 unlabel = supertype @target `compose` supertype @target `compose` supertype @target

derive :: forall tt t ll i .
 Multicomponent (AR) t tt ll =>
 t `L` tt `T` ll `T` i `AR____` tt `T` i
derive = multicomponent @(AR) @t @tt @ll

within :: forall tt t ll i .
 Unlabelable (AR) (t `L` tt `T` ll) =>
 Multicomponent (AT) t tt ll =>
 t `L` tt `T` ll `T` i `AR____` tt `T` i `P__` tt `T` i `AR` Unlabeled (t `L` tt `T` ll) `T` i
within = supertype @(AR) `ha'nt'ha` multicomponent @(AT) @t @tt @ll `yio'yio'yio` unlabel @(AR)

happen :: forall tt t ll i .
 Unlabelable (AR) (t `L` tt `T` ll) =>
 Multicomponent (TR) t tt ll =>
 t `L` tt `T` ll `T` i `AR____` tt `T` i `P__` Unlabeled (t `L` tt `T` ll) `T` i
happen = supertype @(AR) `ha'nt'ha` multicomponent @(TR) @t @tt @ll `yio'yio` unlabel @(AR)

class Fieldable i r where
 -- TODO: generalise over categories?
 record :: Supertype (r `AT` i)

instance {-# OVERLAPPABLE #-}
 ( Covariant Objective (AR) ee (eee `P` eeee)
 , Contravariant Objective (AR) ee (eee `P` eeee)
 , Fieldable e (eee `P` eeee)
 ) => Fieldable e ee where
 record = (fio @(AR) `compose` fio @(AR))
   (objective @T'II'I @AR @ee @(eee `P` eeee))
  `compose` record @e @(eee `P` eeee)
  `compose` objective @T'I'II @AR @ee @(eee `P` eeee)

instance Fieldable e e where
 record x = These x identity

instance Fieldable e (ee `P` e) where
 record (These x xx) = These xx (These x)

instance {-# OVERLAPS #-} Fieldable e ee => Fieldable e (ee `P` eee) where
 record (These x xs) = (this `ha` record @e @ee `ha'nt'ha` x) `These` (that `ha` record @e @ee `ha'nt'ha` x `ho_` (`These` xs))

itself :: Category AR_ => e `AR_` e
itself = identity

mirror :: Supertype (i `AT` i)
mirror x = These x identity
