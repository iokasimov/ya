module Ya.Program.Interface.Match where

import Ya.Algebra

-- TODO: generalize over categories
class Excludable a r where
 on :: r `AR_` r `MN` a `ML` a

-- instance Excludable a aa => Excludable a (T e aa) where
 -- on = on `ha` unwrap @AR

instance Excludable a (l # a `ML` aa) where
 on = That `ha'he` is `la` This

instance (aa `ML` l # a `MN` a ~ aa)
 => Excludable a (aa `ML` l # a) where
 on = This `la` That `ha'he` is

instance (l # a `ML` aa `ML` aaa `MN` a ~ aa `ML` aaa)
 => Excludable a (l # a `ML` aa `ML` aaa) where
 on = That `ha'he` is `la` This `ha` This `la` This `ha` That

instance (aa `ML` l # a `ML` aaa `MN` a ~ aa `ML` aaa)
 => Excludable a (aa `ML` l # a `ML` aaa) where
 on = This `ha` This `la` That `ha'he` is `la` This `ha` That

instance (l # a `ML` aa `ML` aaa `ML` aaaa `MN` a ~ aa `ML` aaa `ML` aaaa)
 => Excludable a (l # a `ML` aa `ML` aaa `ML` aaaa) where
 on = That `ha'he` is `la` This `ha` This `ha` This `la` This `ha` This `ha` That `la` This `ha` That

instance (aa `ML` l # a `ML` aaa `ML` aaaa `MN` a ~ aa `ML` aaa `ML` aaaa)
 => Excludable a (aa `ML` l # a `ML` aaa `ML` aaaa) where
 on = This `ha` This `ha` This `la` That `ha'he` is `la` This `ha` This `ha` That `la` This `ha` That

instance (aa `ML` aaa `ML` l # a `ML` aaaa `MN` a ~ aa `ML` aaa `ML` aaaa)
 => Excludable a (aa `ML` aaa `ML` l # a `ML` aaaa) where
 on = This `ha` This `ha` This `la` This `ha` This `ha` That `la` That `ha'he` is `la` This `ha` That

{-
on' :: Excludable a r => r `AR_` Unit `ML` a
on' x = on x `yui` Unit

class Layable a r where
 lay :: a `AR_` r

instance Layable a a where
 lay = identity

instance Layable a aa => Layable a (T l aa) where
 lay = wrap `ha` lay

instance Layable a (a `ML` aa) where
 lay = This

instance Layable a (aa `ML` a) where
 lay = That

instance Layable a (a `ML` aa `ML` aaa) where
 lay = This `ha` This

instance Layable a (aa `ML` a `ML` aaa) where
 lay = This `ha` That

instance Layable (a `ML` aaa) (a `ML` aa `ML` aaa) where
 lay = This `ha` This `la` That

instance Layable (aaa `ML` a) (a `ML` aa `ML` aaa) where
 lay = That `la` This `ha` This

-- TODO: define more Layable instances

class Fittable a r where
 fit :: r `AR_` MN a r `ML` a

instance
 ( Layable aa (MN a (aa `ML` aaa) `ML` a)
 , Layable aaa (MN a (aa `ML` aaa) `ML` a)
 ) => Fittable a (aa `ML` aaa) where
 fit = lay `la` lay

instance
 ( Layable aa (MN a (aa `ML` aaa `ML` aaaa) `ML` a)
 , Layable aaa (MN a (aa `ML` aaa `ML` aaaa) `ML` a)
 , Layable aaaa (MN a (aa `ML` aaa `ML` aaaa) `ML` a)
 ) => Fittable a (aa `ML` aaa `ML` aaaa) where
 fit = lay `la` lay `la` lay

-}
