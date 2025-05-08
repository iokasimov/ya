module Ya.Program.Interface.Match where

import Ya.Algebra
import Ya.Operators

-- TODO: generalize over categories
class Excludable a r where
 on :: r `AR_` (r `M` a) `S` a

-- instance Excludable a aa => Excludable a (T e aa) where
 -- on = on `ha` unwrap @(AR)

instance Excludable a ((l # a) `S` aa) where
 on = That `ha'he` is `la` This

instance ((aa `S` (l # a) `M` a) ~ (aa))
 => Excludable a (aa `S` (l # a)) where
 on = This `la` That `ha'he` is

instance (((l # a) `S` aa `S` aaa `M` a) ~ (aa `S` aaa))
 => Excludable a ((l # a) `S` aa `S` aaa) where
 on = That `ha'he` is `la` This `ha` This `la` This `ha` That

instance ((aa `S` (l # a) `S` aaa `M` a) ~ (aa `S` aaa))
 => Excludable a (aa `S` (l # a) `S` aaa) where
 on = This `ha` This `la` That `ha'he` is `la` This `ha` That

instance (((l # a) `S` aa `S` aaa `S` aaaa `M` a) ~ (aa `S` aaa `S` aaaa))
 => Excludable a ((l # a) `S` aa `S` aaa `S` aaaa) where
 on = That `ha'he` is `la` This `ha` This `ha` This `la` This `ha` This `ha` That `la` This `ha` That

instance ((aa `S` (l # a) `S` aaa `S` aaaa `M` a) ~ (aa `S` aaa `S` aaaa))
 => Excludable a (aa `S` (l # a) `S` aaa `S` aaaa) where
 on = This `ha` This `ha` This `la` That `ha'he` is `la` This `ha` This `ha` That `la` This `ha` That

instance ((aa `S` aaa `S` (l # a) `S` aaaa `M` a) ~ (aa `S` aaa `S` aaaa))
 => Excludable a (aa `S` aaa `S` (l # a) `S` aaaa) where
 on = This `ha` This `ha` This `la` This `ha` This `ha` That `la` That `ha'he` is `la` This `ha` That

{-
on' :: Excludable a r => r `AR_` Unit `S` a
on' x = on x `yui` Unit

class Layable a r where
 lay :: a `AR_` r

instance Layable a a where
 lay = identity

instance Layable a aa => Layable a (T l aa) where
 lay = wrap `ha` lay

instance Layable a (a `S` aa) where
 lay = This

instance Layable a (aa `S` a) where
 lay = That

instance Layable a (a `S` aa `S` aaa) where
 lay = This `ha` This

instance Layable a (aa `S` a `S` aaa) where
 lay = This `ha` That

instance Layable (a `S` aaa) (a `S` aa `S` aaa) where
 lay = This `ha` This `la` That

instance Layable (aaa `S` a) (a `S` aa `S` aaa) where
 lay = That `la` This `ha` This

-- TODO: define more Layable instances

class Fittable a r where
 fit :: r `AR_` (M) a r `S` a

instance
 ( Layable aa (M a (aa `S` aaa) `S` a)
 , Layable aaa (M a (aa `S` aaa) `S` a)
 ) => Fittable a (aa `S` aaa) where
 fit = lay `la` lay

instance
 ( Layable aa (M a (aa `S` aaa `S` aaaa) `S` a)
 , Layable aaa (M a (aa `S` aaa `S` aaaa) `S` a)
 , Layable aaaa (M a (aa `S` aaa `S` aaaa) `S` a)
 ) => Fittable a (aa `S` aaa `S` aaaa) where
 fit = lay `la` lay `la` lay

-}
