module Ya.Program.Interface.Matchable where

import Ya.Algebra
import Ya.Operators
import Ya.Program.Primitive

-- TODO: generalize over categories
class Matchable target entire where
 on :: entire `AR_` entire `M` target `S` target

-- instance Matchable a aa => Matchable a (Tagged e aa) where
 -- on = on `ha` unwrap @(AR)

instance Matchable e (e `S` ee) where
 on = That `ha` is `la` This

instance ((ee `S` e `M` e) ~ (ee))
 => Matchable e (ee `S` e) where
 on = This `la` That `ha` is

instance ((e `S` ee `S` eee `M` e) ~ (ee `S` eee))
 => Matchable e (e `S` ee `S` eee) where
 on = That `ha` is `la` This `ha` This `la` This `ha` That

instance ((ee `S` e `S` eee `M` e) ~ (ee `S` eee))
 => Matchable e (ee `S` e `S` eee) where
 on = This `ha` This `la` That `ha` is `la` This `ha` That

instance ((e `S` ee `S` eee `S` eeee `M` e) ~ (ee `S` eee `S` eeee))
 => Matchable e (e `S` ee `S` eee `S` eeee) where
 on = That `ha` is `la` This `ha` This `ha` This `la` This `ha` This `ha` That `la` This `ha` That

instance ((ee `S` e `S` eee `S` eeee `M` e) ~ (ee `S` eee `S` eeee))
 => Matchable e (ee `S` e `S` eee `S` eeee) where
 on = This `ha` This `ha` This `la` That `ha` is `la` This `ha` This `ha` That `la` This `ha` That

instance ((ee `S` eee `S` e `S` eeee `M` e) ~ (ee `S` eee `S` eeee))
 => Matchable e (ee `S` eee `S` e `S` eeee) where
 on = This `ha` This `ha` This `la` This `ha` This `ha` That `la` That `ha` is `la` This `ha` That

{-
on' :: Excludable a entire => r `AR_` Unit `S` a
on' x = on x `yui` Unit

class Layable a r where
 lay :: a `AR_` r

instance Layable a a where
 lay = identity

instance Layable a aa => Layable a (Tagged l aa) where
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
