module Ya.Program.Interface.Matchable where

import Ya.Algebra
import Ya.Operators
import Ya.Program.Primitive

-- TODO: try generalize over categories
class Matchable goal entire where
 on :: entire `AR_` entire `M` goal `S` goal

instance Matchable e (e `S` ee) where
 on = That `ha` is `has` This

instance ((ee `S` e `M` e) ~ (ee))
 => Matchable e (ee `S` e) where
 on = This `has` That `ha` is

instance ((e `S` ee `S` eee `M` e) ~ (ee `S` eee))
 => Matchable e (e `S` ee `S` eee) where
 on = That `ha` is `has` This `ha` This `has` This `ha` That

instance ((ee `S` e `S` eee `M` e) ~ (ee `S` eee))
 => Matchable e (ee `S` e `S` eee) where
 on = This `ha` This `has` That `ha` is `has` This `ha` That

instance ((e `S` ee `S` eee `S` eeee `M` e) ~ (ee `S` eee `S` eeee))
 => Matchable e (e `S` ee `S` eee `S` eeee) where
 on = That `ha` is `has` This `ha` This `ha` This `has` This `ha` This `ha` That `has` This `ha` That

instance ((ee `S` e `S` eee `S` eeee `M` e) ~ (ee `S` eee `S` eeee))
 => Matchable e (ee `S` e `S` eee `S` eeee) where
 on = This `ha` This `ha` This `has` That `ha` is `has` This `ha` This `ha` That `has` This `ha` That

instance ((ee `S` eee `S` e `S` eeee `M` e) ~ (ee `S` eee `S` eeee))
 => Matchable e (ee `S` eee `S` e `S` eeee) where
 on = This `ha` This `ha` This `has` This `ha` This `ha` That `has` That `ha` is `has` This `ha` That