module Ya.Program.Interface.Matchable where

import Ya.Algebra
import Ya.Operators
import Ya.Program.Primitive

-- TODO: try generalize over categories
class Matchable goal entire where
 on :: entire `AR_` entire `M` goal `S` goal

instance Matchable e (e `S` ee) where
 on = That `ha` is `hs` This

instance ((ee `S` e `M` e) ~ (ee))
 => Matchable e (ee `S` e) where
 on = This `hs` That `ha` is

instance ((e `S` ee `S` eee `M` e) ~ (ee `S` eee))
 => Matchable e (e `S` ee `S` eee) where
 on = That `ha` is `hs` This `ha` This `hs` This `ha` That

instance ((ee `S` e `S` eee `M` e) ~ (ee `S` eee))
 => Matchable e (ee `S` e `S` eee) where
 on = This `ha` This `hs` That `ha` is `hs` This `ha` That

instance ((e `S` ee `S` eee `S` eeee `M` e) ~ (ee `S` eee `S` eeee))
 => Matchable e (e `S` ee `S` eee `S` eeee) where
 on = That `ha` is `hs` This `ha` This `ha` This `hs` This `ha` This `ha` That `hs` This `ha` That

instance ((ee `S` e `S` eee `S` eeee `M` e) ~ (ee `S` eee `S` eeee))
 => Matchable e (ee `S` e `S` eee `S` eeee) where
 on = This `ha` This `ha` This `hs` That `ha` is `hs` This `ha` This `ha` That `hs` This `ha` That

instance ((ee `S` eee `S` e `S` eeee `M` e) ~ (ee `S` eee `S` eeee))
 => Matchable e (ee `S` eee `S` e `S` eeee) where
 on = This `ha` This `ha` This `hs` This `ha` This `ha` That `hs` That `ha` is `hs` This `ha` That