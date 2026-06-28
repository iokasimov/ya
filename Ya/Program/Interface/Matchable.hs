module Ya.Program.Interface.Matchable where

import Ya.Algebra
import Ya.Operators
import Ya.Program.Primitive

-- TODO: try generalize over categories
class Matchable goal entire where
 option :: entire `AR_` entire `M` goal `S` goal

instance Matchable e (e `S` ee) where
 option = That `ha` itself `has` This

instance ((ee `S` e `M` e) ~ (ee))
 => Matchable e (ee `S` e) where
 option = This `has` That `ha` itself

instance ((e `S` ee `S` eee `M` e) ~ (ee `S` eee))
 => Matchable e (e `S` ee `S` eee) where
 option = That `ha` itself `has` This `ha` This `has` This `ha` That

instance ((ee `S` e `S` eee `M` e) ~ (ee `S` eee))
 => Matchable e (ee `S` e `S` eee) where
 option = This `ha` This `has` That `ha` itself `has` This `ha` That

instance ((e `S` ee `S` eee `S` eeee `M` e) ~ (ee `S` eee `S` eeee))
 => Matchable e (e `S` ee `S` eee `S` eeee) where
 option = That `ha` itself `has` This `ha` This `ha` This `has` This `ha` This `ha` That `has` This `ha` That

instance ((ee `S` e `S` eee `S` eeee `M` e) ~ (ee `S` eee `S` eeee))
 => Matchable e (ee `S` e `S` eee `S` eeee) where
 option = This `ha` This `ha` This `has` That `ha` itself `has` This `ha` This `ha` That `has` This `ha` That

instance ((ee `S` eee `S` e `S` eeee `M` e) ~ (ee `S` eee `S` eeee))
 => Matchable e (ee `S` eee `S` e `S` eeee) where
 option = This `ha` This `ha` This `has` This `ha` This `ha` That `has` That `ha` itself `has` This `ha` That
