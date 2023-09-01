module Ya.Algebra.Operators where

import Ya.Algebra.Definition

infixl 9 `i`
infixl 8 `ii`
infixl 7 `iii`

iii, ii, i :: Category into => into t t
iii = identity
ii = identity
i = identity