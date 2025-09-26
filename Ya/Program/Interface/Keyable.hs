{-# LANGUAGE UndecidableInstances #-}
module Ya.Program.Interface.Keyable where

import Ya.Algebra
import Ya.Operators
import Ya.Program.Labels
import Ya.Program.Patterns
import Ya.Program.Primitive

import Ya.Program.Interface.Fieldable
import Ya.Program.Interface.Stackable
import Ya.Program.Interface.Shiftable

class Keyable k t where
 key :: k `AR_` Supertype (t i `AT` Stops k i)

-- instance Keyable k ((Alone `P'T'I'TT'I` Shafted List) `T'TT'I` Along k) where

-- TODO: test this instance using new literal
instance
 ( Setoid (AR) k
 , Component (AR) (Alone `P'T'I'TT'I` (Reverse List `P'T'I'TT'I` Forward List)) (Construction Maybe)
 , Component (AR) (Reverse List `P'T'I'TT'I` Forward List) (Construction Maybe)
 ) => Keyable k (Construction Maybe `T'TT'I` Along k) where
 key k x =
  let prepared = unwrap x `yi` to @(Scrolling List) in
  let adjusted = prepared `yi` locate (That Unit `lu` Predicate `hv` _exact_key_ k) `ho` this in
  case unwrap adjusted of
   This Unit ->s
    Break k `lu` ((\_ -> x) `la` (\i -> push (Along (i `lu` k)) `hv` unwrap x `yi` that `ho` wrap @(AR)))
   That (T'TT'I'TTT'I (These (Alone (T'II'I (These xx kk))) xxx)) ->
    Valid xx `lu` ((\_ -> wrap @(AR) `ha` to @(Nonempty List) `hv` xxx) `la` (\i -> wrap @(AR) `ha` to @(Nonempty List) `hv` T'TT'I'TTT'I (These (Alone (T'II'I (These i kk))) xxx)))

-- TODO: I think it should work. Here I'm going to use an instance above and then _locate_ (Down Unit `P` ) with Scrolling Tree
-- instance Keyable (Construction Maybe k) ((List `T'TT'I` Along k) `T'TT'I_` Construction (List `T'TT'I` Along k)) where
--  key k x = k `yokl` Forth `ha` 

_exact_key_ k (Alone (T'II'I (These _ kk))) =
 Wrong `hu` by False `la` Valid `hu` by True `li_` (k `lu'q` kk)
