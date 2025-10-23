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

instance
 ( Setoid (AR) k
 , Component (AR) (Alone `P'T'I'TT'I` (Shafted List)) (Construction Maybe)
 , Component (AR) (Shafted List) (Construction Maybe)
 ) => Keyable k (Construction Maybe `T'TT'I` Along k) where
 key k x =
  let prepared = unwrap x `yi` to @(Scrolling List) in
  let predicate = Match `hv_` _exact_key_ k `ha` unwrap @AR in
  let adjusted = prepared `yi` spot (That Unit `lu` predicate) `ho` this in
  case unwrap adjusted of
   This Unit ->
    Break k `lu` ((\_ -> x) `la` (\i -> push (Along (i `lu` k)) `hv` unwrap x `yi` that `ho` wrap @(AR)))
   That (T'TT'I'TTT'I (These (Alone (T'II'I (These xx kk))) xxx)) ->
    Valid xx `lu` ((\_ -> wrap @(AR) `ha` to @(Nonempty List) `hv` xxx) `la` (\i -> wrap @(AR) `ha` to @(Nonempty List) `hv` T'TT'I'TTT'I (These (Alone (T'II'I (These i kk))) xxx)))

instance
 ( Setoid (AR) k
 , Component (AR) (Alone `P'T'I'TT'I` Shafted List) (Nonempty List)
 , Component (AR) (Nonempty List) List
 , Component (AR) (Shafted List) List
 ) => Keyable k (List `T'TT'I` Along k) where
 key k = on_empty_list `la` on_nonempty_list where

  on_empty_list _ = Break k `lu` (Error `hu` T'TT'I empty `la` (`lu` k) `ho` Along `ho` intro @List @(AR) `ho` T'TT'I)

  on_nonempty_list x =
   let prepared = x `yi` to @(Scrolling List) @(Nonempty List) in
   let predicate = Match `hv_` _exact_key_ k `ha` unwrap @AR in
   let adjusted = prepared `yi` spot (That Unit `lu` predicate) `ho` this in
   case unwrap adjusted of
    This Unit -> Break k `lu_` (Error `hu_` T'TT'I `ha` to @List `hv` x `la` (\i -> push (Along (i `lu` k)) `hv` x `yi` that `ho` to @List `ho` T'TT'I))
    That (T'TT'I'TTT'I (These (Alone (T'II'I (These xx kk))) xxx)) ->
     Valid xx `lu` (Error `hu_` T'TT'I `ha` to @List `hv` xxx `la` (\i -> T'TT'I `ha` to @List `ha` to @(Nonempty List) `hv` T'TT'I'TTT'I (These (Alone (T'II'I (These i kk))) xxx)))

_exact_key_ k (T'II'I (These _ kk)) =
 Wrong `hu` by False `la` Valid `hu` by True `li_` (k `lu'q` kk)

-- TODO: I think it should work. Here I'm going to use an instance above and then _locate_ (Down Unit `P` ) with Scrolling Tree
-- instance Keyable (Construction Maybe k) (Construction Maybe `T'TT'I` Construction List `T'TT'I` Along k) where
--  key ks x = ks `yokl` Forth `ha` Apply `ha` go_horizontally where

--   predicate k = Match `hv_` _exact_key_ k `ha` this `ha` top @Tree

--   go_horizontally k = intro @(State `T` Scrolling Tree) -- Stops `T`  `JNT` 
--    `yuk_____` Apply `ha` State `ha` Event `ha` spot (That Unit `lu` predicate k)
--    `ha__'he'he` Scope `hv` it @(List (Along k (Construction (List `T'TT'I` Along k))))
--         -- `ho_` Scope `hv` as @()

-- (`kyok`): Instruction t a `AR__` (t `T'TT'I` Instruction t a `AR___` t `T'TT'I` Instruction t a) `AR__` Instruction t o

-- `C'AR__` Construction
-- Shifting t List `T'TT'I` Tree `P'T'I'TT'I` Chassis List t Tree
-- Scrolling Tree 

 -- key (Root k ks) = unwrap @(AR)
 --  `hv__` unwrap @(AT) @((List `T'TT'I` Along k) `T'TT'I` Construction (List `T'TT'I` Along k) `T'I_` _)
 --   `ho_` Scope `ha` key @k @(List `T'TT'I` Along k) `hv` k

  -- `ho_` unwrap @(AT) @((List `T'TT'I` Along k) (Construction (List `T'TT'I` Along k) _))
  -- `ho_` unwrap @(AT) @(List (Along k (Construction (List `T'TT'I` Along k) _)))

-- Construction Maybe k 

-- Scope _ k

-- Scope _ (Construction Maybe k)

-- Scope (t i) (Stops k i)

-- Scope (t (tt i)) (Stops (Construction Maybe k) i)

  -- Scope `hv` as @(Shifting Alone List `T'TT'I` Tree) @(Scrolling Tree) `ho` 

-- source a (tt o) `AR___` target (t a) (tt ( t o))

