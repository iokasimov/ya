module Ya.Interface.Primitives where

import Ya.Semantics.Structures

type Alone = I

pattern Alone :: forall i . i -> Alone i
pattern Alone x = Identity x

type Flout = T'I'

type Given = T'I'II (AR)

pattern Given :: e `AR` ee `AR_` Given e ee
pattern Given x = T'I'II x

type Taken = T'II'I (AR)

pattern Taken :: ee `AR` e `AR_` Taken e ee
pattern Taken x = T'II'I x

type Boolean = T'I'II (S) Unit Unit

pattern Boolean :: Unit `S` Unit `AR` Boolean
pattern Boolean e = T'I'II e

pattern False x = T'I'II (This x) :: Boolean
pattern True x = T'I'II (That x) :: Boolean

type Added = T'II'I P

pattern Added :: forall e ee . e `P` ee `AR` Added ee e
pattern Added x = T'II'I x

type Halts = T'I'II (S) Unit

type Maybe = T'I'II (S) Unit

type Stops = T'I'II (S)

{-
pattern Stops x = T'I'II @(S) x

pattern Error :: i -> Stops i ii
pattern Error x = T'I'II (This x)

pattern Break :: i -> Stops i ii
pattern Break x = T'I'II (This x)
-}

type Twice = T'I'I (P)

type Opted = T'I'I (S)

type Origination = F'T'I'TT

type Instruction = Origination Stops

type Construction = Origination Added

type family Nonempty t where
 Nonempty (Maybe `T'TT'I` Construction Maybe) = Construction Maybe
 Nonempty (List `T'TT'I` Construction t) = Construction Maybe `T'TT'I` Construction t

type List = Maybe `T'TT'I` Construction Maybe
