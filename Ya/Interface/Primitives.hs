module Ya.Interface.Primitives where

import Ya.Semantics.Structures

type Alone = I

type Other = T'I'

type Arrow = (AR)

type Given = T'I'II (AR)

type Taken = T'II'I (AR)

type Attribute = T'I'TT'II'T'II'I (AR) P

type Scope = T'I'TT'II'T'II'I (AR) P

type Reach = T'I'II Scope

type Budge = T'II'I Scope

type Boolean = T'I'II (S) Unit Unit

type Added = T'II'I P

type Halts = T'I'II (S) Unit

type Maybe = T'I'II (S) Unit

type Stops = T'I'II (S)

type Twice = T'I'I (P)

type Opted = T'I'I (S)

type Origination = F'T'I'TT

type Instruction = Origination Stops

type Construction = Origination Added

type family Nonempty t where
 Nonempty (Maybe `T'TT'I` Construction Maybe) = Construction Maybe
 Nonempty (List `T'TT'I` Construction t) = Construction Maybe `T'TT'I` Construction t

type List = Maybe `T'TT'I` Construction Maybe

type Tree = Construction List

type Match = T'II'I Arrow Boolean
