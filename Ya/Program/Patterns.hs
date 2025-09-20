{-# LANGUAGE AllowAmbiguousTypes #-}
module Ya.Program.Patterns where

import Ya.Algebra

type Same = I

pattern Same e = Identity e

type Once = I

pattern Once :: e -> Once e
pattern Once e = Identity e

type Alone = I

pattern Alone :: e -> Alone e
pattern Alone e = Identity e

type Singular = I

pattern Singular :: e -> Singular e
pattern Singular e = Identity e

-- type Focused = I

-- pattern Focused :: e -> Focused e
-- pattern Focused e = Identity e

type Apparently = I

pattern Apparently :: e -> Apparently e
pattern Apparently e = Identity e

type Boolean = S'I'II Unit Unit

pattern Boolean :: Unit `S` Unit `AR_` Boolean
pattern Boolean e = T'I'II e

pattern False x = T'I'II (This x) :: Boolean
pattern True x = T'I'II (That x) :: Boolean

pattern Selfsame x = T'I'II (That x)

type Given = T'I'II (AR)

pattern Given :: e `AR` e `AR__` Given e e
pattern Given e = T'I'II e

type Supplied = T'II'I P

type Equipped = T'II'I P

pattern Equip :: forall e ee . e `P` ee -> Equipped ee e
pattern Equip x = T'II'I x

type Optional = S'I'II Unit

pattern Empty :: Unit -> Maybe i
pattern Empty x = T'I'II (This x)

pattern Exist :: i -> Maybe i
pattern Exist x = T'I'II (That x)

pattern Optionally x = T'I'II x

type Halts = S'I'II Unit

type Maybe = S'I'II Unit

pattern Maybe :: Unit `S` e `AR_` Maybe e
pattern Maybe x = T'I'II @(S) @Unit x

type Progress = T'I'II (S)

pattern Progress x = T'I'II @(S) x

pattern Interrupt :: e -> Progress e ee
pattern Interrupt x = T'I'II @(S) (This x)

pattern Continue :: ee -> Progress e ee
pattern Continue x = T'I'II @(S) (That x)

pattern Erase :: e -> Progress e ee
pattern Erase x = T'I'II (This x)

pattern Store :: ee -> Progress e ee
pattern Store x = T'I'II (That x)

pattern Allot :: ee -> Progress e ee
pattern Allot x = T'I'II (That x)

type Stops = T'I'II (S)

type Error = T'I'II (S)

pattern Error :: e -> Error e ee
pattern Error x = T'I'II (This x)

pattern Break :: e -> Error e ee
pattern Break x = T'I'II (This x)

type Catch = T'I'II (S)

pattern Catch :: e -> Error e ee
pattern Catch x = T'I'II (This x)

type Reach = T'I'II (S)

pattern Reach :: e -> Error e ee
pattern Reach x = T'I'II (This x)

type Until = T'I'II (S)

pattern Wrong :: e -> Error e ee
pattern Wrong x = T'I'II (This x)

-- TODO: remove
pattern Close :: e -> Error e ee
pattern Close x = T'I'II (This x)

pattern Valid :: ee -> Error e ee
pattern Valid x = T'I'II (That x)

pattern Ok :: ee -> Error e ee
pattern Ok x = T'I'II (That x)

type Probably = T'I'II (S)

pattern Probably x = T'I'II @(S) x

type Perhaps = T'I'II (S)

pattern Perhaps x = T'I'II @(S) x

type Reference u i ii iii = i `AR_` u ii (iii `AR_` i)

type Attribute = T'I'TT'II'T'II'I (AR) P

pattern Attribute :: forall ee e . (e `AR_` (P) ee (ee -> e)) -> Attribute e ee
pattern Attribute x = T'I'TT'II'T'II'I @(AR) @(P) x

type Scope = T'I'TT'II'T'II'I (AR) P

pattern Scope :: forall ee e . (e `AR_` (P) ee (ee -> e)) -> Scope e ee
pattern Scope x = T'I'TT'II'T'II'I @(AR) @(P) x

-- type Directive = U_I_UT'I'II (AR) (S)

-- pattern Directive :: forall ee e . (e `AR_` (S) e ee) -> Directive e ee
-- pattern Directive x = U_I_UT'I'II @(AR) @(S) x

type Match = U_I_UU_M_I_II_II (AR) (S)

pattern Match :: forall ee e . (e `AR_` (S) (M e ee) ee) -> Match e ee
pattern Match x = U_I_UU_M_I_II_II @(AR) @(S) x

type Automation e ee eee = e `AR_` ee `P` eee

type Transition = T'I'TT'II'I (AR) (P)

pattern Transition :: Automation e ee e `AR__` Transition e ee
pattern Transition x = T'I'TT'II'I @(AR) @(P) x

type Event = T'I'TT'II'I (AR) P

pattern Event :: Automation e ee e `AR__` Event e ee
pattern Event x = T'I'TT'II'I @(AR) @(P) x

type State = T'I'II Transition

pattern State :: forall e o . Transition e o -> State e o
pattern State x = T'I'II @Transition x

type Branching t tt i = T'I'II t i `T'TT'I` tt

type Construction = R_U_I_T_I P

pattern Construct xs = R_U_I_T_I xs

pattern Root x xs = R_U_I_T_I (Recursive (T'TT'I (T'I'II (These x xs))))

pattern Node x xs = Recursive (T'TT'I (T'I'II (These x xs)))

-- pattern Yet x xs = Recursive (T'I'TT'II (These x xs))

type Instruction = R_U_I_T_I (S)

-- x `kyokl` Level `ha` ...

-- TODO: t `C'AR___` Instruction t

-- pattern Value x = R_U_I_T_I (Recursive (T'I'TT'II (This x)))
-- pattern Impel x = R_U_I_T_I (Recursive (T'I'TT'II (That x)))

pattern Impel :: t (Recursive (T'I'II (S) i `T'TT'I` t)) `AR____` Instruction t i
pattern Impel xs = R_U_I_T_I (Recursive (T'TT'I (T'I'II (That xs))))

pattern Value :: i `AR____` Instruction t i
pattern Value x = R_U_I_T_I (Recursive (T'TT'I (T'I'II (This x))))

type List = Optional `T'TT'I` Construction Optional

pattern List xs = T'TT'I @Optional @(Construction Optional) (Exist (R_U_I_T_I xs))

type Quest = List

pattern Item :: i -> t (Recursive (T'I'II (P) i `T'TT'I` t)) -> Recursive (T'I'II (P) i `T'TT'I` t)
pattern Item x xs = Recursive (T'TT'I (T'I'II (These x xs)))

pattern Next :: forall ee e . ee `AR_` Progress e ee
pattern Next x = T'I'II (That x)

pattern Last :: forall e ee . e `AR_` Progress e ee
pattern Last x = T'I'II (This x)

type family Brancher datastructure where
 Brancher (T'TT'I t (Construction t)) = t

type family Nonempty datastructure where
 Nonempty (T'TT'I Optional (Construction Optional)) = Construction Optional

pattern Nonempty :: forall t i . Recursive (T'I'II (P) i `T'TT'I` Brancher t) -> Construction (Brancher t) i
pattern Nonempty xs = R_U_I_T_I xs

type Tree = Construction List

pattern Tree x xs = R_U_I_T_I (Recursive (T'TT'I (T'I'II (These x (T'TT'I (Exist (Construct xs)))))))

type family Binary t where
 Binary Tree = Construction (T'I'I (P) `T'TT'I` Optional)

pattern Binary xs = T'TT'I (T'I'I xs)

type family Forest tree where
 Forest (Construction t) = t `T'TT'I` Construction t

type Stream = Construction Alone

pattern Stream :: Stream i -> Stream i
pattern Stream xs = xs

type Way = Unit `S` Unit

pattern Back :: forall r e ee . (r ~ e `S` ee) => e -> r
pattern Back x = This x

pattern Fore :: forall r ee e . (r ~ e `S` ee) => ee -> r
pattern Fore x = That x

pattern Passed x = This x
pattern Future x = That x

type Decision = (S) Unit Unit

pattern No x = This x
pattern Yes x = That x

type Side = (S) Unit Unit

pattern Left x = This x
pattern Right x = That x

type Vertical = (S) Unit Unit

type Predicate = T'II'I Arrow Boolean

pattern Predicate :: e `AR` Boolean `AR_` Predicate e
pattern Predicate e = T'II'I e

pattern Junction :: t e `P` tt e `AR__` (t `P'T'I'TT'I` tt) e
pattern Junction x = T'TT'I'TTT'I  x
