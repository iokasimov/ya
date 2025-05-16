{-# LANGUAGE AllowAmbiguousTypes #-}
module Ya.Program.Patterns where

import Ya.Algebra

type Same = I

pattern Same e = Identity e

type Once = I

pattern Once :: e -> Once e
pattern Once e = Identity e

type Only = I

pattern Only :: e -> Only e
pattern Only e = Identity e

type Singular = I

pattern Singular :: e -> Singular e
pattern Singular e = Identity e

type Focused = I

pattern Focused :: e -> Focused e
pattern Focused e = Identity e

type Apparently = I

pattern Apparently :: e -> Apparently e
pattern Apparently e = Identity e

type Boolean = T'I'II (S) Unit Unit

pattern Boolean :: Unit `S` Unit `AR_` Boolean
pattern Boolean e = T'I'II e

pattern False x = T'I'II (This x)

pattern True x = T'I'II (That x)

pattern Selfsame x = T'I'II (That x)

type Provided = T'I'II (AR)

type Supplied = T'II'I P

type Equipped = T'II'I P

pattern Equip :: e `P` ee -> Equipped ee e
pattern Equip x = T'II'I x

type Optional = T'I'II (S) Unit

pattern None :: Unit -> Optional e
pattern None x = T'I'II (This x)

pattern Some :: ee -> T'I'II (S) e ee
pattern Some x = T'I'II (That x)

pattern Optionally x = T'I'II x

type Halts = T'I'II (S) Unit

type Maybe = T'I'II (S) Unit

pattern Maybe :: Unit `S` e `AR_` Maybe e
pattern Maybe x = T'I'II @(S) @Unit x

type Progress = T'I'II (S)

pattern Progress x = T'I'II @(S) x

pattern Interrupt :: e -> Progress e ee
pattern Interrupt x = T'I'II @(S) (This x)

pattern Continue :: ee -> Progress e ee
pattern Continue x = T'I'II @(S) (That x)

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

pattern Ok x = T'I'II (That x)

type Probably = T'I'II (S)

pattern Probably x = T'I'II @(S) x

type Perhaps = T'I'II (S)

pattern Perhaps x = T'I'II @(S) x

type Reference u i ii iii = i `AR_` u ii (iii `AR_` i)

type Attribute = U_I_UU_II_T'II'I (AR) P

pattern Attribute :: forall ee e . (e `AR_` (P) ee (ee -> e)) -> Attribute e ee
pattern Attribute x = U_I_UU_II_T'II'I @(AR) @(P) x

type Scope = U_I_UU_II_T'II'I (AR) P

pattern Scope :: forall ee e . (e `AR_` (P) ee (ee -> e)) -> Scope e ee
pattern Scope x = U_I_UU_II_T'II'I @(AR) @(P) x

-- type Directive = U_I_UT'I'II (AR) (S)

-- pattern Directive :: forall ee e . (e `AR_` (S) e ee) -> Directive e ee
-- pattern Directive x = U_I_UT'I'II @(AR) @(S) x

type Match = U_I_UU_M_I_II_II (AR) (S)

pattern Match :: forall ee e . (e `AR_` (S) (M e ee) ee) -> Match e ee
pattern Match x = U_I_UU_M_I_II_II @(AR) @(S) x

type Automation e ee eee = e `AR_` ee `P` eee

type Transition = U_I_UT'II'I (AR) P

pattern Transition :: Automation e ee e `AR__` Transition e ee
pattern Transition x = U_I_UT'II'I @(AR) @(P) x

type Event = U_I_UT'II'I (AR) P

pattern Event :: Automation e ee e `AR__` Event e ee
pattern Event x = U_I_UT'II'I @(AR) @(P) x

type State = T'I'II Transition

pattern State :: forall e o . Transition e o -> State e o
pattern State x = T'I'II @Transition x

type Construction = R_U_I_T_I P

pattern Construct xs = R_U_I_T_I xs

pattern Root x xs = R_U_I_T_I (Recursive (U_I_T_II (These x xs)))

pattern Node x xs = Recursive (U_I_T_II (These x xs))

-- pattern Yet x xs = Recursive (U_I_T_II (These x xs))

type Instruction = R_U_I_T_I (S)

pattern Instruct xs = R_U_I_T_I (Recursive (U_I_T_II (That xs)))

pattern Load x = R_U_I_T_I (Recursive (U_I_T_II (This x)))

type List = Optional `T'TT'I` Construction Optional

pattern List xs = T'TT'I @Optional @(Construction Optional) (Some (R_U_I_T_I xs))

pattern Item :: i -> t (Recursive (U_I_T_II t (P) i)) -> Recursive (U_I_T_II t (P) i)
pattern Item x xs = Recursive (U_I_T_II (These x xs))

pattern Next :: forall ee e . ee `AR_` Progress e ee
pattern Next x = T'I'II (That x)

pattern Last :: forall e ee . e `AR_` Progress e ee
pattern Last x = T'I'II (This x)

type family Brancher datastructure where
 Brancher (T'TT'I t (Construction t)) = t

type family Nonempty datastructure where
 Nonempty (T'TT'I Optional (Construction Optional)) = Construction Optional

pattern Nonempty :: forall t i . Recursive (U_I_T_II (Brancher t) (P) i) -> Construction (Brancher t) i
pattern Nonempty xs = R_U_I_T_I xs

pattern Empty :: forall t e . (Brancher t ~ Optional)
 => Unit -> T'TT'I Optional (Construction Optional) e
pattern Empty x = T'TT'I (None x)

type Tree = Construction List

pattern Tree x xs = R_U_I_T_I (Recursive (U_I_T_II (These x (T'TT'I (Some (Construct xs))))))

type family Binary t where
 Binary Tree = Construction (U_I_I (P) `T'TT'I` Optional)

pattern Binary xs = T'TT'I (U_I_I xs)

type family Forest tree where
 Forest (Construction t) = t `T'TT'I` Construction t

type Stream = Construction Only

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
pattern Junction x = U_T_I_TT_I  x