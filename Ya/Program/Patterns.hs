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

type Boolean = U_I_II ML Unit Unit

pattern Boolean :: Unit `ML` Unit `AR_` Boolean
pattern Boolean e = U_I_II e

pattern False x = U_I_II (This x)

pattern True x = U_I_II (That x)

pattern Selfsame x = U_I_II (That x)

type Provided = U_I_II (->)

type Supplied = U_II_I LM

type Equipped = U_II_I LM

pattern Equip :: e `LM` ee -> Equipped ee e
pattern Equip x = U_II_I x

type Optional = U_I_II ML Unit

pattern None :: Unit -> Optional e
pattern None x = U_I_II (This x)

pattern Some :: e -> Optional e
pattern Some x = U_I_II (That x)

pattern Optionally x = U_I_II x

type Halts = U_I_II ML Unit

type Maybe = U_I_II ML Unit

pattern Maybe :: Unit `ML` e `AR_` Maybe e
pattern Maybe x = U_I_II @ML @Unit x

type Progress = U_I_II ML

pattern Progress x = U_I_II @ML x

pattern Interrupt :: e -> Progress e ee
pattern Interrupt x = U_I_II @ML (This x)

pattern Continue :: ee -> Progress e ee
pattern Continue x = U_I_II @ML (That x)

type Error = U_I_II ML

pattern Error :: e -> Error e ee
pattern Error x = U_I_II (This x)

type Catch = U_I_II ML

pattern Catch :: e -> Error e ee
pattern Catch x = U_I_II (This x)

type Reach = U_I_II ML

pattern Reach :: e -> Error e ee
pattern Reach x = U_I_II (This x)

pattern Wrong :: e -> Error e ee
pattern Wrong x = U_I_II (This x)

-- TODO: remove
pattern Close :: e -> Error e ee
pattern Close x = U_I_II (This x)

pattern Valid :: ee -> Error e ee
pattern Valid x = U_I_II (That x)

pattern Ok x = U_I_II (That x)

type Probably = U_I_II ML

pattern Probably x = U_I_II @ML x

type Perhaps = U_I_II ML

pattern Perhaps x = U_I_II @ML x

type Reference u i ii iii = i `AR_` u ii (iii `AR_` i)

type Attribute = U_I_UU_II_U_II_I (->) LM

pattern Attribute :: forall ee e . (e `AR_` LM ee (ee -> e)) -> Attribute e ee
pattern Attribute x = U_I_UU_II_U_II_I @(->) @LM x

type Scope = U_I_UU_II_U_II_I (->) LM

pattern Scope :: forall ee e . (e `AR_` LM ee (ee -> e)) -> Scope e ee
pattern Scope x = U_I_UU_II_U_II_I @(->) @LM x

-- type Directive = U_I_UU_I_II (->) ML

-- pattern Directive :: forall ee e . (e `AR_` ML e ee) -> Directive e ee
-- pattern Directive x = U_I_UU_I_II @(->) @ML x

type Match = U_I_UU_MN_I_II_II (->) ML

pattern Match :: forall ee e . (e `AR_` ML (MN e ee) ee) -> Match e ee
pattern Match x = U_I_UU_MN_I_II_II @(->) @ML x

type Automation e ee eee = e `AR_` ee `LM` eee

type Transition = U_I_UU_II_I (->) LM

pattern Transition x = U_I_UU_II_I @(->) @LM x

pattern Event x = U_I_UU_II_I @(->) @LM x

type State = U_I_II Transition

pattern State :: forall e o . Transition e o -> State e o
pattern State x = U_I_II @Transition x

type Construction = R_U_I_T_I LM

pattern Construct xs = R_U_I_T_I xs

pattern Root x xs = R_U_I_T_I (Recursive (U_I_T_II (These x xs)))

pattern Node x xs = Recursive (U_I_T_II (These x xs))

-- pattern Yet x xs = Recursive (U_I_T_II (These x xs))

type Instruction = R_U_I_T_I ML

pattern Instruct xs = R_U_I_T_I (Recursive (U_I_T_II (That xs)))

pattern Load x = R_U_I_T_I (Recursive (U_I_T_II (This x)))

type List = Optional `T'TT'I` Construction Optional

pattern List xs = T'TT'I @Optional @(Construction Optional) (Some (R_U_I_T_I xs))

pattern Item :: i -> t (Recursive (U_I_T_II t LM i)) -> Recursive (U_I_T_II t LM i)
pattern Item x xs = Recursive (U_I_T_II (These x xs))

pattern Next :: forall ee e . ee `AR_` Progress e ee
pattern Next x = U_I_II (That x)

pattern Last :: forall e ee . e `AR_` Progress e ee
pattern Last x = U_I_II (This x)

type family Brancher datastructure where
 Brancher (T'TT'I t (Construction t)) = t

type family Nonempty datastructure where
 Nonempty (T'TT'I Optional (Construction Optional)) = Construction Optional

pattern Nonempty :: forall t i . Recursive (U_I_T_II (Brancher t) LM i) -> Construction (Brancher t) i
pattern Nonempty xs = R_U_I_T_I xs

pattern Empty :: forall t e . (Brancher t ~ Optional)
 => Unit -> T'TT'I Optional (Construction Optional) e
pattern Empty x = T'TT'I (None x)

type Tree = Construction List

pattern Tree x xs = R_U_I_T_I (Recursive (U_I_T_II (These x (T'TT'I (Some (Construct xs))))))

type family Binary t where
 Binary Tree = Construction (U_I_I LM `T'TT'I` Optional)

pattern Binary xs = T'TT'I (U_I_I xs)

type family Forest tree where
 Forest (Construction t) = t `T'TT'I` Construction t

type Stream = Construction Only

pattern Stream :: Stream i -> Stream i
pattern Stream xs = xs

type Way = ML Unit Unit

pattern Back :: forall r e ee . (r ~ e `ML` ee) => e -> r
pattern Back x = This x

pattern Fore :: forall r ee e . (r ~ e `ML` ee) => ee -> r
pattern Fore x = That x

pattern Passed x = This x
pattern Future x = That x

type Decision = ML Unit Unit

pattern No x = This x
pattern Yes x = That x

type Side = ML Unit Unit

pattern Left x = This x
pattern Right x = That x

type Vertical = ML Unit Unit

type Predicate = U_II_I Arrow Boolean

pattern Predicate :: e `AR` Boolean `AR_` Predicate e
pattern Predicate e = U_II_I e
