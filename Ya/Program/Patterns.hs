{-# LANGUAGE AllowAmbiguousTypes #-}
module Ya.Program.Patterns where

import Ya.Algebra

type Same = I

pattern Same e = Identity e

type Once = I

pattern Once e = Identity e

type Only = I

pattern Only e = Identity e

type Singular = I

pattern Singular e = Identity e

type Focused = I

pattern Focused e = Identity e

type Apparently = I

pattern Apparently e = Identity e

type Boolean = Straight ML () ()

pattern Boolean e = U_I_II e

pattern False x = U_I_II (This x)

pattern True x = U_I_II (That x)

pattern Selfsame x = U_I_II (That x)

type Provided = U_I_II (->)

type Supplied = U_II_I LM

type Optional = U_I_II ML ()

pattern None x = U_I_II (This x)

pattern Some x = U_I_II (That x)

pattern Optionally x = U_I_II x

type Halts = U_I_II ML ()

type Maybe = U_I_II ML ()

pattern Maybe x = U_I_II @ML @() x

type Haltable t = JNT t Halts

type Progress = U_I_II ML

pattern Progress x = U_I_II @ML x

pattern Interrupt x = U_I_II @ML (This x)

pattern Continue x = U_I_II @ML (That x)

type Error = U_I_II ML

pattern Error x = U_I_II (This x)

pattern Wrong x = U_I_II (This x)

pattern Close x = U_I_II (This x)

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

type Directive = U_I_UU_II_U_II_I (->) ML

pattern Directive :: forall ee e . (e `AR_` ML ee (ee -> e)) -> Directive e ee
pattern Directive x = U_I_UU_II_U_II_I @(->) @ML x

type Automation e ee eee = e `AR_` ee `LM` eee

type Transition = U_I_UU_II_I (->) LM

pattern Transition x = U_I_UU_II_I @(->) @LM x

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

pattern List xs = T'TT'I @Optional @(Construction Optional) xs

pattern Next x xs = Recursive (U_I_T_II (These x (Some xs)))

pattern Last x = Recursive (U_I_T_II (These x (None ())))

type family Brancher datastructure where
 Brancher (T'TT'I t (Construction t)) = t

type family Nonempty datastructure where
 Nonempty (T'TT'I Optional (Construction Optional)) = Construction Optional

pattern Nonempty :: forall t i . Construction (Brancher t) i -> Construction (Brancher t) i
pattern Nonempty xs = xs

pattern Empty :: forall t e . (Brancher t ~ Optional)
 => () -> T'TT'I Optional (Construction Optional) e
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

type Way = ML () ()

pattern Back :: forall r e ee . (r ~ e `ML` ee) => e -> r
pattern Back x = This x

pattern Fore :: forall r ee e . (r ~ e `ML` ee) => ee -> r
pattern Fore x = That x

pattern Passed x = This x
pattern Future x = That x

type Decision = ML () ()

pattern No x = This x
pattern Yes x = That x

type Side = ML () ()

pattern Left x = This x
pattern Right x = That x

type Vertical = ML () ()

type Cascading = Labeled (Straight LM () ())

pattern Cascading :: t e -> Cascading t e
pattern Cascading e = T_'_I e

type Repeating = Labeled (U_I_I LM ())

pattern Again :: t e -> Repeating t e
pattern Again e = T_'_I e

type Trying = Labeled (U_I_II ML () ())

pattern Try :: t e -> Trying t e
pattern Try e = T_'_I e

type Checking = Trying

pattern Check :: t e -> Trying t e
pattern Check e = Try e

type Retrying = Labeled (U_II_I ML () ())

pattern Retry :: t e -> Retrying t e
pattern Retry e = T_'_I e

type Fore = U_I_II ML () ()

type Back = U_II_I ML () ()

type Forward = T_'_I Fore

pattern Forward :: t e -> Forward t e
pattern Forward e = T_'_I e

type Reverse = T_'_I Back

pattern Reverse :: t e -> Reverse t e
pattern Reverse e = T_'_I e

pattern Forth :: t e -> Forward t e
pattern Forth e = T_'_I e

pattern Prior :: t e -> Reverse t e
pattern Prior e = T_'_I e

pattern Old :: t e -> Labeled (U_II_I ML () ()) t e
pattern Old e = T_'_I e

pattern New :: t e -> Labeled (U_I_II ML () ()) t e
pattern New e = T_'_I e

pattern Use :: t e -> Labeled (U_I_II ML () ()) t e
pattern Use e = T_'_I e
