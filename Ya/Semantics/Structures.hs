{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE UndecidableInstances #-}
module Ya.Semantics.Structures where

infixl 9 `T`, `L`, `P`, `S`, `M`
infixl 8 `T_`, `T'I`, `I'T`, `T'TT`, `TT'T`, `P_`, `S_`, `M_`
infixl 7 `T__`, `T'I_`, `I'T_`, `T'TT_`, `TT'T_`, `T'TT'I`, `TT'T'I`, `P__`, `S__`, `M__`
infixl 6 `T___`, `T'I__`, `I'T__`, `T'TT__`, `TT'T__`, `T'TT'I_`, `TT'T'I_`, `S___`
infixl 5 `T____`, `T'I___`, `I'T___`, `T'TT___`, `TT'T___`, `T'TT'I__`, `TT'T'I__`, `P'T'I'TT'I`, `S'T'I'TT'I`
infixl 4 `T_____`, `T'TT____`, `TT'T____`, `T'TT'I___`, `TT'T'I___`
infixl 3 `T______`, `T'TT_____`, `TT'T_____`, `T'TT'I____`, `TT'T'I____`
infixl 2 `T_______`, `T'TT______`, `TT'T______`, `T'TT'I_____`, `TT'T'I_____`
infixl 1 `T________`, `T'TT_______`, `TT'T_______`

infixl 8 `AR`, `AT`, `TR`, `AS`, `C'AR`, `C'AT`, `C'TR`
infixl 7 `AR_`, `AT_`, `TR_`, `AS_`, `C'AR_`, `C'AT_`, `C'TR_`
infixl 6 `AR__`, `AT__`, `TR__`, `AS__`, `C'AR__`, `C'AT__`, `C'TR__`
infixl 5 `AR___`, `AT___`, `TR___`, `AS___`, `C'AR___`, `C'AT___`,`C'TR___`
infixl 4 `AR____`, `AT____`, `TR____`, `AS____`, `C'AR____`, `C'AT____`,`C'TR____`
infixl 3 `AR_____`, `AT_____`, `TR_____`, `AS_____`, `C'AR_____`, `C'AT_____`,`C'TR_____`
infixl 2 `AR______`, `AT______`, `TR______`, `AS______`, `C'AR______`, `C'AT______`, `C'TR______`
infixl 1 `AR_______`, `AT_______`, `TR_______`, `AS_______`, `C'AR_______`, `C'AT_______`,`C'TR_______`

type family Supertype i

class Relation direction morphism i where
 relate :: direction morphism i (Supertype i)

type Subtyping = Relation T'II'I
type Supertyping = Relation T'I'II

class (Subtyping target i, Supertyping target i) => Wrapper target i where
deriving instance (Subtyping target i, Supertyping target i) => Wrapper target i

instance Wrapper (AR) i => Relation T'I'II (AT) i where
 relate = T'I'II (T'I'TT'II'T'II'I (\i -> These (supertype i) subtype))

instance Wrapper (AR) i => Relation T'II'I (AT) i where
 relate = T'II'I (T'I'TT'II'T'II'I (\i -> These (subtype i) supertype))

supertype :: forall target i .
 Supertyping target i =>
 target i (Supertype i)
supertype = let T'I'II x = relate in x

subtype :: forall target i .
 Subtyping target i =>
 target (Supertype i) i
subtype = let T'II'I x = relate in x

type T t = t
type T_ t = t
type T__ t = t
type T___ t = t
type T____ t = t
type T_____ t = t
type T______ t = t
type T_______ t = t
type T________ t = t

type T'I t = t
type T'I_ t = t
type T'I__ t = t
type T'I___ t = t

type I'T i t = t i
type I'T_ i t = t i
type I'T__ i t = t i
type I'T___ i t = t i

type T'TT t tt i = t (tt i)
type T'TT_ t tt i = t (tt i)
type T'TT__ t tt i = t (tt i)
type T'TT___ t tt i = t (tt i)
type T'TT____ t tt i = t (tt i)
type T'TT_____ t tt i = t (tt i)
type T'TT______ t tt i = t (tt i)
type T'TT_______ t tt i = t (tt i)

type TT'T t tt i = tt (t i)
type TT'T_ t tt i = tt (t i)
type TT'T__ t tt i = tt (t i)
type TT'T___ t tt i = tt (t i)
type TT'T____ t tt i = tt (t i)
type TT'T_____ t tt i = tt (t i)
type TT'T______ t tt i = tt (t i)
type TT'T_______ t tt i = tt (t i)

newtype I i = Identity i

type instance Supertype (I i) = i

instance Relation T'I'II (->) (I i)
 where relate = T'I'II (\(Identity x) -> x)

instance Relation T'II'I (->) (I i)
 where relate = T'II'I Identity

newtype T'TT'I t tt i = T'TT'I (t (tt i))

type T'TT'I_ = T'TT'I
type T'TT'I__ = T'TT'I
type T'TT'I___ = T'TT'I
type T'TT'I____ = T'TT'I
type T'TT'I_____ = T'TT'I

type instance Supertype (t `T'TT'I` tt `T'I_` i) = t (tt i)

instance Relation T'I'II (->) (T'TT'I f g i)
 where relate = T'I'II (\(T'TT'I x) -> x)

instance Relation T'II'I (->) (T'TT'I f g i)
 where relate = T'II'I T'TT'I

newtype TT'T'I t tt i = TT'T'I (tt (t i))

type TT'T'I_ = TT'T'I
type TT'T'I__ = TT'T'I
type TT'T'I___ = TT'T'I
type TT'T'I____ = TT'T'I
type TT'T'I_____ = TT'T'I

type instance Supertype (TT'T'I t tt i) = tt (t i)

instance Relation T'I'II (->) (TT'T'I f g i)
 where relate = T'I'II (\(TT'T'I x) -> x)

instance Relation T'II'I (->) (TT'T'I f g i)
 where relate = T'II'I TT'T'I

newtype T'I'I t i = T'I'I (t i i)

type instance Supertype (T'I'I t i) = t i i

instance Relation T'I'II (->) (T'I'I t i)
 where relate = T'I'II (\(T'I'I x) -> x)

instance Relation T'II'I (->) (T'I'I t i)
 where relate = T'II'I T'I'I

newtype T'I'II t i ii = T'I'II (t i ii)

type instance Supertype (T'I'II t i ii) = t i ii

instance Relation T'I'II (->) (T'I'II t i ii)
 where relate = T'I'II (\(T'I'II x) -> x)

instance Relation T'II'I (->) (T'I'II t i ii)
 where relate = T'II'I T'I'II

newtype T'II'I t i ii = T'II'I (t ii i)

type instance Supertype (T'II'I t ii i) = t i ii

instance Relation T'I'II (->) (T'II'I t i ii)
 where relate = T'I'II (\(T'II'I x) -> x)

instance Relation T'II'I (->) (T'II'I t i ii)
 where relate = T'II'I T'II'I

newtype T'I' i ii = T'I' i

type instance Supertype (T'I' i ii) = i

instance Relation T'II'I (->) (T'I' i ii)
 where relate = T'II'I T'I'

instance Relation T'I'II (->) (T'I' i ii)
 where relate = T'I'II (\(T'I' x) -> x)

newtype T'TT'I'II'I t tt i ii = T'TT'I'II'I (t (tt i ii) i)

type instance Supertype (T'TT'I'II'I t tt i ii) = t (tt i ii) i

instance Relation T'II'I (->) (T'TT'I'II'I t tt i ii)
 where relate = T'II'I T'TT'I'II'I

instance Relation T'I'II (->) (T'TT'I'II'I t tt i ii)
 where relate = T'I'II (\(T'TT'I'II'I x) -> x)

newtype T'I'TT'II t tt i ii = T'I'TT'II (t i (tt ii))

type instance Supertype (T'I'TT'II t tt i ii) = t i (tt ii)

instance Relation T'I'II (->) (T'I'TT'II t tt i ii)
 where relate = T'I'II (\(T'I'TT'II x) -> x)

instance Relation T'II'I (->) (T'I'TT'II t tt i ii)
 where relate = T'II'I T'I'TT'II

newtype T'I'TT'II'I t tt i ii = T'I'TT'II'I (t i (tt ii i))

type instance Supertype (T'I'TT'II'I t tt i ii) = t i (tt ii i)

instance Relation T'II'I (->) (T'I'TT'II'I t tt i ii)
 where relate = T'II'I T'I'TT'II'I

instance Relation T'I'II (->) (T'I'TT'II'I t tt i ii)
 where relate = T'I'II (\(T'I'TT'II'I x) -> x)

newtype T'TT'I'TTT'I t tt ttt i = T'TT'I'TTT'I (t (tt i) (ttt i))

type instance Supertype (T'TT'I'TTT'I t tt ttt i) = t (tt i) (ttt i)

instance Relation T'I'II (->) (T'TT'I'TTT'I u t tt i)
 where relate = T'I'II (\(T'TT'I'TTT'I x) -> x)

instance Relation T'II'I (->) (T'TT'I'TTT'I u t tt i)
 where relate = T'II'I T'TT'I'TTT'I

newtype T'I'TT'II'T'II'I t tt i ii = T'I'TT'II'T'II'I (t i (tt ii (t ii i)))

type instance Supertype (T'I'TT'II'T'II'I t tt i ii) = t i (tt ii (t ii i))

instance Relation T'II'I (->) (T'I'TT'II'T'II'I t tt i ii) where
 relate = T'II'I T'I'TT'II'T'II'I

instance Relation T'I'II (->) (T'I'TT'II'T'II'I t tt i ii) where
 relate = T'I'II (\(T'I'TT'II'T'II'I x) -> x)

newtype T'T'I'II'TT'I'II t tt i ii = T'T'I'II'TT'I'II (t (t i ii) (tt i ii))

type instance Supertype (T'T'I'II'TT'I'II t tt i ii) = t (t i ii) (tt i ii)

instance Relation T'II'I (->) (T'T'I'II'TT'I'II t tt i ii)
 where relate = T'II'I T'T'I'II'TT'I'II

instance Relation T'I'II (->) (T'T'I'II'TT'I'II t tt i ii)
 where relate = T'I'II (\(T'T'I'II'TT'I'II x) -> x)

newtype T'V'TT'II'I'TTT'I v tt t ttt i ii = T'V'TT'II'I'TTT'I (t (v tt ii i) (ttt i))

type Embedding = T'V'TT'II'I'TTT'I

pattern Embedding i = T'V'TT'II'I'TTT'I i

type instance Supertype (T'V'TT'II'I'TTT'I v t tt ttt i ii) = tt (v t ii i) (ttt i)

instance Relation T'I'II (->) (T'V'TT'II'I'TTT'I v t tt ttt i ii)
 where relate = T'I'II (\(T'V'TT'II'I'TTT'I x) -> x)

instance Relation T'II'I (->) (T'V'TT'II'I'TTT'I v t tt ttt i ii)
 where relate = T'II'I T'V'TT'II'I'TTT'I

newtype Label t tt l i = Label (t i)

type L = Label

type instance Supertype (L t _t l i) = t i

instance Relation T'I'II (->) (L t _t l i)
 where relate = T'I'II (\(Label x) -> x)

instance Relation T'II'I (->) (L t _t l i)
 where relate = T'II'I Label

newtype Recursive f = Recursive (f (Recursive f))

type Fixed = Recursive

pattern Fixed x = Recursive x

type instance Supertype (Recursive f) = f (Recursive f)

instance Relation T'I'II (->) (Recursive f)
 where relate = T'I'II (\(Recursive x) -> x)

instance Relation T'II'I (->) (Recursive f)
 where relate = T'II'I Recursive

newtype F'T'I'TT t tt i = F'T'I'TT (Recursive (t i `T'TT'I` tt))

type instance Supertype (F'T'I'TT t tt i) = Recursive (t i `T'TT'I` tt)

instance Relation T'I'II (->) (F'T'I'TT t tt i)
 where relate = T'I'II (\(F'T'I'TT x) -> x)

instance Relation T'II'I (->) (F'T'I'TT t tt i)
 where relate = T'II'I F'T'I'TT

type instance Supertype ((AR) Unit i) = i

instance Relation T'II'I (->) ((AR) Unit i)
 where relate = T'II'I (\i -> (\_ -> i))

instance Relation T'I'II (->) ((AR) Unit i)
 where relate = T'I'II (\f -> f Unit)

type instance Supertype ((AR) Void i) = Unit

instance Relation T'II'I (->) ((AR) Void i)
 where relate = T'II'I (\_ -> \case)

instance Relation T'I'II (->) ((AR) Void i)
 where relate = T'I'II (\_ -> Unit)

type AR = (->)
type AR_ = (->)
type AR__ = (->)
type AR___ = (->)
type AR____ = (->)
type AR_____ = (->)
type AR______ = (->)
type AR_______ = (->)

type RA ii i = AR i ii
type RA_ ii i = AR i ii
type RA__ ii i = AR i ii
type RA___ ii i = AR i ii
type RA____ ii i = AR i ii
type RA_____ ii i = AR i ii
type RA______ ii i = AR i ii
type RA_______ ii i = AR i ii

type AT = T'I'TT'II'T'II'I (AR) (P)
type AT_ = T'I'TT'II'T'II'I (AR) (P)
type AT__ = T'I'TT'II'T'II'I (AR) (P)
type AT___ = T'I'TT'II'T'II'I (AR) (P)
type AT____ = T'I'TT'II'T'II'I (AR) (P)
type AT_____ = T'I'TT'II'T'II'I (AR) (P)
type AT______ = T'I'TT'II'T'II'I (AR) (P)
type AT_______ = T'I'TT'II'T'II'I (AR) (P)

type TA ii i = AT i ii
type TA_ ii i = AT i ii
type TA__ ii i = AT i ii
type TA___ ii i = AT i ii
type TA____ ii i = AT i ii
type TA_____ ii i = AT i ii
type TA______ ii i = AT i ii
type TA_______ ii i = AT i ii

type TR = T'I'TT'II'I (AR) (P)
type TR_ = T'I'TT'II'I (AR) (P)
type TR__ = T'I'TT'II'I (AR) (P)
type TR___ = T'I'TT'II'I (AR) (P)
type TR____ = T'I'TT'II'I (AR) (P)
type TR_____ = T'I'TT'II'I (AR) (P)
type TR______ = T'I'TT'II'I (AR) (P)
type TR_______ = T'I'TT'II'I (AR) (P)

type RT ii i = TR i ii
type RT_ ii i = TR i ii
type RT__ ii i = TR i ii
type RT___ ii i = TR i ii
type RT____ ii i = TR i ii
type RT_____ ii i = TR i ii
type RT______ ii i = TR i ii
type RT_______ ii i = TR i ii

type AS = T'TT'I'II'I (P) (AR)
type AS_ = T'TT'I'II'I (P) (AR)
type AS__ = T'TT'I'II'I (P) (AR)
type AS___ = T'TT'I'II'I (P) (AR)
type AS____ = T'TT'I'II'I (P) (AR)
type AS_____ = T'TT'I'II'I (P) (AR)
type AS______ = T'TT'I'II'I (P) (AR)
type AS_______ = T'TT'I'II'I (P) (AR)

type C'AR t tt = forall i . t i `AR` tt i

type C'AR_ t tt = C'AR t tt
type C'AR__ t tt = C'AR t tt
type C'AR___ t tt = C'AR t tt
type C'AR____ t tt = C'AR t tt
type C'AR_____ t tt = C'AR t tt
type C'AR______ t tt = C'AR t tt
type C'AR_______ t tt = C'AR t tt

type C'AT t tt = forall i . t i `AT` tt i

type C'AT_ t tt = C'AT t tt
type C'AT__ t tt = C'AT t tt
type C'AT___ t tt = C'AT t tt
type C'AT____ t tt = C'AT t tt
type C'AT_____ t tt = C'AT t tt
type C'AT______ t tt = C'AT t tt
type C'AT_______ t tt = C'AT t tt

type C'TR t tt = forall i . t i `TR` tt i

type C'TR_ t tt = C'TR t tt
type C'TR__ t tt = C'TR t tt
type C'TR___ t tt = C'TR t tt
type C'TR____ t tt = C'TR t tt
type C'TR_____ t tt = C'TR t tt
type C'TR______ t tt = C'TR t tt
type C'TR_______ t tt = C'TR t tt

data Void

data Unit = Unit

data Product i ii = These i ii

type P = Product
type P_ = Product
type P__ = Product

type P'T'I'TT'I = T'TT'I'TTT'I (P)

data Sum i ii = This i | That ii

type S = Sum
type S_ = Sum
type S__ = Sum
type S___ = Sum

type S'T'I'TT'I = T'TT'I'TTT'I (S)

type Whether = T'T'I'II'TT'I'II Sum Product

type W = Whether

type family Minus r i where
 Minus (i `S` ii) i = ii
 Minus (ii `S` i) i = ii
 Minus (ii `S` eee) i = ii `M` i `S` eee
 Minus i i = Void

type M i ii = Minus i ii
type M_ i ii = Minus i ii
type M__ i ii = Minus i ii
