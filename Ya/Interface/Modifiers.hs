module Ya.Interface.Modifiers where

import Ya.Semantics.Structures

pattern Same :: i `AR_` i
pattern Same x = x

pattern Null, Fail :: Void `AR_` Void
pattern Null x = x
pattern Fail x = x

pattern Only, Pass :: Unit `AR_` Unit
pattern Only x = x
pattern Pass x = x

pattern Both :: Unit `S` Unit `AR_` Unit `S` Unit
pattern Both x = x

pattern Sole :: Unit `P` Unit `AR_` Unit `P` Unit
pattern Sole x = x

pattern None :: Void `P` Unit `AR_` Void `P` Unit
pattern None x = x

pattern Some :: Unit `S` i `AR_` Unit `S` i
pattern Some x = x

pattern Back :: forall e ee r . (r ~ e `S` ee) => e -> r
pattern Back x = This x
