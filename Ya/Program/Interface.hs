{-# OPTIONS_GHC -fno-warn-orphans #-}
{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE UndecidableSuperClasses #-}
module Ya.Program.Interface where

import Ya.Algebra
import Ya.Program.Patterns
import Ya.Program.Primitive

class Field e r where
 has :: Reference r e e

instance Field e e where
 has = self

instance Field e (e `LM` ee) where
 has = U_I_UU_III_U_II_I `i` \(These f fs) -> f `lm` (`lm` fs)

instance {-# OVERLAPS #-} Field e ee => Field e (eee `LM` ee) where
 has = U_I_UU_III_U_II_I `i` \(These old fs) -> These
  `i` (has @e @ee `yi'` fs `huuuu` this)
  `i` \new -> old `lm` adjust (Attribute `yi` has @e @ee) (but new) fs

class Match e ee where
 match :: (e -> r) -> (ee -> r) -> (ee -> r)

instance Match e e where
 match target _ = target

instance Match e (e `ML` es) where
 match target rest = target `rf` rest `ha` That

instance Match e (es `ML` e) where
 match target rest = rest `ha` This `rf` target

instance {-# OVERLAPS #-} Match e ee => Match e (ee `ML` es) where
 match target rest = match `yi` target `yi` rest `ha` This `rf` rest `ha` That

type family Vector x xs where
 Vector x (y `LM` xs) = (x ~ y, Vector x xs)
 Vector x y = x ~ y

class Literal datastructure item literal
 where as :: literal -> datastructure item

instance Literal (Construction Optional) item item where
 as x = Construct `yi` Last x

instance Literal (Construction Optional) item init =>
 Literal (Construction Optional) item (init `LM` item) where
 as (These init last) =
  (as @(Construction Optional) @item init `yoklKL`  push `ho` State `ho` Back)
  `yi'_yi'_yi'_o`  Construct (Last last) `yi` this

instance Literal (Construction (U_I_I LM `T_TT_I` Optional)) item item where
 as x = Root x (T_TT_I (U_I_I (None () `lm` None ())))

instance (Literal (Construction (U_I_I LM `T_TT_I` Optional)) item lst, Literal (Construction (U_I_I LM `T_TT_I` Optional)) item rst) =>
 Literal (Construction (U_I_I LM `T_TT_I` Optional)) item (item `LM` Optional lst `LM` Optional rst) where
 as (These (These x lx) rx) = Root x `ha` T_TT_I `ha` U_I_I
   `yi_yi_yi` lx `yo` as @(Binary Tree) `ho` unwrap @Arrow
     `yi_lm` rx `yo` as @(Binary Tree) `ho` unwrap @Arrow

class Stack datastructure where
 pop :: Transition `TI` datastructure item `TI` Optional item
 push :: item -> Transition `TI` datastructure item `TI` item

instance Stack List where
 pop = W_I_I_II `ha` U_I_UU_II_III `i` \case
  Empty @List _ -> These `i` Empty @List () `i` (None ())
  T_TT_I (Some (Construct (Yet x xs))) -> These `i` (T_TT_I / xs `yo` R_U_I_T_I) `i` Some x
 push x = W_I_I_II `ha` U_I_UU_II_III `yi` \s -> These
  `i` rewrap (Some `ha` R_U_I_T_I `ha` Yet x `ha` (`yo` unwrap @Arrow @(R_U_I_T_I _ _ _))) s
  `i` x

instance Stack (Construction Optional) where
 pop = W_I_I_II `ha` U_I_UU_II_III `yi` \case
  R_U_I_T_I (Recursive (U_I_T_II (These x (Some xs)))) -> These `i` R_U_I_T_I xs `i` Some x
  R_U_I_T_I (Recursive (U_I_T_II (These x (None _)))) -> These `i_i` R_U_I_T_I `i` Yet x (None ()) `i_i` (None ())
 push x = W_I_I_II `ha` U_I_UU_II_III `yi` \old ->
  let new = Next x `rwr` old in These new x

type Scrolling datastructure =
 U_T_I_TT_I LM Only (Shafted datastructure)

type family Shafted datastructure = result | result -> datastructure where
 Shafted (Construction Singular) = U_T_I_TT_I LM Stream Stream
 Shafted (Optional `T_TT_I` Construction Optional) = U_I_I LM `T_TT_I` List
 Shafted (Construction (U_I_I LM `T_TT_I` Optional)) = U_T_I_TT_I LM
  (U_I_I LM `T_TT_I` Optional) (List `T_TT_I` U_I_I ML `T_TT_I` U_T_I_TT_I LM Only (Optional `T_TT_I` Binary Tree))

instance Mapping Straight Straight Arrow Arrow (Construction Optional) (U_T_I_TT_I LM Only (U_I_I LM `T_TT_I` List)) where
 mapping = rewrap / \from (Root x xs) ->
  from x `hu` Singular `yi_yi_lm` Empty @List () `yi_lm` xs `yo` R_U_I_T_I `huu` T_TT_I `yo` from
   `huuuuu` T_TT_I `ha` U_I_I `huuuuuu` U_T_I_TT_I

type family Orientation datastructure where
 Orientation Stream = () `ML` ()
 Orientation (Optional `T_TT_I` Construction Optional) = () `ML` ()
 Orientation (Construction (U_I_I LM `T_TT_I` Optional)) = () `ML` () `ML` ()

type family Scrolled datastructure where
 Scrolled Stream = Only
 Scrolled (Optional `T_TT_I` Construction Optional) = Optional
 Scrolled (Construction (U_I_I LM `T_TT_I` Optional)) = Optional

class Scrollable datastructure item where
 scroll :: Orientation datastructure
  `ARR` Transition
   `TI` Scrolling datastructure item
   `TI` Scrolled datastructure item

instance Scrollable (Optional `T_TT_I` Construction Optional) item where
 scroll way = unwrap @Arrow `ha` tnj @(State (Scrolling List _))
  `i_i_i_i_i` enter @(State `TI` Scrolling List _ `JT` Halts)
    `yukl` State `i_i_i` pop `haa'` (has @(Shafted List _) `hu` Attribute) `ho'` rep way `yokl` on @Halts
    `yokl` State `haaa` put `hoo_ha` unwrap @Attribute `ho` (has @(Focused _)  `hu` Attribute) `ho` unwrap @Attribute
    `yokl` State `haaa` push `hoo_ha` unwrap @Attribute `ho` (has @(Shafted List _) `hu` Attribute) `ho'` rep (not way)

-- TODO: instance Scrollable (Construction (U_I_I LM `T_TT_I` Optional)) item where

-- TODO: think about alternative implementations
instance Mapping Straight Straight (->) (->) (List `T_TT_I` Cascading List) List
	where mapping = rwr / \from -> \case
		T_TT_I (T_TT_I (U_I_II (This ())))
			-> T_TT_I (U_I_II (This ()))
		T_TT_I (T_TT_I (U_I_II (That (R_U_I_T_I (Recursive (U_I_T_II (These (Cascading (T_TT_I (U_I_II (This ())))) _)))))))
			-> T_TT_I (U_I_II (This ()))
		T_TT_I (T_TT_I (U_I_II (That (R_U_I_T_I (Recursive (U_I_T_II (These (Cascading (T_TT_I (U_I_II (That
			(R_U_I_T_I (Recursive (U_I_T_II (These x xx)))))))) xxx)))))))
			-> T_TT_I (U_I_II (That (R_U_I_T_I (Recursive (U_I_T_II (These (from x)
					(fo @Arrow unwrap `compose` unwrap @Arrow / map @Straight @Straight @(->) @(->) @(List `T_TT_I` Cascading List) @List from
						(T_TT_I (T_TT_I (U_I_II (That (R_U_I_T_I (Recursive (U_I_T_II (These (Cascading `ha` T_TT_I / xx `yo` R_U_I_T_I) xxx))))))))
					)
				))))))

instance Mapping Straight Straight (->) (->) (Construction Optional) (Construction Optional `T_TT_I` Construction Optional)
	where mapping = rwr / \from -> \case
		R_U_I_T_I (Recursive (U_I_T_II (These e (U_I_II (This ()))))) ->
			T_TT_I `ha` R_U_I_T_I
				`i` Last (R_U_I_T_I (Recursive (U_I_T_II (These (from e) (U_I_II (This ()))))))
		R_U_I_T_I (Recursive (U_I_T_II (These e (U_I_II (That es))))) ->
			T_TT_I `ha` R_U_I_T_I
				`ha` Next (R_U_I_T_I (Recursive (U_I_T_II (These (from e) (U_I_II (That / unwrap (R_U_I_T_I es `yo` from)))))))
				`i` Last (map @Straight @Straight @(->) @(->) from (R_U_I_T_I es))
