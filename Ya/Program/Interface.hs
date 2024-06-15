{-# OPTIONS_GHC -fno-warn-orphans #-}
{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE UndecidableSuperClasses #-}
module Ya.Program.Interface where

import Ya.Algebra
import Ya.Program.Primitive

on :: (e `ARR` ee) `ARR` (e `ARR` r) `ARR` (e `ARR` r)
on constructor handle = \x -> that (constructor x `lm` handle x)

class Field e r where
	field :: Attribute r e

has :: Field e r => Attribute r e
has = field

instance Field e e
	where field = identity

instance Field e (Only e)
	where field = W_I_II_II `a` U_I_UU_III_U_II_I
		`i` \(Only x) -> These `i` x `i` \new -> Only new

instance Field e (e `LM` ee)
	where field = W_I_II_II `a` U_I_UU_III_U_II_I
		`i` \(These f fs) -> These `i` f `i` \f_ -> These f_ fs

instance {-# OVERLAPS #-} Field e ee => Field e (eee `LM` ee) where
	field = W_I_II_II `a` U_I_UU_III_U_II_I `i` \(These old fs) -> These
		`i` inspect (field @e @ee) fs
		`i` \new -> These old `i` adjust (field @e @ee) (\_ -> new) fs

instance {-# OVERLAPS #-} Field (Focused e) (Construction t e)
	where field = W_I_II_II `a` U_I_UU_III_U_II_I `i`
		\(Root old xs) -> These / Focused old / \new -> Root (unwrap new) xs

instance {-# OVERLAPS #-} Covariant Endo Semi Functor (->) t =>
	Field (t (Construction t e)) (Construction t e)
	where field = W_I_II_II `a` U_I_UU_III_U_II_I `i`
		\(Root x old) -> These
			(wrap @(R_U_I_T_I _ _ _) `fo` old)
			(\new -> Root x / rw @Arrow @(R_U_I_T_I _ _ _) `fo` new)

section :: forall t tt e .
	Field (t e) (tt e) =>
	Attribute (tt e) (t e)
section = field @(t e) @(tt e)

sub :: forall t tt e .
	Field (t e) (tt e) =>
	Attribute (tt e) (t e)
sub = field @(t e) @(tt e)

class Match e ee where
  match :: (e -> r) -> (ee -> r) -> (ee -> r)

instance Match e e where
  match target _ = target

instance Match e (e `ML` es) where
  match target rest = target `rf` rest `a` That

instance Match e (es `ML` e) where
  match target rest = rest `a` This `rf` target

instance {-# OVERLAPS #-} Match e ee => Match e (ee `ML` es) where
  match target rest = match `yi` target `yi` rest `a` This `rf` rest `a` That

-- TODO: replace `Same` with `~`
type family Vector x xs where
	Vector x (y `LM` xs) = (Same x y, Vector x xs)
	Vector x y = Same x y

class Literal datastructure item literal
 where literal :: literal -> datastructure item

instance Literal (Construction Optional) item item where
 literal x = Construct `yi` Last x

instance Literal (Construction Optional) item init =>
 Literal (Construction Optional) item (init `LM` item) where
 literal (These init last) =
  (literal @(Construction Optional) @item init `yoklKL`  push `o` State `o` Back)
  `rw_rw_rw_o`  Construct (Last last) `yi` this

instance Literal (Construction (U_I_I LM `T_TT_I` Optional)) item item where
 literal x = Root x (T_TT_I (U_I_I (None () `lm` None ())))

instance (Literal (Construction (U_I_I LM `T_TT_I` Optional)) item lst, Literal (Construction (U_I_I LM `T_TT_I` Optional)) item rst) =>
 Literal (Construction (U_I_I LM `T_TT_I` Optional)) item (item `LM` Optional lst `LM` Optional rst) where
 literal (These (These x lx) rx) = Root x `a` T_TT_I `a` U_I_I
   `yi_yi_yi` lx `yo` literal @(Binary Tree) `o` unwrap
     `yi_lm` rx `yo` literal @(Binary Tree) `o` unwrap

class Stack datastructure where
	pop :: Transition `TI` datastructure item `TI` Optional item
	push :: item -> Transition `TI` datastructure item `TI` item

instance Stack List where
	pop = W_I_I_II `a` U_I_UU_II_III `i` \case
		Empty @List _ -> These `i` Empty @List () `i` (None ())
		T_TT_I (Some (Construct (Yet x xs))) -> These `i` (T_TT_I / xs `yo` R_U_I_T_I) `i` Some x
	push x = W_I_I_II `a` U_I_UU_II_III `yi` \s -> These
		`i` rewrap (Some `a` R_U_I_T_I `a` Yet x `a` (`yo` rw @Arrow @(R_U_I_T_I _ _ _))) s
		`i` x

instance Stack (Construction Optional) where
	pop = W_I_I_II `a` U_I_UU_II_III `yi` \case
		R_U_I_T_I (Yet x (Some xs)) -> These `i` R_U_I_T_I xs `i` Some x
		R_U_I_T_I (Yet x (None _)) -> These `i_i` R_U_I_T_I `i` Yet x (None ()) `i_i` (None ())
	push x = W_I_I_II `a` U_I_UU_II_III `yi` \old ->
		let new = Next x `rwr` old in These new x

type Scrolling datastructure =
 Labeled datastructure (U_T_I_TT_I LM Only (Situation datastructure))

type family Situation datastructure = result | result -> datastructure where
 Situation (Construction Singular) = U_T_I_TT_I LM Stream Stream
 Situation (Optional `T_TT_I` Construction Optional) = U_I_I LM `T_TT_I` List
 Situation (Construction (U_I_I LM `T_TT_I` Optional)) = U_T_I_TT_I LM
  (U_I_I LM `T_TT_I` Optional) (List `T_TT_I` U_I_I ML `T_TT_I` U_T_I_TT_I LM Only (Optional `T_TT_I` Binary Tree))

instance Mapping Straight Straight Arrow Arrow (Construction Optional) (Labeled List (U_T_I_TT_I LM Only (U_I_I LM `T_TT_I` List))) where
 mapping = rewrap / \from (Root x xs) -> 
  from x `u` Singular `yi_yi_lm` Empty @List () `yi_lm` xs `yo` R_U_I_T_I `uu` T_TT_I `yo` from
   `uuuuu` T_TT_I `a` U_I_I `uuuuuu` U_T_I_TT_I `o` label

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

instance Scrollable List item where
 scroll way = unwrap `a` tnj @(State (Scrolling List _))
  `i_i_i_i_i` enter @(State (Scrolling List _) `JT` Halts)
    `yukl` State @(Scrolling List _) `i_i_i` pop `aa` sub @(Situation List) `o_rw_o` rep way `yokl` as' @(Optional _)
    `yokl` State @(Scrolling List _) `aaa` put `oo_a` sub @Focused `o_rw_o` as @item @Attribute
    `yokl` State @(Scrolling List _) `aaa` push `oo_a` sub @(Situation List) `o_rw_o` rep (not way)

instance {-# OVERLAPS #-} Field (Focused e)
 (Labeled List (U_T_I_TT_I LM Focused (U_I_I LM `T_TT_I` List)) e) where
  field = W_I_II_II `a` U_I_UU_III_U_II_I `i` \(T_'_I (U_T_I_TT_I (These x xs))) -> x `lm` T_'_I `a` U_T_I_TT_I `a` (`lm` xs)

instance {-# OVERLAPS #-} Field ((U_I_I LM `T_TT_I` List) e)
 (Labeled List (U_T_I_TT_I LM Focused (U_I_I LM `T_TT_I` List)) e) where
  field = W_I_II_II `a` U_I_UU_III_U_II_I `i` \(T_'_I (U_T_I_TT_I (These x xs))) -> xs `lm` T_'_I `a` U_T_I_TT_I `a` (x `lm`)

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
					(fo unwrap `compose` unwrap / map @Straight @Straight @(->) @(->) @(List `T_TT_I` Cascading List) @List from
						(T_TT_I (T_TT_I (U_I_II (That (R_U_I_T_I (Recursive (U_I_T_II (These (Cascading `a` T_TT_I / xx `yo` R_U_I_T_I) xxx))))))))
					)
				))))))

instance Mapping Straight Straight (->) (->) (Construction Optional) (Construction Optional `T_TT_I` Construction Optional)
	where mapping = rwr / \from -> \case
		R_U_I_T_I (Recursive (U_I_T_II (These e (U_I_II (This ()))))) ->
			T_TT_I `a` R_U_I_T_I
				`i` Last (R_U_I_T_I (Recursive (U_I_T_II (These (from e) (U_I_II (This ()))))))
		R_U_I_T_I (Recursive (U_I_T_II (These e (U_I_II (That es))))) ->
			T_TT_I `a` R_U_I_T_I
				`a` Next (R_U_I_T_I (Recursive (U_I_T_II (These (from e) (U_I_II (That / unwrap (R_U_I_T_I es `yo` from)))))))
				`i` Last (map @Straight @Straight @(->) @(->) from (R_U_I_T_I es))
