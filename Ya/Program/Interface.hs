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
 where lit :: literal -> datastructure item

instance Literal (Construction Optional) item item
 where lit x = Construct `yi` Last x

instance Literal (Construction Optional) item init =>
 Literal (Construction Optional) item (init `LM` item) where
 lit (These init last) =
  (lit @(Construction Optional) @item init `yoklKL`  push `o` State `o` Back)
  `rw_rw_rw_o`  Construct (Last last) `yi` this

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

type family Scrolling datastructure = result | result -> datastructure where
	Scrolling Stream = Labeled Stream (U_T_I_TT_I LM (U_T_I_TT_I LM Stream Only) Stream)
	Scrolling List = Labeled List (U_T_I_TT_I LM (U_T_I_TT_I LM List Only) List)

type family Context datastructure = result | result -> datastructure where
 Context (Labeled List (U_T_I_TT_I LM (U_T_I_TT_I LM List Only) List)) = U_T_I_TT_I LM List List

instance Mapping Straight Straight Arrow Arrow
	(R_U_I_T_I LM Optional) (Labeled List (U_T_I_TT_I LM (U_T_I_TT_I LM List Identity) List))
	where mapping = rewrap / \from (Root x xs) ->
		label (U_T_I_TT_I (These
			(Empty @List () `lm` Identity (from x) `u_u` U_T_I_TT_I)
			((T_TT_I / xs `yo` R_U_I_T_I) `yo` from)
			)
		)

type family Orientation datastructure where
	Orientation Stream = Way
	Orientation List = Way

type family Scrolled datastructure where
	Scrolled Stream = Only
	Scrolled List = Optional

class Scrollable datastructure item where
 scroll :: Orientation datastructure -> Transition
  `TI` Scrolling datastructure item
  `TI` (Scrolled datastructure) (Scrolling datastructure item)

-- TODO: try use the fact that `Way` ~ `Boolean`
-- `Boolean` is `Representative` for `U_I_I LM`
instance Scrollable List item where
	scroll (That _) = W_I_I_II `a` U_I_UU_II_III `yi` \case
		previous@(T_'_I (U_T_I_TT_I (These (U_T_I_TT_I (These (T_TT_I bs) (Identity x))) (T_TT_I (Some (Construct (Yet f fs))))))) -> These
			(T_'_I (U_T_I_TT_I (These (U_T_I_TT_I (These (List `a` Some `a` Construct `yi`Yet x (bs `yo` unwrap)) (Identity f))) (T_TT_I / fs `yo` wrap ))))
			(Some previous)
		previous@(_) -> These previous (None ())
	scroll (This _) = W_I_I_II `a` U_I_UU_II_III `yi` \case
		previous@(T_'_I (U_T_I_TT_I (These (U_T_I_TT_I (These (T_TT_I (Some (Construct (Yet b bs)))) (Identity x))) (T_TT_I fs)))) -> These
			(T_'_I (U_T_I_TT_I (These (U_T_I_TT_I (These (T_TT_I / bs `yo` R_U_I_T_I) (Identity b))) (List `a` Some `a` Construct `yi` Yet x (fs `yo` unwrap)))))
			(Some previous)
		previous@(_) -> These previous (None ())

instance {-# OVERLAPS #-} Field (Focused e)
 (Labeled List (U_T_I_TT_I LM (U_T_I_TT_I LM List Focused) List) e) where
  field = W_I_II_II `a` U_I_UU_III_U_II_I
   `i` \(T_'_I (U_T_I_TT_I (These (U_T_I_TT_I (These bs x)) fs))) -> These
    `i` x
    `i` \x' -> T_'_I (U_T_I_TT_I (These (U_T_I_TT_I (These bs x')) fs))

instance {-# OVERLAPS #-} Field (U_T_I_TT_I LM List List e)
 (Labeled List (U_T_I_TT_I LM (U_T_I_TT_I LM List Only) List) e) where
  field = W_I_II_II `a` U_I_UU_III_U_II_I
   `i` \(T_'_I (U_T_I_TT_I (These (U_T_I_TT_I (These bs x)) fs))) -> These
    `i` U_T_I_TT_I (These bs fs)
    `i` \(U_T_I_TT_I (These bs' fs')) -> T_'_I (U_T_I_TT_I (These (U_T_I_TT_I (These bs' x)) fs'))

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

instance Mapping Straight Straight (->) (->)
	(R_U_I_T_I LM Optional)
	(R_U_I_T_I LM Optional `T_TT_I` R_U_I_T_I LM Optional)
	where mapping = rwr / \from -> \case
		R_U_I_T_I (Recursive (U_I_T_II (These e (U_I_II (This ()))))) ->
			T_TT_I `a` R_U_I_T_I
				`i` Last (R_U_I_T_I (Recursive (U_I_T_II (These (from e) (U_I_II (This ()))))))
		R_U_I_T_I (Recursive (U_I_T_II (These e (U_I_II (That es))))) ->
			T_TT_I `a` R_U_I_T_I
				`a` Next (R_U_I_T_I (Recursive (U_I_T_II (These (from e) (U_I_II (That / unwrap (R_U_I_T_I es `yo` from)))))))
				`i` Last (map @Straight @Straight @(->) @(->) from (R_U_I_T_I es))
