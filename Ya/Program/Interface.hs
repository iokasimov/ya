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
	has :: Attribute r e

instance Field e e
	where has = identity

instance Field e (Only e)
	where has = W_I_II_II `a` U_I_UU_III_U_II_I
		`i` \(Only x) -> These `i` x `i` \new -> Only new

instance Field e (e `LM` ee)
	where has = W_I_II_II `a` U_I_UU_III_U_II_I
		`i` \(These f fs) -> These `i` f `i` \f_ -> These f_ fs

instance {-# OVERLAPS #-} Field e ee => Field e (eee `LM` ee) where
	has = W_I_II_II `a` U_I_UU_III_U_II_I `i` \(These old fs) ->These
		`i` inspect (has @e @ee) fs
		`i` \new -> These old `i` adjust (has @e @ee) (\_ -> new) fs

instance Field (t e) (U_T_I_TT_I LM tt t e)
	where has = W_I_II_II `a` U_I_UU_III_U_II_I `i`
		\(U_T_I_TT_I (These y x)) -> These `i` x `i` \x_ -> U_T_I_TT_I (These y x_)

instance {-# OVERLAPS #-} Field e (tt ee) => Field e (U_T_I_TT_I LM tt t ee) where
	has = W_I_II_II `a` U_I_UU_III_U_II_I `i` \(U_T_I_TT_I (These x y)) -> These
		`i` inspect (has @e @(tt ee)) x
		`i` \new -> U_T_I_TT_I / These
			`i` adjust (has @e @(tt ee)) (\_ -> new) x
			`i` y

instance Field (Focused e) (Construction t e)
	where has = W_I_II_II `a` U_I_UU_III_U_II_I `i`
		\(Root old xs) -> These / Focused old / \new -> Root (unwrap new) xs

instance Covariant Endo Semi Functor (->) t =>
	Field (t (Construction t e)) (Construction t e)
	where has = W_I_II_II `a` U_I_UU_III_U_II_I `i`
		\(Root x old) -> These
			(wrap @(R_U_I_T_I _ _ _) `fo` old)
			(\new -> Root x / rw @Arrow @(R_U_I_T_I _ _ _) `fo` new)

part :: forall t tt e .
	Field (t e) (tt e) =>
	Attribute (tt e) (t e)
part = has @(t e) @(tt e)

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

type family Vector x xs where
	Vector x (y `LM` xs) = (Same x y, Vector x xs)
	Vector x y = Same x y

class Stack datastructure morphism where
	pop :: morphism `TI` datastructure item `TI` Optional item
	push :: item -> morphism `TI` datastructure item `TI` item

instance Stack List Statefully where
	pop = W_I_I_II `a` U_I_UU_II_III `i` \case
		Empty @List _ -> These `i` Empty @List () `i` (None ())
		List (Yet x xs) -> These `i` (T_TT_I / xs `yo` R_U_I_T_I) `i` Some x
	push x = W_I_I_II `a` U_I_UU_II_III `yi` \s -> These
		`i` rewrap (Some `a` R_U_I_T_I `a` Yet x `a` (`yo` rw @Arrow @(R_U_I_T_I _ _ _))) s
		`i` x

instance Stack (Construction Optional) Statefully where
	pop = W_I_I_II `a` U_I_UU_II_III `yi` \case
		R_U_I_T_I (Yet x (Some xs)) -> These `i` R_U_I_T_I xs `i` Some x
		R_U_I_T_I (Yet x (None _)) -> These `i_i` R_U_I_T_I `i` Yet x (None ()) `i_i` (None ())
	push x = W_I_I_II `a` U_I_UU_II_III `yi` \old ->
		let new = Next x `rwr` old in These new x

instance {-# OVERLAPS #-} Stack datastructure Statefully => Stack datastructure Transition where
	pop = (rwr `compose` rwr) (fio (\(These x y) -> These y x)) (pop @datastructure @Statefully)
	push x = (rwr `compose` rwr) (fio (\(These x y) -> These y x)) (push @datastructure @Statefully x)

type family Scrolling datastructure = result | result -> datastructure where
	Scrolling List = U_T_I_TT_I LM (U_T_I_TT_I LM List Identity) List

instance Mapping Straight Straight Arrow Arrow
	(R_U_I_T_I LM Optional) (U_T_I_TT_I LM (U_T_I_TT_I LM List Identity) List)
	where mapping = rewrap / \from (Root x xs) ->
		(U_T_I_TT_I (These
			(Empty @List () `lm` Identity (from x) `u_u` U_T_I_TT_I)
			((T_TT_I / xs `yo` R_U_I_T_I) `yo` from)
			)
		)

type family Orientation datastructure where
	Orientation List = Horizontal

class Scrollable datastructure has morphism where
	scroll :: Orientation datastructure -> morphism
		`TI` Scrolling datastructure has
		`TI` Optional (Scrolling datastructure has)

-- TODO: try use the fact that `Horizontal` ~ `Boolean`
-- `Boolean` is `Representative` for `U_I_I LM`
instance Scrollable List has Statefully where
	scroll (That _) = W_I_I_II `a` U_I_UU_II_III `yi` \case
		previous@(U_T_I_TT_I (These (U_T_I_TT_I (These (T_TT_I bs) (Identity x))) (List (Yet f fs)))) -> These
			(U_T_I_TT_I (These (U_T_I_TT_I (These (List (Yet x (bs `yo` unwrap))) (Identity f))) (T_TT_I / fs `yo` wrap )))
			(Some previous)
		previous@(_) -> These previous (None ())
	scroll (This _) = W_I_I_II `a` U_I_UU_II_III `yi` \case
		previous@(U_T_I_TT_I (These (U_T_I_TT_I (These (List (Yet b bs)) (Identity x))) (T_TT_I fs))) -> These
			(U_T_I_TT_I (These (U_T_I_TT_I (These (T_TT_I / bs `yo` R_U_I_T_I) (Identity b))) (List (Yet x (fs `yo` unwrap)))))
			(Some previous)
		previous@(_) -> These previous (None ())

instance {-# OVERLAPS #-} Scrollable t has Statefully => Scrollable t has Transition where
	scroll orient = W_I_II_I `compose` U_I_UU_II_III
		`compose` fio (\(These x y) -> These y x)
		`compose` unwrap `compose` unwrap
		/ scroll @t @has @Statefully orient

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

class Automatable morphism where
	review :: morphism old old
	switch :: new -> morphism new new
	-- change_ :: (new -> new) -> morphism new old

instance Automatable Statefully where
	review = W_I_I_II `a` U_I_UU_II_III `i` \old -> These `i` old `i` old
	switch new = W_I_I_II `a` U_I_UU_II_III `i` \old -> These `i` new `i` new
	-- change_ f = W_I_I_II `a` U_I_UU_II_III `i` \s -> These `i` f s `i` s

instance Automatable Transition where
	review = W_I_II_I `a` U_I_UU_II_III `i` \old -> These `i` old `i` old
	switch new = W_I_II_I `a` U_I_UU_II_III `i` \old -> These `i` new `i` new
