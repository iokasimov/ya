{-# LANGUAGE AllowAmbiguousTypes #-}
module Ya.Algebra.Definition where

import Ya.Algebra.Abstract

class Transformation v from into f g where
	transformation :: v from s t -> into (f s) (g t)

transform :: forall v from into f g s t .
	Transformation v from into f g =>
	Castable Dual Arrow (v from s t) =>
	Supertype (v from s t) -> into (f s) (g t)
transform from = transformation @v @from @into @f @g @s @t (wrap @Arrow from)