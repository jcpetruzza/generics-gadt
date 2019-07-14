{-# OPTIONS_GHC -Wno-orphans #-}
{-# LANGUAGE UndecidableInstances #-}
module Generics.Deriving.Eq.Exts
  (
  ) where

import Generics.Deriving.Eq

import GHC.Generics.Exts

instance GEq' t => GEq' (GM1 i a t) where
  geq' (GM1 l) (GM1 r) = geq' l r

instance (c => GEq' t) => GEq' (c :=>: t) where
  geq' (Ct l) (Ct r) = geq' l r


instance GEq' (SubstSk free t) => GEq' (GEx free '[] ftvars btvars a t) where
  geq' (QF l) (QF r) = geq' l r

instance
  ( GEq' (GEx (x :> v ': free) bound (Ty v ': ftvars) btvars a t)
  ) => GEq' (GEx free (V x k K ': bound) ftvars (Ty v ': btvars) a t) where
  geq' (ExG l) (ExG r) = geq' l r

