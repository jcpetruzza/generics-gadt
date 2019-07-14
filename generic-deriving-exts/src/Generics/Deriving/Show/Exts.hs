{-# OPTIONS_GHC -Wno-orphans #-}
{-# LANGUAGE UndecidableInstances #-}
module Generics.Deriving.Show.Exts
  (
  ) where

import Generics.Deriving.Show

import GHC.Generics.Exts

instance GShow' t => GShow' (GADT a t) where
  gshowsPrec' ty n (GADT t) = gshowsPrec' ty n t
  isNullary (GADT t) = isNullary t

instance (c => GShow' t) => GShow' (c :=>: t) where
  gshowsPrec' ty n (Ct t) = gshowsPrec' ty n t
  isNullary (Ct t) = isNullary t


instance GShow' (SubstSk free t) => GShow' (GEx free '[] ftvars btvars a t) where
  gshowsPrec' ty n (QF t) = gshowsPrec' ty n t
  isNullary (QF t) = isNullary t


instance
  (forall (v :: k) ftvars' btvars' . GShow' (GEx (x :> v ': free) bound ftvars' btvars' a t))
    => GShow' (GEx free (V x k K ': bound) ftvars btvars a t) where
  gshowsPrec' ty n = \case
    Ex  t -> gshowsPrec' ty n t
    ExG t -> gshowsPrec' ty n t

  isNullary = \case
    Ex  t -> isNullary t
    ExG t -> isNullary t

