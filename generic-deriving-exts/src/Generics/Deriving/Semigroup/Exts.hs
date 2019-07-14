{-# OPTIONS_GHC -Wno-orphans #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE UndecidableInstances #-}
module Generics.Deriving.Semigroup.Exts
  (
  ) where

import Data.Proxy

import Generics.Deriving.Semigroup

import GHC.Generics.Exts
import GHC.Generics.Pruning

instance (GPruning a t, GSemigroup' (Pruned a t)) => GSemigroup' (GADT a t) where
  gsappend' (GADT l) (GADT r) = GADT $ gextend (Proxy :: Proxy a) $ gsappend' (gprune (Proxy :: Proxy a) l) (gprune (Proxy :: Proxy a) r)

instance (c => GSemigroup' t) => GSemigroup' (c :=>: t) where
  gsappend' (Ct l) (Ct r) = Ct (gsappend' l r)


instance GSemigroup' (SubstSk free t) => GSemigroup' (GEx free '[] ftvars btvars a t) where
  gsappend' (QF l) (QF r) = QF (gsappend' l r)


instance
  ( GSemigroup' (GEx (x :> v ': free) bound (Ty v ': ftvars) btvars a t)
  ) => GSemigroup' (GEx free (V x k K ': bound) ftvars (Ty v ': btvars) a t) where
  gsappend' (ExG l) (ExG r) = ExG (gsappend' l r)

