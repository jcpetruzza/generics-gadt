{-# OPTIONS_GHC -Wno-orphans #-}
{-# LANGUAGE UndecidableInstances #-}
module Generics.Deriving.Monoid.Exts
  (
  ) where

import Data.Kind(Type)
import Data.Proxy
import GHC.Generics

import Generics.Deriving.Monoid

import GHC.Generics.Exts
import GHC.Generics.Pruning

instance (GPruning t, GMonoid' (Pruned t)) => GMonoid' (GADT t) where
  gmempty' = GADT $ gextend gmempty'
  gmappend' (GADT l) (GADT r) = GADT $ gextend $ gmappend' (gprune l) (gprune r)

instance (c, c => GMonoid' t) => GMonoid' (c :=>: t) where
  gmempty' = Ct gmempty'
  gmappend' (Ct l) (Ct r) = Ct (gmappend' l r)


instance (GMonoid' (SubstSk free t), a ~ SubstSk free refined) => GMonoid' (GEx free '[] ftvars '[] refined a t) where
  gmempty' = QF gmempty'
  gmappend' (QF l) (QF r) = QF (gmappend' l r)


instance
  ( GMonoid' (GEx (x :> (v :: k) ': free) bound (Ty v ': ftvars) btvars refined a t)
  ) => GMonoid' (GEx free (V x k K ': bound) ftvars (Ty v ': btvars) refined a t) where
  gmempty' = ExG gmempty'
  gmappend' (ExG l) (ExG r) = ExG (gmappend' l r)

