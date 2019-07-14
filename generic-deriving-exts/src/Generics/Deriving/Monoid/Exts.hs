{-# OPTIONS_GHC -Wno-orphans #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE UndecidableInstances #-}
module Generics.Deriving.Monoid.Exts
  (
  ) where

import Data.Proxy

import Generics.Deriving.Monoid

import GHC.Generics.Exts
import GHC.Generics.Pruning

instance (GPruning a t, GMonoid' (Pruned a t)) => GMonoid' (GADT a t) where
  gmempty' = GADT $ gextend (Proxy :: Proxy a) gmempty'
  gmappend' (GADT l) (GADT r) = GADT $ gextend pa $ gmappend' (gprune pa l) (gprune pa r)
    where pa = Proxy :: Proxy a

instance (c, c => GMonoid' t) => GMonoid' (c :=>: t) where
  gmempty' = Ct gmempty'
  gmappend' (Ct l) (Ct r) = Ct (gmappend' l r)


instance (GMonoid' (SubstSk free t)) => GMonoid' (GEx free '[] ftvars '[] a t) where
  gmempty' = QF gmempty'
  gmappend' (QF l) (QF r) = QF (gmappend' l r)


instance
  ( GMonoid' (GEx (x :> (v :: k) ': free) bound (Ty v ': ftvars) btvars a t)
  ) => GMonoid' (GEx free (V x k K ': bound) ftvars (Ty v ': btvars) a t) where
  gmempty' = ExG gmempty'
  gmappend' (ExG l) (ExG r) = ExG (gmappend' l r)

