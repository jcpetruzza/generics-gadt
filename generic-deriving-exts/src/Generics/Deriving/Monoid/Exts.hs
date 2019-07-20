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

instance (GPruning a t, GMonoid' (Pruned a t)) => GMonoid' (GD1 a t) where
  gmempty' = GM1 $ gextend (Proxy :: Proxy a) gmempty'
  gmappend' (GM1 l) (GM1 r) = GM1 $ gextend pa $ gmappend' (gprune pa l) (gprune pa r)
    where pa = Proxy :: Proxy a

instance GMonoid' t => GMonoid' (GC1 a t) where
  gmempty' = GM1 gmempty'
  gmappend' (GM1 l) (GM1 r) = GM1 $ gmappend' l r

instance (c, GMonoid' t) => GMonoid' (c :=>: t) where
  gmempty' = Ct gmempty'
  gmappend' (Ct l) (Ct r) = Ct (gmappend' l r)


instance GMonoid' (SubstSk free t) => GMonoid' (QF free t) where
  gmempty' = QF gmempty'
  gmappend' (QF l) (QF r) = QF (gmappend' l r)

instance GMonoid' (sf (n :> vn ': free) t) => GMonoid' (Let n vn sf free t) where
  gmempty' = Let gmempty'
  gmappend' (Let l) (Let r) = Let (gmappend' l r)
