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

instance (GPruning a t, GSemigroup' (Pruned a t)) => GSemigroup' (GD1 a t) where
  gsappend' (GM1 l) (GM1 r) = GM1 $ gextend (Proxy :: Proxy a) $ gsappend' (gprune (Proxy :: Proxy a) l) (gprune (Proxy :: Proxy a) r)

instance GSemigroup' t => GSemigroup' (GC1 a t) where
  gsappend' (GM1 l) (GM1 r) = GM1 $ gsappend' l r


instance (c => GSemigroup' t) => GSemigroup' (c :=>: t) where
  gsappend' (Ct l) (Ct r) = Ct (gsappend' l r)


instance GSemigroup' (SubstSk free t) => GSemigroup' (QF free t) where
  gsappend' (QF l) (QF r) = QF (gsappend' l r)

instance GSemigroup' (sf (n :> vn ': free) t) => GSemigroup' (Let n vn sf free t) where
  gsappend' (Let l) (Let r) = Let (gsappend' l r)

