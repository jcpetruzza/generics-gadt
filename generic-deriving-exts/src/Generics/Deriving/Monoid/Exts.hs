{-# OPTIONS_GHC -Wno-orphans #-}
{-# LANGUAGE UndecidableInstances #-}
module Generics.Deriving.Monoid.Exts
  (
  ) where

import Generics.Deriving.Monoid

import GHC.Generics
import GHC.Generics.Exts
import GHC.Generics.Pruning


instance
   ( c
   , GMonoid' t
   )
  => GMonoid' (c :=>: t)
  where
    gmempty' = Ct gmempty'
    gmappend' (Ct l) (Ct r) = Ct (gmappend' l r)


instance
   ( GMonoid' (Subst free t)
   )
  => GMonoid' (QF free t)
  where
    gmempty' = QF gmempty'
    gmappend' (QF l) (QF r) = QF (gmappend' l r)


instance
   ( GMonoid' (sf ('Assgn a free) t)
   )
  => GMonoid' (Let a sf free t)
  where
    gmempty' = Let gmempty'
    gmappend' (Let l) (Let r) = Let (gmappend' l r)


instance
   ( ma ~ DoMatch km pat a
   , GMonoid' (Let (ma :: km) sf free t)
   )
  => GMonoid' (Match km pat a sf free t)
  where
    gmempty' = Match gmempty'
    gmappend' (Match l) (Match r) = Match (gmappend' l r)


instance
   ( Generic a
   , Prunable (Rep a)
   , Extendable (Rep a)
   , GMonoid' (Pruned (Rep a))
   )
  => GMonoid (Pruning a)
  where
      gmempty
        = Pruning $ to $ extend gmempty'

      gmappend (Pruning l) (Pruning r)
        = Pruning $ to $ extend $ gmappend' (prune $ from l) (prune $ from r)
