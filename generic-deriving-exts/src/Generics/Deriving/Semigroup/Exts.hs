{-# OPTIONS_GHC -Wno-orphans #-}
{-# LANGUAGE UndecidableInstances #-}
module Generics.Deriving.Semigroup.Exts
  (
  ) where

import Generics.Deriving.Semigroup

import GHC.Generics
import GHC.Generics.Exts
import GHC.Generics.Pruning


instance
   ( c => GSemigroup' t
   )
  => GSemigroup' (c :=>: t)
  where
    gsappend' (Ct l) (Ct r) = Ct (gsappend' l r)


instance
   ( GSemigroup' (Subst free t)
   )
  => GSemigroup' (QF free t)
  where
    gsappend' (QF l) (QF r) = QF (gsappend' l r)

instance
   ( GSemigroup' (sf ('Assgn a free) t)
   )
  => GSemigroup' (Let a sf free t)
  where
    gsappend' (Let l) (Let r) = Let (gsappend' l r)

instance
   ( ma ~ DoMatch km pat a
   , GSemigroup' (Let (ma :: km) sf free t)
   )
  => GSemigroup' (Match km pat a sf free t)
  where
    gsappend' (Match l) (Match r) = Match (gsappend' l r)


instance
   ( Generic a
   , Prunable (Rep a)
   , Extendable (Rep a)
   , GSemigroup' (Pruned (Rep a))
   )
  => GSemigroup (Pruning a)
  where
    gsappend (Pruning l) (Pruning r)
      = Pruning $ to $ extend $ gsappend' (prune $ from l) (prune $ from r)
