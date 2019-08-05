{-# OPTIONS_GHC -Wno-orphans #-}
{-# LANGUAGE UndecidableInstances #-}
module Generics.Deriving.Eq.Exts
  (
  ) where

import Generics.Deriving.Eq

import GHC.Generics.Exts

instance
   ( c => GEq' t
   )
  => GEq' (c :=>: t)
  where
    geq' (Ct l) (Ct r) = geq' l r


instance
   ( GEq' (Subst free t)
   )
  => GEq' (QF free t)
  where
    geq' (QF l) (QF r) = geq' l r


instance
   ( GEq' (sf ('Assgn a free) t)
   )
  => GEq' (Let a sf free t)
  where
    geq' (Let l) (Let r) = geq' l r


instance
   ( ma ~ DoMatch km pat a
   , GEq' (Let (ma :: km) sf free t)
   )
  => GEq' (Match km pat a sf free t)
  where
    geq' (Match l) (Match r) = geq' l r
