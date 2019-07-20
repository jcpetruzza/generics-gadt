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


instance GEq' (SubstSk free t) => GEq' (QF free t) where
  geq' (QF l) (QF r) = geq' l r

instance GEq' (sf (n :> vn ': free) t) => GEq' (Let n vn sf free t) where
  geq' (Let l) (Let r) = geq' l r
