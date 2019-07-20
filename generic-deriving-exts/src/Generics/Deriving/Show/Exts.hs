{-# OPTIONS_GHC -Wno-orphans #-}
{-# LANGUAGE UndecidableInstances #-}
module Generics.Deriving.Show.Exts
  (
  ) where

import Generics.Deriving.Show

import GHC.Generics.Exts

instance GShow' t => GShow' (GM1 i a t) where
  gshowsPrec' ty n (GM1 t) = gshowsPrec' ty n t
  isNullary (GM1 t) = isNullary t

instance (c => GShow' t) => GShow' (c :=>: t) where
  gshowsPrec' ty n (Ct t) = gshowsPrec' ty n t
  isNullary (Ct t) = isNullary t


instance GShow' (SubstSk free t) => GShow' (QF free t) where
  gshowsPrec' ty n (QF t) = gshowsPrec' ty n t
  isNullary (QF t) = isNullary t

instance GShow' (sf (n :> vn ': free ) t) => GShow' (Let n vn sf free t) where
  gshowsPrec' ty n (Let sf) = gshowsPrec' ty n sf
  isNullary (Let sf) = isNullary sf

instance (forall (a :: kvn). GShow' (sf (n :> a ':free) t)) => GShow' (Ex n kvn sf free t) where
  gshowsPrec' ty n (Ex sf) = gshowsPrec' ty n sf
  isNullary (Ex sf) = isNullary sf

