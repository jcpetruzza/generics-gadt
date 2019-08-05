{-# OPTIONS_GHC -Wno-orphans #-}
{-# LANGUAGE UndecidableInstances #-}
module Generics.Deriving.Show.Exts
  (
  ) where

import Generics.Deriving.Show

import GHC.Generics.Exts


instance
   ( c => GShow' t
   )
  => GShow' (c :=>: t)
  where
    gshowsPrec' ty n (Ct t) = gshowsPrec' ty n t
    isNullary (Ct t) = isNullary t


instance
   ( GShow' (Subst free t)
   )
  => GShow' (QF free t)
  where
    gshowsPrec' ty n (QF t) = gshowsPrec' ty n t
    isNullary (QF t) = isNullary t

instance
   ( (GShow' (sf ('Assgn a free) t))
   )
  => GShow' (Let a sf free t)
  where
    gshowsPrec' ty n (Let sf) = gshowsPrec' ty n sf
    isNullary (Let sf) = isNullary sf

instance
   ( (forall (a :: k). GShow' (Let (a :: k) sf free t))
   )
  => GShow' (Ex k sf free t)
  where
    gshowsPrec' ty n (Ex sf) = gshowsPrec' ty n sf
    isNullary (Ex sf) = isNullary sf

instance
   ( ma ~ DoMatch km pat a
   , GShow' (Let (ma :: km) sf free t)
   )
  => GShow' (Match km pat a sf free t)
  where
    gshowsPrec' ty n (Match sf) = gshowsPrec' ty n sf
    isNullary (Match sf) = isNullary sf
