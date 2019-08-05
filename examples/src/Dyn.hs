{-# LANGUAGE Rank2Types #-}
{-# LANGUAGE UndecidableInstances #-}
module Dyn
  ( Dyn(..)
  , cmap
  ) where

import Data.Kind ( Type )
import Data.Constraint ( (:-)(Sub), Dict(..) )

import GHC.Generics
import GHC.Generics.Exts

import Generics.Deriving.Exts ()
import Generics.Deriving.Show ( GShow(..) )


data Dyn c where
  Dyn :: c a => a -> Dyn c

cmap :: (forall a. c a :- d a) -> Dyn c -> Dyn d
cmap proof (Dyn x) = mkDyn proof x
  where
    mkDyn :: c a => (c a :- d a) -> a -> Dyn d
    mkDyn (Sub Dict) a = Dyn a

instance GShow (Dyn GShow)

instance Generic (Dyn c) where
  type Rep (Dyn c)
    = D1 ('MetaData "Dyn" "Main" "package-name" 'False)
       (C1 ('MetaCons "Dyn" 'PrefixI 'False)
         (S1 ('MetaSel 'Nothing 'NoSourceUnpackedness 'NoSourceStrictness 'DecidedLazy)
           (Let c (Ex Type QF) 'Grnd
              ((Var 1) (Var 0 :: Type) :=>: (K1 R (Var 0)))
           )
         )
       )

  from (Dyn a)
    =  M1 $ M1 $ M1 $ Let $ Ex $ Let $ QF $ Ct $ K1 a

  to (M1 (M1 (M1 (Let (Ex (Let (QF (Ct (K1 a)))))))))
    = Dyn a
